# -*- coding: utf-8 -*-
from __future__ import annotations 

import base64 
import json 
import os 
import shutil 
import sys 
import threading 
import time 
from dataclasses import dataclass 
from datetime import datetime 
from queue import Queue ,Empty 
from typing import Dict ,List ,Optional ,Tuple 


import requests 
from bs4 import BeautifulSoup 

import tkinter as tk 
from tkinter import ttk ,messagebox ,simpledialog 
from tkinter .scrolledtext import ScrolledText 

try :
    from plyer import notification 
    PLYER_AVAILABLE =True 
except Exception :
    PLYER_AVAILABLE =False 


    
APP_TITLE ="ZJUのInnerCruly小工具(made by Colamentos's GPT5.2)"
APP_ID ="InnerCrulyTool"

def get_user_data_root (app_id :str )->str :
    
    # Windows
    if os .name =="nt":
        base =os .environ .get ("APPDATA")or os .path .expanduser ("~")
        return os .path .join (base ,app_id )

        # Linux/Unix
    xdg =os .environ .get ("XDG_DATA_HOME")
    if xdg :
        return os .path .join (xdg ,app_id )
    return os .path .join (os .path .expanduser ("~"),".local","share",app_id )

def migrate_portable_data_if_needed (new_root :str ,portable_dir :str )->None :
    
    try :
        old_root =os .path .abspath (portable_dir )
        if not os .path .isdir (old_root ):
            return 
        new_data_dir =os .path .join (new_root ,"data")
        old_cfg =os .path .join (old_root ,"config.json")
        new_cfg =os .path .join (new_data_dir ,"config.json")
        if not os .path .exists (old_cfg ):
            return 
        if os .path .exists (new_cfg ):
            return 

        os .makedirs (new_data_dir ,exist_ok =True )

        
        try :
            shutil .copy2 (old_cfg ,new_cfg )
        except Exception :
            return 

            
        old_snap =os .path .join (old_root ,"snapshots")
        new_snap =os .path .join (new_data_dir ,"snapshots")
        if os .path .isdir (old_snap )and not os .path .isdir (new_snap ):
            try :
                shutil .copytree (old_snap ,new_snap )
            except Exception :
                pass 

                
        try :
            shutil .rmtree (old_root )
        except Exception :
            pass 
    except Exception :
        return 

DATA_ROOT =get_user_data_root (APP_ID )
migrate_portable_data_if_needed (DATA_ROOT ,"data")

OUTPUT_DIR =os .path .join (DATA_ROOT ,"data")
CONFIG_FILE =os .path .join (OUTPUT_DIR ,"config.json")
SNAPSHOT_DIR =os .path .join (OUTPUT_DIR ,"snapshots")


MAX_RETRIES =3 
TIMEOUT =(5 ,12 )

MAX_SEMESTER_INDEX =12 

TYPE_CORE ="专业核心课程"
TYPE_MAJOR ="主修课程"
TYPE_NONMAJOR ="非主修课程"
TYPE_INVISIBLE ="看不见我喵"
TYPE_ALL ="全部"

BINARY_SCORE_TEXTS ={"合格","不合格"}

RETAKE_BEST ="best"
RETAKE_FIRST ="first"

COLOR_BG ="#F5F7FB"
COLOR_CARD ="#FFFFFF"
COLOR_BORDER ="#E6E8EF"
COLOR_TEXT ="#111827"
COLOR_SUBTEXT ="#6B7280"
COLOR_DANGER ="#EF4444"


COLOR_DELTA_BAD ="#7F1D1D"# deep red
COLOR_DELTA_GOOD ="#065F46"# deep green

ACCENT ="#2563EB"
ACCENT_HOVER ="#1D4ED8"
ACCENT_DISABLED ="#93C5FD"

TYPE_COLOR ={
TYPE_CORE :"#991B1B",
TYPE_MAJOR :"#2563EB",
TYPE_NONMAJOR :"#059669",
TYPE_INVISIBLE :"#6B7280",
}


SEM_COLORS =[
"#3B82F6","#22C55E","#F97316","#A855F7",
"#EF4444","#14B8A6","#EAB308","#0EA5E9",
"#F43F5E","#84CC16","#6366F1","#10B981"
]


def ensure_dir (path :str )->None :
    os .makedirs (path ,exist_ok =True )

def resource_path (rel_path :str )->str :
    
    base =getattr (sys ,"_MEIPASS",os .path .abspath ("."))
    return os .path .join (base ,rel_path )


def set_app_icon (root :tk .Tk )->None :
    
    try :
        if os .name =="nt":
            ico =resource_path (os .path .join ("assets","app.ico"))
            if os .path .exists (ico ):
                root .iconbitmap (ico )

        png =resource_path (os .path .join ("assets","app.png"))
        if os .path .exists (png ):
            img =tk .PhotoImage (file =png )
            root .iconphoto (True ,img )
            
            root ._icon_img =img # type: ignore[attr-defined]
    except Exception :
        pass 

def now_str ()->str :
    return datetime .now ().strftime ("%Y-%m-%d %H:%M:%S")


def safe_float (x ,default =0.0 )->float :
    try :
        return float (x )
    except Exception :
        return default 


def _rsa_encrypt (password_str :str ,e_str :str ,M_str :str )->str :
    
    password_bytes =bytes (password_str ,"ascii")
    password_int =int .from_bytes (password_bytes ,"big")
    e_int =int (e_str ,16 )
    M_int =int (M_str ,16 )
    result_int =pow (password_int ,e_int ,M_int )
    return hex (result_int )[2 :].rjust (128 ,"0")


def map_semester (semester_code :str )->str :
    
    if not semester_code or not isinstance (semester_code ,str )or len (semester_code )<12 :
        return "未知学期"
    try :
        semester_part =semester_code [1 :].split (")")[0 ]
        start_year ,end_year ,term =semester_part .split ("-")
        short_start =str (int (start_year )%100 ).zfill (2 )
        short_end =str (int (end_year )%100 ).zfill (2 )
        return f"{short_start }-{short_end }秋冬"if term =="1"else f"{short_start }-{short_end }春夏"
    except Exception :
        return "未知学期"


def parse_semester_sort_key (sem :str )->Tuple [int ,int ]:
    
    if not sem or sem =="未知学期":
        return (9999 ,9 )
    try :
        yy =int (sem [0 :2 ])
        start_year =2000 +yy 
        term =1 if "秋冬"in sem else 2 
        return (start_year ,term )
    except Exception :
        return (9999 ,9 )


        
GRADE_TO_GPA ={
(95 ,100 ):5.0 ,(92 ,94 ):4.8 ,(89 ,91 ):4.5 ,(86 ,88 ):4.2 ,
(83 ,85 ):3.9 ,(80 ,82 ):3.6 ,(77 ,79 ):3.3 ,(74 ,76 ):3.0 ,
(71 ,73 ):2.7 ,(68 ,70 ):2.4 ,(65 ,67 ):2.1 ,(62 ,64 ):1.8 ,
(60 ,61 ):1.5 ,(0 ,59 ):0.0 
}


def convert_grade (score_text :str )->Tuple [float ,float ]:
    
    grade_map ={
    "优秀":(90.0 ,4.5 ),
    "良好":(80.0 ,3.5 ),
    "中等":(70.0 ,2.5 ),
    "及格":(60.0 ,1.5 ),
    "不及格":(0.0 ,0.0 ),
    }
    if score_text in grade_map :
        return grade_map [score_text ]
    try :
        score =float (score_text )
        for (low ,high ),gpa in GRADE_TO_GPA .items ():
            if low <=score <=high :
                return score ,gpa 
        return score ,0.0 
    except Exception :
        return 0.0 ,0.0 

        
GRADE_TO_GPA_43 ={
(95 ,100 ):4.3 ,
(92 ,94 ):4.2 ,
(89 ,91 ):4.1 ,
(86 ,88 ):4.0 ,
(83 ,85 ):3.9 ,
(80 ,82 ):3.6 ,
(77 ,79 ):3.3 ,
(74 ,76 ):3.0 ,
(71 ,73 ):2.7 ,
(68 ,70 ):2.4 ,
(65 ,67 ):2.1 ,
(62 ,64 ):1.8 ,
(60 ,61 ):1.5 ,
(0 ,59 ):0.0 ,
}


def convert_grade_43 (score_text :str )->Tuple [float ,float ]:
    
    score_text =str (score_text or "").strip ()

    
    if score_text in BINARY_SCORE_TEXTS :
        return 0.0 ,0.0 

        
    grade_map_43 ={
    "优秀":(90.0 ,4.1 ),
    "良好":(80.0 ,3.5 ),
    "中等":(70.0 ,2.5 ),
    "及格":(60.0 ,1.5 ),
    "不及格":(0.0 ,0.0 ),
    }
    if score_text in grade_map_43 :
        return grade_map_43 [score_text ]

        
    try :
        score =float (score_text )
        for (low ,high ),gpa in GRADE_TO_GPA_43 .items ():
            if low <=score <=high :
                return score ,gpa 
        return score ,0.0 
    except Exception :
        return 0.0 ,0.0 


def compute_gpa_43 (courses :List [Course ],weights :WeightsConfig )->float :
    
    stat_courses =select_retake_attempts (courses ,weights .retake_policy )

    total_credits =0.0 
    sum_gpa =0.0 

    for c in stat_courses :
        if is_excluded_from_calc (c ):
            continue 

        _score ,gpa43 =convert_grade_43 (c .score_text )
        credits =float (c .credits )

        sum_gpa +=gpa43 *credits 
        total_credits +=credits 

    if total_credits <=1e-9 :
        return 0.0 
    return round (sum_gpa /total_credits ,4 )

def course_key (name :str ,credits :float ,semester :str ,course_code :str ="")->str :
    ident =(course_code or name ).strip ()
    return f"{ident }|{credits :.2f}|{semester }"


def b64e (s :str )->str :
    return "b64:"+base64 .b64encode (s .encode ("utf-8")).decode ("ascii")


def b64d (s :str )->str :
    if not s .startswith ("b64:"):
        return ""
    try :
        return base64 .b64decode (s [4 :].encode ("ascii")).decode ("utf-8")
    except Exception :
        return ""

def _cn_initial (ch :str )->str :
    
    if not ch :
        return ""
    o =ord (ch )
    if (48 <=o <=57 )or (65 <=o <=90 )or (97 <=o <=122 ):
        return ch .lower ()

    try :
        gbk =ch .encode ("gbk",errors ="ignore")
        if len (gbk )<2 :
            return ""
        code =gbk [0 ]*256 +gbk [1 ]
    except Exception :
        return ""

    table =[
    (45217 ,45252 ,"a"),(45253 ,45760 ,"b"),(45761 ,46317 ,"c"),
    (46318 ,46825 ,"d"),(46826 ,47009 ,"e"),(47010 ,47296 ,"f"),
    (47297 ,47613 ,"g"),(47614 ,48118 ,"h"),(48119 ,49061 ,"j"),
    (49062 ,49323 ,"k"),(49324 ,49895 ,"l"),(49896 ,50370 ,"m"),
    (50371 ,50613 ,"n"),(50614 ,50621 ,"o"),(50622 ,50905 ,"p"),
    (50906 ,51386 ,"q"),(51387 ,51445 ,"r"),(51446 ,52217 ,"s"),
    (52218 ,52697 ,"t"),(52698 ,52979 ,"w"),(52980 ,53640 ,"x"),
    (53689 ,54480 ,"y"),(54481 ,55289 ,"z"),
    ]
    for lo ,hi ,letter in table :
        if lo <=code <=hi :
            return letter 
    return ""

def pinyin_initials (text :str )->str :
    if not text :
        return ""
    res =[]
    for ch in text .strip ():
        ini =_cn_initial (ch )
        if ini :
            res .append (ini )
    return "".join (res )



    
@dataclass 
class Course :
    name :str 
    credits :float 
    score_text :str 
    semester :str 
    semester_index :int # 1..12
    course_type :str 
    source_major_flag :bool 
    course_code :str =""


@dataclass 
class WeightsConfig :
    nonmajor_weight :float =0.3 # 0..1
    core_multiplier :float =1.2 # 1..2
    core_mode :str ="gpa"
    retake_policy :str =RETAKE_BEST # best / first

    
class ConfigStore :
    def __init__ (self ,path :str ):
        self .path =path 
        self .data ={
        "course_overrides":{},
        "course_overrides_by_user":{},# username -> { key -> {"type": "..."} }
        "weights":{
        "nonmajor_weight":0.3 ,
        "core_multiplier":1.2 ,
        "core_mode":"gpa",
        "retake_policy":RETAKE_BEST ,
        },
        "saved_login":{
        "enabled":False ,
        "username":"",
        "password":""
        },
        "weights_by_user":{},

        
        # sim_by_user[username] = {
        #   "enabled": bool,
        #   "active_id": str,
        #   "profiles": { id: { "name": str, "courses": [...], "weights": {...} } }
        # }
        "sim_by_user":{},

        
        # targets_by_user[username] = {
        #   "avg_gpa_target": str, "w_gpa_target": str, "gpa43_target": str,
        #   "expected_credits": str,
        #   "last_hint_sig": str
        # }
        "targets_by_user":{},
        }
        self .load ()


    def load (self )->None :
        ensure_dir (os .path .dirname (self .path ))
        if not os .path .exists (self .path ):
            self .save ()
            return 
        try :
            with open (self .path ,"r",encoding ="utf-8")as f :
                obj =json .load (f )
            if isinstance (obj ,dict ):
                self .data .update (obj )
        except Exception :
            self .save ()

    def save (self )->None :
        ensure_dir (os .path .dirname (self .path ))
        with open (self .path ,"w",encoding ="utf-8")as f :
            json .dump (self .data ,f ,ensure_ascii =False ,indent =2 )

            # ---- overrides ----
    def get_override_type (self ,key :str ,username :Optional [str ]=None )->Optional [str ]:
        
        if username :
            cobu =self .data .get ("course_overrides_by_user",{})
            if isinstance (cobu ,dict ):
                uco =cobu .get (username )
                if isinstance (uco ,dict ):
                    v =uco .get (key )
                    if isinstance (v ,dict ):
                        t =v .get ("type")
                        if t in (TYPE_CORE ,TYPE_MAJOR ,TYPE_NONMAJOR ,TYPE_INVISIBLE ):
                            return t 

        co =self .data .get ("course_overrides",{})
        v =co .get (key )
        if isinstance (v ,dict ):
            t =v .get ("type")
            if t in (TYPE_CORE ,TYPE_MAJOR ,TYPE_NONMAJOR ,TYPE_INVISIBLE ):
                return t 
        return None 

    def set_override_type (self ,key :str ,t :str ,username :Optional [str ]=None )->None :
        if t not in (TYPE_CORE ,TYPE_MAJOR ,TYPE_NONMAJOR ,TYPE_INVISIBLE ):
            return 

        if username :
            cobu =self .data .setdefault ("course_overrides_by_user",{})
            if isinstance (cobu ,dict ):
                uco =cobu .setdefault (username ,{})
                if isinstance (uco ,dict ):
                    uco [key ]={"type":t }
                    self .save ()
                    return 

        co =self .data .setdefault ("course_overrides",{})
        co [key ]={"type":t }
        self .save ()

    def clear_overrides (self ,username :Optional [str ]=None )->None :
        if username :
            cobu =self .data .get ("course_overrides_by_user",{})
            if isinstance (cobu ,dict )and username in cobu :
                try :
                    del cobu [username ]
                except Exception :
                    cobu [username ]={}
            self .save ()
            return 

        self .data ["course_overrides"]={}
        self .save ()

        # ---- weights ----
    def get_weights (self ,username :Optional [str ]=None )->WeightsConfig :
        w =None 
        if username :
            wbu =self .data .get ("weights_by_user",{})
            if isinstance (wbu ,dict ):
                cand =wbu .get (username )
                if isinstance (cand ,dict ):
                    w =cand 

        if not isinstance (w ,dict ):
            w =self .data .get ("weights",{})

        rp =w .get ("retake_policy",RETAKE_BEST )
        if rp not in (RETAKE_BEST ,RETAKE_FIRST ):
            rp =RETAKE_BEST 

        return WeightsConfig (
        nonmajor_weight =safe_float (w .get ("nonmajor_weight",0.3 ),0.3 ),
        core_multiplier =safe_float (w .get ("core_multiplier",1.2 ),1.2 ),
        core_mode =w .get ("core_mode","gpa")if w .get ("core_mode","gpa")in ("gpa","credits")else "gpa",
        retake_policy =rp 
        )

    def set_weights (self ,wc :WeightsConfig ,username :Optional [str ]=None )->None :
        payload ={
        "nonmajor_weight":float (wc .nonmajor_weight ),
        "core_multiplier":float (wc .core_multiplier ),
        "core_mode":wc .core_mode ,
        "retake_policy":wc .retake_policy 
        }

        if username :
            wbu =self .data .setdefault ("weights_by_user",{})
            if isinstance (wbu ,dict ):
                wbu [username ]=payload 
        else :
            self .data ["weights"]=payload 

        self .save ()

        # ---- saved login ----
    def get_saved_login (self )->Tuple [bool ,str ,str ]:
        sl =self .data .get ("saved_login",{})
        enabled =bool (sl .get ("enabled",False ))
        username =str (sl .get ("username","")or "")
        password =b64d (str (sl .get ("password","")or ""))
        return enabled ,username ,password 

    def set_saved_login (self ,enabled :bool ,username :str ,password :str )->None :
        self .data ["saved_login"]={
        "enabled":bool (enabled ),
        "username":username if enabled else "",
        "password":b64e (password )if enabled else ""
        }
        self .save ()

    def clear_saved_login (self )->None :
        self .set_saved_login (False ,"","")

        
def fetch_data (username :str ,password :str )->Tuple [List [dict ],bool ,str ,Dict [str ,object ]]:
    start_ts =time .perf_counter ()
    error_type :Optional [str ]=None 

    def _meta ()->Dict [str ,object ]:
        return {
        "elapsed":round (float (time .perf_counter ()-start_ts ),4 ),
        "error_type":error_type 
        }

    headers ={
    "User-Agent":"Mozilla/5.0",
    "Accept":"text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language":"zh-CN,zh;q=0.9,en;q=0.8",
    "Connection":"keep-alive",
    }
    data_headers ={
    "User-Agent":"Mozilla/5.0",
    "Accept":"application/json, text/javascript, */*; q=0.01",
    "Host":"zdbk.zju.edu.cn",
    "Origin":"https://zdbk.zju.edu.cn",
    "X-Requested-With":"XMLHttpRequest",
    "Connection":"keep-alive",
    }

    session =requests .session ()
    session .headers .update (headers )

    log_url ="https://zjuam.zju.edu.cn/cas/login?service=https%3A%2F%2Fzdbk.zju.edu.cn%2Fjwglxt%2Fxtgl%2Flogin_ssologin.html"
    user_data ={"username":username ,"password":password ,"execution":None ,"_eventId":"submit"}

    execution_value =None 
    for attempt in range (MAX_RETRIES ):
        try :
            res =session .get (log_url ,timeout =TIMEOUT )
            res .raise_for_status ()
            soup =BeautifulSoup (res .text ,"html.parser")
            input_tag =soup .find ("input",{"name":"execution"})
            if not input_tag :
                error_type ="api"
                return [],False ,"接口变更：无法获取登录参数 execution",_meta ()
            execution_value =input_tag .get ("value")
            if not execution_value :
                error_type ="api"
                return [],False ,"接口变更：登录参数 execution 为空",_meta ()
            break 
        except requests .exceptions .Timeout :
            error_type ="timeout"
            if attempt ==MAX_RETRIES -1 :
                return [],False ,"网络超时：访问登录页超时",_meta ()
            time .sleep (1 )
        except requests .exceptions .RequestException as e :
            if attempt ==MAX_RETRIES -1 :
                return [],False ,f"访问登录页失败：{e }",_meta ()
            time .sleep (1 )

    user_data ["execution"]=execution_value 

    try :
        pub =session .get ("https://zjuam.zju.edu.cn/cas/v2/getPubKey",timeout =TIMEOUT ).json ()
        n ,e =pub ["modulus"],pub ["exponent"]
        user_data ["password"]=_rsa_encrypt (password ,e ,n )
    except requests .exceptions .Timeout :
        error_type ="timeout"
        return [],False ,"网络超时：获取公钥超时",_meta ()
    except Exception as e :
        error_type ="api"
        return [],False ,f"接口变更：获取/加密公钥失败：{e }",_meta ()

    try :
        login_response =session .post (log_url ,data =user_data ,allow_redirects =False ,timeout =TIMEOUT )

        
        if login_response .status_code ==200 :
            txt =login_response .text or ""
            if ("用户名或密码"in txt )or ("密码错误"in txt )or ("登录失败"in txt ):
                error_type ="auth"
                return [],False ,"认证失败：用户名或密码错误",_meta ()

        if login_response .status_code not in (200 ,301 ,302 ):
            error_type ="api"
            return [],False ,f"登录请求失败，HTTP {login_response .status_code }",_meta ()

        current_url =login_response .headers .get ("location")
        if current_url and current_url .startswith ("http://"):
            current_url =current_url .replace ("http://","https://")

        max_redirects =10 
        redirect_count =0 
        while current_url and redirect_count <max_redirects :
            try :
                redirect_response =session .get (current_url ,allow_redirects =False ,timeout =TIMEOUT )
                redirect_response .raise_for_status ()
                if "filtererr.jsp"in current_url :
                    error_type ="auth"
                    return [],False ,"认证失败：登录被拦截（filtererr.jsp）",_meta ()
                current_url =redirect_response .headers .get ("location")
                if current_url and current_url .startswith ("http://"):
                    current_url =current_url .replace ("http://","https://")
                redirect_count +=1 
            except requests .exceptions .Timeout :
                error_type ="timeout"
                return [],False ,"网络超时：登录重定向超时",_meta ()
            except requests .exceptions .RequestException as e :
                return [],False ,f"重定向失败：{e }",_meta ()
    except requests .exceptions .Timeout :
        error_type ="timeout"
        return [],False ,"网络超时：登录请求超时",_meta ()
    except Exception as e :
        return [],False ,f"登录过程异常：{e }",_meta ()

    score_url ="https://zdbk.zju.edu.cn/jwglxt/cxdy/xscjcx_cxXscjIndex.html?doType=query&queryModel.showCount=2000"
    stats_url ="https://zdbk.zju.edu.cn/jwglxt/zycjtj/xszgkc_cxXsZgkcIndex.html?doType=query&queryModel.showCount=2000"

    score_data =[]
    for attempt in range (MAX_RETRIES ):
        try :
            response =session .get (score_url ,headers =data_headers ,timeout =TIMEOUT )
            if response .status_code !=200 :
                error_type ="api"
                return [],False ,f"接口变更：成绩接口返回 HTTP {response .status_code }",_meta ()
            try :
                data =response .json ()
            except Exception as e :
                error_type ="api"
                return [],False ,f"接口变更：成绩接口 JSON 解析失败：{e }",_meta ()
            score_data =data .get ("items",[])or []
            if not isinstance (score_data ,list ):
                error_type ="api"
                return [],False ,"接口变更：成绩接口 items 字段异常",_meta ()
            break 
        except requests .exceptions .Timeout :
            error_type ="timeout"
            if attempt ==MAX_RETRIES -1 :
                return [],False ,"网络超时：读取成绩接口超时",_meta ()
            time .sleep (1 )
        except Exception as e :
            if attempt ==MAX_RETRIES -1 :
                return [],False ,f"读取成绩接口失败：{e }",_meta ()
            time .sleep (1 )

    stats_data =[]
    for attempt in range (MAX_RETRIES ):
        try :
            response =session .get (stats_url ,headers =data_headers ,timeout =TIMEOUT )
            if response .status_code !=200 :
                stats_data =[]
                break 
            try :
                data =response .json ()
            except Exception :
                stats_data =[]
                break 
            items =data .get ("items",[])or []
            if isinstance (items ,list ):
                stats_data =[item for item in items if item .get ("xdbjmc")!="未修"]
            else :
                stats_data =[]
            break 
        except requests .exceptions .Timeout :
            if attempt ==MAX_RETRIES -1 :
                stats_data =[]
                break 
            time .sleep (1 )
        except Exception :
            if attempt ==MAX_RETRIES -1 :
                stats_data =[]
                break 
            time .sleep (1 )

    raw_courses :List [dict ]=[]
    existing_primary =set ()# (ident, credits_2, semester)
    existing_by_name =set ()

    def _extract_course_code (item :dict )->str :
    
        if not isinstance (item ,dict ):
            return ""

        for k in ("kch","kcdm","kcbh","courseCode","course_code"):
            v =(item .get (k )or "").strip ()
            if v :
                return v 

                
                
        xkkh =(item .get ("xkkh")or "").strip ()
        if xkkh .startswith ("(")and ")-"in xkkh :
            try :
                tail =xkkh .split (")-",1 )[1 ]
                parts =tail .split ("-")
                if len (parts )>=1 :
                    code =(parts [0 ]or "").strip ()
                    if code :
                        return code 
            except Exception :
                pass 

        return ""


    def _extract_semester (item :dict )->str :
        
        if not isinstance (item ,dict ):
            return "未知学期"

        for k in ("xkkh","xnxq01id","xnxq"):
            raw =(item .get (k )or "").strip ()
            if raw :
                sem =map_semester (raw )
                if sem !="未知学期":
                    return sem 

        xnm =str (item .get ("xnm")or "").strip ()
        xqm =str (item .get ("xqm")or item .get ("xq")or "").strip ()
        if xnm .isdigit ()and xqm in ("1","2"):
            try :
                end_year =int (xnm )+1 
                sem =map_semester (f"({xnm }-{end_year }-{xqm })")
                return sem 
            except Exception :
                pass 

        return "未知学期"

    for item in stats_data :
        course_name =(item .get ("kcmc")or "").strip ()
        cj =(item .get ("cj")or "").strip ()
        if course_name and cj :
            semester =_extract_semester (item )
            credits =safe_float (item .get ("xf",0.0 ),0.0 )
            credits2 =float (f"{credits :.2f}")
            code =_extract_course_code (item )

            k_primary =((code or course_name ),credits2 ,semester )
            k_name =(course_name ,credits2 ,semester )

            existing_primary .add (k_primary )
            existing_by_name .add (k_name )

            raw_courses .append ({
            "name":course_name ,
            "course_code":code ,
            "credits":credits ,
            "score":cj ,
            "semester":semester ,
            "is_major":True 
            })

    for item in score_data :
        course_name =(item .get ("kcmc")or "").strip ()
        cj =(item .get ("cj")or "").strip ()
        if not course_name or not cj :
            continue 

        semester =_extract_semester (item )
        credits =safe_float (item .get ("xf",0.0 ),0.0 )
        credits2 =float (f"{credits :.2f}")
        code =_extract_course_code (item )

        k_primary =((code or course_name ),credits2 ,semester )
        k_name =(course_name ,credits2 ,semester )

        
        if (k_primary in existing_primary )or (k_name in existing_by_name ):
            continue 

        raw_courses .append ({
        "name":course_name ,
        "course_code":code ,
        "credits":credits ,
        "score":cj ,
        "semester":semester ,
        "is_major":False 
        })

        
        existing_primary .add (k_primary )
        existing_by_name .add (k_name )

    return raw_courses ,True ,f"获取成功：{len (raw_courses )} 门课程",_meta ()

    
def is_binary_score (score_text :str )->bool :
    return str (score_text or "").strip ()in BINARY_SCORE_TEXTS 


def is_excluded_from_calc (c :Course )->bool :


    return is_binary_score (c .score_text )or (c .course_type ==TYPE_INVISIBLE )


def credits_sum (courses :List [Course ])->float :
    return round (sum (float (c .credits )for c in courses ),4 )

def credits_sum_unique (courses :List [Course ],wc :WeightsConfig )->float :
    
    stat_courses =select_retake_attempts (courses ,wc .retake_policy )
    return round (sum (float (c .credits )for c in stat_courses ),4 )

def select_retake_attempts (courses :List [Course ],retake_policy :str )->List [Course ]:
    
    if retake_policy not in (RETAKE_BEST ,RETAKE_FIRST ):
        retake_policy =RETAKE_BEST 

    by_ident :Dict [str ,List [Course ]]={}
    for c in courses :
        ident =(c .course_code or c .name ).strip ()
        by_ident .setdefault (ident ,[]).append (c )

    chosen :List [Course ]=[]
    for _ident ,lst in by_ident .items ():
        if len (lst )==1 :
            chosen .append (lst [0 ])
            continue 

        if retake_policy ==RETAKE_FIRST :
            lst_sorted =sorted (lst ,key =lambda x :(x .semester_index if x .semester_index >0 else 9999 ))
            chosen .append (lst_sorted [0 ])
        else :
            def score_key (x :Course ):
                s ,g =convert_grade (x .score_text )
                return (g ,s ,-(x .semester_index if x .semester_index >0 else 0 ))
            chosen .append (max (lst ,key =score_key ))

    chosen .sort (key =lambda c :(c .semester_index ,c .name ))
    return chosen 



def compute_metrics (
courses :List [Course ],
weights :WeightsConfig ,
weighted :bool 
)->Tuple [float ,float ]:
    
    stat_courses =select_retake_attempts (courses ,weights .retake_policy )

    total_w =0.0 
    sum_score =0.0 
    sum_gpa =0.0 

    for c in stat_courses :
        if is_excluded_from_calc (c ):
            continue 

        score ,gpa =convert_grade (c .score_text )
        credits =float (c .credits )

        if not weighted :
            w =credits 
            sum_score +=score *w 
            sum_gpa +=gpa *w 
            total_w +=w 
            continue 

            
        nonmajor_x =float (weights .nonmajor_weight )if c .course_type ==TYPE_NONMAJOR else 1.0 

        
        if c .course_type ==TYPE_CORE :
            if weights .core_mode =="gpa":
            
                score =score *float (weights .core_multiplier )
                gpa =gpa *float (weights .core_multiplier )
                w =credits *nonmajor_x 
            else :
            
                w =credits *nonmajor_x *float (weights .core_multiplier )
        else :
        
            w =credits *nonmajor_x 

        sum_score +=score *w 
        sum_gpa +=gpa *w 
        total_w +=w 

    if total_w <=1e-9 :
        return 0.0 ,0.0 
    return (round (sum_score /total_w ,4 ),round (sum_gpa /total_w ,4 ))


def group_by_academic_year (courses :List [Course ])->Dict [int ,List [Course ]]:
    groups :Dict [int ,List [Course ]]={}
    for c in courses :
        idx =c .semester_index 
        if idx <=0 :
            continue 
        year =(idx +1 )//2 
        groups .setdefault (year ,[]).append (c )
    return groups 


def group_by_semester (courses :List [Course ])->Dict [int ,List [Course ]]:
    
    groups :Dict [int ,List [Course ]]={}
    for c in courses :
        idx =c .semester_index 
        if idx <=0 :
            continue 
        groups .setdefault (idx ,[]).append (c )
    return groups 


def _stat_courses_for_analysis (courses :List [Course ],wc :WeightsConfig )->List [Course ]:
    stat_courses =select_retake_attempts (courses ,wc .retake_policy )
    return [c for c in stat_courses if not is_excluded_from_calc (c )]

def _score_bins (scores :List [float ])->List [Tuple [str ,int ]]:
    bins =[("0-59",0 ),("60-69",0 ),("70-79",0 ),("80-89",0 ),("90-100",0 )]
    for s in scores :
        if s <60 :
            bins [0 ]=(bins [0 ][0 ],bins [0 ][1 ]+1 )
        elif s <70 :
            bins [1 ]=(bins [1 ][0 ],bins [1 ][1 ]+1 )
        elif s <80 :
            bins [2 ]=(bins [2 ][0 ],bins [2 ][1 ]+1 )
        elif s <90 :
            bins [3 ]=(bins [3 ][0 ],bins [3 ][1 ]+1 )
        else :
            bins [4 ]=(bins [4 ][0 ],bins [4 ][1 ]+1 )
    return bins 

def draw_line_chart (canvas :tk .Canvas ,xs :List [int ],ys :List [float ],*,y_min =None ,y_max =None ,title :str ="")->None :

    sig =("line",tuple (xs or []),tuple ([float (v )for v in (ys or [])]),float (y_min )if y_min is not None else None ,float (y_max )if y_max is not None else None ,str (title or ""))
    if getattr (canvas ,"_last_draw_sig",None )==sig :
        return 
    canvas ._last_draw_sig =sig # type: ignore[attr-defined]

    canvas .delete ("all")
    w =int (canvas .winfo_reqwidth ())
    h =int (canvas .winfo_reqheight ())
    pad =26 

    if title :
        canvas .create_text (8 ,8 ,anchor ="nw",text =title ,fill =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 ,"bold"))

    if not xs or not ys or len (xs )!=len (ys ):
        canvas .create_text (10 ,h //2 ,anchor ="w",text ="暂无数据",fill =COLOR_SUBTEXT )
        return 

    xmin ,xmax =min (xs ),max (xs )
    if xmin ==xmax :
        xmin -=1 
        xmax +=1 

    ymin =min (ys )if y_min is None else float (y_min )
    ymax =max (ys )if y_max is None else float (y_max )
    if abs (ymax -ymin )<1e-9 :
        ymin -=1.0 
        ymax +=1.0 

    def sx (x ):
        return pad +(w -2 *pad )*(float (x -xmin )/float (xmax -xmin ))

    def sy (y ):
        return h -pad -(h -2 *pad )*(float (y -ymin )/float (ymax -ymin ))

        # axes
    canvas .create_line (pad ,pad ,pad ,h -pad ,fill =COLOR_BORDER )
    canvas .create_line (pad ,h -pad ,w -pad ,h -pad ,fill =COLOR_BORDER )

    pts =[]
    for x ,y in zip (xs ,ys ):
        pts .append ((sx (x ),sy (y )))

        # polyline
    for i in range (1 ,len (pts )):
        canvas .create_line (pts [i -1 ][0 ],pts [i -1 ][1 ],pts [i ][0 ],pts [i ][1 ],fill =ACCENT ,width =2 )

        # points + labels
    for i ,(px ,py )in enumerate (pts ):
        canvas .create_oval (px -3 ,py -3 ,px +3 ,py +3 ,fill =ACCENT ,outline =ACCENT )
        if len (xs )<=10 :
            canvas .create_text (px ,h -pad +10 ,anchor ="n",text =str (xs [i ]),fill =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",8 ))


def draw_dual_line_chart (
canvas :tk .Canvas ,
xs :List [int ],
ys_a :List [float ],
ys_b :List [float ],
*,
title :str ="",
label_a :str ="不加权",
label_b :str ="加权",
y_min =None ,
y_max =None 
)->None :
    
    sig =(
    "dual",
    tuple (xs or []),
    tuple ([float (v )for v in (ys_a or [])]),
    tuple ([float (v )for v in (ys_b or [])]),
    float (y_min )if y_min is not None else None ,
    float (y_max )if y_max is not None else None ,
    str (title or ""),str (label_a or ""),str (label_b or "")
    )
    if getattr (canvas ,"_last_draw_sig",None )==sig :
        return 
    canvas ._last_draw_sig =sig # type: ignore[attr-defined]

    canvas .delete ("all")
    w =int (canvas .winfo_reqwidth ())
    h =int (canvas .winfo_reqheight ())
    pad =26 

    if title :
        canvas .create_text (8 ,8 ,anchor ="nw",text =title ,fill =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 ,"bold"))

    if (not xs )or (not ys_a )or (not ys_b )or (len (xs )!=len (ys_a ))or (len (xs )!=len (ys_b )):
        canvas .create_text (10 ,h //2 ,anchor ="w",text ="暂无数据",fill =COLOR_SUBTEXT )
        return 

    xmin ,xmax =min (xs ),max (xs )
    if xmin ==xmax :
        xmin -=1 
        xmax +=1 

    all_y =list (ys_a )+list (ys_b )
    ymin =min (all_y )if y_min is None else float (y_min )
    ymax =max (all_y )if y_max is None else float (y_max )
    if abs (ymax -ymin )<1e-9 :
        ymin -=1.0 
        ymax +=1.0 

    def sx (x ):
        return pad +(w -2 *pad )*(float (x -xmin )/float (xmax -xmin ))

    def sy (y ):
        return h -pad -(h -2 *pad )*(float (y -ymin )/float (ymax -ymin ))

        # axes
    canvas .create_line (pad ,pad ,pad ,h -pad ,fill =COLOR_BORDER )
    canvas .create_line (pad ,h -pad ,w -pad ,h -pad ,fill =COLOR_BORDER )

    pts_a =[(sx (x ),sy (y ))for x ,y in zip (xs ,ys_a )]
    pts_b =[(sx (x ),sy (y ))for x ,y in zip (xs ,ys_b )]

    # polyline A
    for i in range (1 ,len (pts_a )):
        canvas .create_line (pts_a [i -1 ][0 ],pts_a [i -1 ][1 ],pts_a [i ][0 ],pts_a [i ][1 ],fill =ACCENT ,width =2 )
        # polyline B
    for i in range (1 ,len (pts_b )):
        canvas .create_line (pts_b [i -1 ][0 ],pts_b [i -1 ][1 ],pts_b [i ][0 ],pts_b [i ][1 ],fill =COLOR_SUBTEXT ,width =2 )

        
    for i ,(px ,py )in enumerate (pts_a ):
        canvas .create_oval (px -3 ,py -3 ,px +3 ,py +3 ,fill =ACCENT ,outline =ACCENT )
        if len (xs )<=10 :
            canvas .create_text (px ,h -pad +10 ,anchor ="n",text =str (xs [i ]),fill =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",8 ))

    for (px ,py )in pts_b :
        canvas .create_rectangle (px -2 ,py -2 ,px +2 ,py +2 ,fill =COLOR_SUBTEXT ,outline =COLOR_SUBTEXT )

        
    canvas .create_text (w -8 ,14 ,anchor ="ne",text =f"{label_a } / {label_b }",fill =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",8 ))

def draw_bar_chart (canvas :tk .Canvas ,items :List [Tuple [str ,int ]],title :str ="")->None :
    sig =("bar",tuple ([(str (a ),int (b ))for a ,b in (items or [])]),str (title or ""))
    if getattr (canvas ,"_last_draw_sig",None )==sig :
        return 
    canvas ._last_draw_sig =sig # type: ignore[attr-defined]

    canvas .delete ("all")
    w =int (canvas .winfo_reqwidth ())
    h =int (canvas .winfo_reqheight ())
    pad =26 

    if title :
        canvas .create_text (8 ,8 ,anchor ="nw",text =title ,fill =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 ,"bold"))

    if not items :
        canvas .create_text (10 ,h //2 ,anchor ="w",text ="暂无数据",fill =COLOR_SUBTEXT )
        return 

    mx =max ([v for _ ,v in items ]or [1 ])
    bw =max (10 ,int ((w -2 *pad )/max (1 ,len (items ))-10 ))
    x =pad +10 

    for label ,val in items :
        bar_h =0 if mx <=0 else int ((h -2 *pad )*(float (val )/float (mx )))
        y0 =h -pad 
        y1 =y0 -bar_h 
        canvas .create_rectangle (x ,y1 ,x +bw ,y0 ,fill =ACCENT ,outline =ACCENT )
        canvas .create_text (x +bw /2 ,y0 +10 ,anchor ="n",text =label ,fill =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",8 ))
        canvas .create_text (x +bw /2 ,y1 -6 ,anchor ="s",text =str (val ),fill =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",8 ))
        x +=bw +18 

        # UI
class ScrollableFrame (tk .Frame ):
    def __init__ (self ,master ,*,height =200 ,bg =COLOR_BG ,**kwargs ):
        super ().__init__ (master ,bg =bg ,**kwargs )
        self ._bg =bg 

        self .canvas =tk .Canvas (self ,highlightthickness =0 ,bd =0 ,background =bg )
        self .vbar =ttk .Scrollbar (self ,orient ="vertical",command =self .canvas .yview )
        self .canvas .configure (yscrollcommand =self .vbar .set )
        self .canvas .configure (yscrollincrement =18 )

        self .inner =tk .Frame (self .canvas ,bg =bg )
        self .inner_id =self .canvas .create_window ((0 ,0 ),window =self .inner ,anchor ="nw")

        self .canvas .pack (side ="left",fill ="both",expand =True )
        self .vbar .pack (side ="right",fill ="y")
        self .canvas .configure (height =height )

        self .inner .bind ("<Configure>",self ._on_inner_configure )
        self .canvas .bind ("<Configure>",self ._on_canvas_configure )

        
        
        self .bind_all ("<MouseWheel>",self ._on_mousewheel_global ,add ="+")
        self .bind_all ("<Button-4>",self ._on_mousewheel_linux_global ,add ="+")
        self .bind_all ("<Button-5>",self ._on_mousewheel_linux_global ,add ="+")

    def _on_inner_configure (self ,_evt ):
        self .canvas .configure (scrollregion =self .canvas .bbox ("all"))

    def _on_canvas_configure (self ,_evt ):
        self .canvas .itemconfig (self .inner_id ,width =self .canvas .winfo_width ())

    def _pointer_in_self (self ,x_root :int ,y_root :int )->bool :
        
        w =self .winfo_containing (x_root ,y_root )
        while w is not None :
            if w is self .canvas or w is self .inner or w is self .vbar :
                return True 
            w =getattr (w ,"master",None )
        return False 

    def _on_mousewheel_global (self ,evt ):
        if not self ._pointer_in_self (evt .x_root ,evt .y_root ):
            return 
        delta =evt .delta 
        if delta ==0 :
            return 
        step =int (-1 *(delta /120 ))
        self .canvas .yview_scroll (step *2 ,"units")

    def _on_mousewheel_linux_global (self ,evt ):
        if not self ._pointer_in_self (evt .x_root ,evt .y_root ):
            return 
        if evt .num ==4 :
            self .canvas .yview_scroll (-3 ,"units")
        elif evt .num ==5 :
            self .canvas .yview_scroll (3 ,"units")

            
class CourseCard (tk .Frame ):
    def __init__ (
    self ,
    master ,
    course :Course ,
    on_type_change ,
    *,
    is_new :bool =False ,
    on_ack_new =None ,
    sim_enabled :bool =False ,
    base_score_text :str ="",
    on_sim_score_change =None ,
    on_delete_course =None ,
    **kwargs 
    ):
        super ().__init__ (master ,bg =COLOR_CARD ,**kwargs )
        self .course =course 
        self .on_type_change =on_type_change 
        self .is_new =bool (is_new )
        self .on_ack_new =on_ack_new 

        
        self .sim_enabled =bool (sim_enabled )
        self .base_score_text =str (base_score_text or "").strip ()
        self .on_sim_score_change =on_sim_score_change 
        self .on_delete_course =on_delete_course 

        self .configure (highlightthickness =1 ,highlightbackground =COLOR_BORDER ,highlightcolor =COLOR_BORDER )
        self ._build ()

    def _build (self ):
        sem_idx =max (1 ,min (MAX_SEMESTER_INDEX ,int (self .course .semester_index )))
        sem_color =SEM_COLORS [(sem_idx -1 )%len (SEM_COLORS )]

        
        bar =tk .Frame (self ,bg =sem_color ,width =6 ,height =84 )
        bar .grid (row =0 ,column =0 ,rowspan =3 ,sticky ="nsw")
        bar .grid_propagate (False )

        def _flash_bar (times :int =6 ):
            if not self .is_new :
                return 
            if times <=0 :
                try :
                    bar .configure (bg =sem_color )
                except Exception :
                    pass 
                return 
            try :
                cur =bar .cget ("bg")
                bar .configure (bg =("#FDE68A"if cur ==sem_color else sem_color ))
            except Exception :
                return 
            self .after (180 ,lambda :_flash_bar (times -1 ))

        if self .is_new :
            _flash_bar (6 )

            
        badge =tk .Canvas (self ,width =24 ,height =24 ,bg =COLOR_CARD ,highlightthickness =0 ,bd =0 )
        badge .create_oval (2 ,2 ,22 ,22 ,fill =sem_color ,outline =sem_color )
        badge .create_text (12 ,12 ,text =str (sem_idx ),fill ="white",font =("Microsoft YaHei UI",9 ,"bold"))
        badge .grid (row =0 ,column =1 ,rowspan =2 ,padx =(10 ,8 ),pady =(12 ,0 ),sticky ="nw")

        
        name_row =tk .Frame (self ,bg =COLOR_CARD )
        name_row .grid (row =0 ,column =2 ,sticky ="w",pady =(10 ,0 ))

        name =tk .Label (name_row ,text =self .course .name ,bg =COLOR_CARD ,fg =COLOR_TEXT ,
        font =("Microsoft YaHei UI",12 ,"bold"))
        name .pack (side ="left")

        if self .is_new :
            new_tag =tk .Label (
            name_row ,text ="NEW",
            bg ="#FEF3C7",fg ="#92400E",
            font =("Microsoft YaHei UI",9 ,"bold"),
            padx =6 ,pady =1 
            )
            new_tag .pack (side ="left",padx =(8 ,0 ))

            def _ack (_evt =None ):
                if callable (self .on_ack_new ):
                    self .on_ack_new (self .course )

            new_tag .bind ("<Button-1>",_ack )
            name .bind ("<Double-Button-1>",_ack )


            
        if is_excluded_from_calc (self .course ):
            excl =tk .Label (self ,text ="不计入计算",bg =COLOR_CARD ,fg =COLOR_DANGER ,
            font =("Microsoft YaHei UI",9 ,"bold"))
            excl .grid (row =0 ,column =3 ,sticky ="w",padx =(10 ,0 ),pady =(12 ,0 ))

            
        sub =tk .Label (
        self ,
        text =f"{self .course .semester }   ·   学分 {self .course .credits :.1f}",
        bg =COLOR_CARD ,
        fg =COLOR_SUBTEXT ,
        font =("Microsoft YaHei UI",9 )
        )
        sub .grid (row =1 ,column =2 ,sticky ="w",pady =(2 ,0 ))

        
        score_text =str (self .course .score_text or "").strip ()

        
        
        
        if score_text =="合格":
            score =0.0 
            gpa =3.0 
            score_line ="合格"
        elif score_text =="不合格":
            score =0.0 
            gpa =0.0 
            score_line ="不合格"
        else :
            score ,gpa =convert_grade (score_text )
            score_line =f"百分制 {score :.1f}"

        right =tk .Frame (self ,bg =COLOR_CARD )
        right .grid (row =0 ,column =4 ,rowspan =2 ,sticky ="e",padx =(8 ,10 ),pady =(10 ,0 ))

        gpa_big =tk .Label (right ,text =f"{gpa :.1f}",bg =COLOR_CARD ,fg =COLOR_TEXT ,
        font =("Microsoft YaHei UI",18 ,"bold"))
        gpa_big .grid (row =0 ,column =0 ,sticky ="e")

        score_small =tk .Label (right ,text =score_line ,bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,
        font =("Microsoft YaHei UI",10 ,"bold"))
        score_small .grid (row =1 ,column =0 ,sticky ="e",pady =(2 ,0 ))

        
        if self .sim_enabled :
            def _delta_color (d :float )->str :
                if d <-1e-9 :
                    return COLOR_DELTA_BAD 
                if d >1e-9 :
                    return COLOR_DELTA_GOOD 
                return COLOR_SUBTEXT 

            base_txt =self .base_score_text 
            cur_txt =str (self .course .score_text or "").strip ()

            base_score ,_ =convert_grade (base_txt )if base_txt else (0.0 ,0.0 )
            cur_score ,_ =convert_grade (cur_txt )if cur_txt else (0.0 ,0.0 )
            d_score =float (cur_score -base_score )

            sim_row =tk .Frame (right ,bg =COLOR_CARD )
            sim_row .grid (row =2 ,column =0 ,sticky ="e",pady =(8 ,0 ))

            tk .Label (sim_row ,text ="模拟",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).pack (side ="left")

            self ._var_sim =tk .StringVar (value =cur_txt )
            ent_sim =ttk .Entry (sim_row ,textvariable =self ._var_sim ,width =8 )
            ent_sim .pack (side ="left",padx =(6 ,6 ))

            lbl_delta =tk .Label (
            sim_row ,
            text =(f"Δ{d_score :+.1f}"if base_txt else ""),
            bg =COLOR_CARD ,
            fg =_delta_color (d_score ),
            font =("Microsoft YaHei UI",9 ,"bold")
            )
            lbl_delta .pack (side ="left")

            def _apply_sim (_evt =None ):
                if not callable (self .on_sim_score_change ):
                    return 
                v =(self ._var_sim .get ()or "").strip ()
                self .on_sim_score_change (self .course ,v )

            ent_sim .bind ("<Return>",_apply_sim )
            ent_sim .bind ("<FocusOut>",_apply_sim )

            
            if callable (self .on_delete_course ):
                ttk .Button (sim_row ,text ="删除",command =lambda :self .on_delete_course (self .course )).pack (side ="left",padx =(8 ,0 ))

                
        type_var =tk .StringVar (value =self .course .course_type )
        type_box =ttk .Combobox (
        self ,
        textvariable =type_var ,
        values =[TYPE_CORE ,TYPE_MAJOR ,TYPE_NONMAJOR ,TYPE_INVISIBLE ],
        state ="readonly",
        width =10 
        )
        type_box .grid (row =2 ,column =2 ,sticky ="w",pady =(10 ,12 ))

        
        tag_color =TYPE_COLOR .get (self .course .course_type ,COLOR_SUBTEXT )
        tag =tk .Label (self ,text =self .course .course_type ,bg =COLOR_CARD ,fg =tag_color ,
        font =("Microsoft YaHei UI",9 ,"bold"))
        tag .grid (row =2 ,column =4 ,sticky ="e",padx =(8 ,10 ),pady =(10 ,12 ))

        def on_select (_evt =None ):
            new_t =type_var .get ()
            if new_t ==self .course .course_type :
                return 
            self .course .course_type =new_t 
            self .on_type_change (self .course ,new_t )

        type_box .bind ("<<ComboboxSelected>>",on_select )

        self .grid_columnconfigure (2 ,weight =1 )

        
class GradeApp (tk .Tk ):
    def __init__ (self ):
        super ().__init__ ()
        set_app_icon (self )
        self .title (APP_TITLE )
        self .geometry ("1160x740")
        self .minsize (1020 ,660 )
        self .configure (bg =COLOR_BG )

        self .config_store =ConfigStore (CONFIG_FILE )
        self ._apply_theme ()

        
        try :
            self .unbind_class ("TCombobox","<MouseWheel>")
            self .unbind_class ("TCombobox","<Button-4>")
            self .unbind_class ("TCombobox","<Button-5>")
        except Exception :
            pass 

        self .net_q :"Queue[dict]"=Queue ()

        self .username :Optional [str ]=None 
        self .password :Optional [str ]=None 

        self .courses :List [Course ]=[]
        self .course_by_key :Dict [str ,Course ]={}

        self .view_courses :List [Course ]=[]
        self ._view_weights :Optional [WeightsConfig ]=None 
        self ._sim_enabled :bool =False 
        self ._sim_active_id :str =""

        self .polling =False 
        self .poll_interval_sec =30 
        self ._fetch_inflight =False 

        self .new_course_pending_keys :set =set ()
        self .last_success_sync_time :str =""
        self .last_request_elapsed :float =0.0 

        self ._build_login ()
        self .after (120 ,self ._process_net_queue )

        # -------------------------
        
        # -------------------------
    def _get_targets_store (self )->dict :
        allu =self .config_store .data .get ("targets_by_user",{})
        if not isinstance (allu ,dict ):
            allu ={}
            self .config_store .data ["targets_by_user"]=allu 
        u =str (self .username or "")
        st =allu .get (u )
        if not isinstance (st ,dict ):
            st ={
            "avg_gpa_target":"",
            "w_gpa_target":"",
            "gpa43_target":"",
            "expected_credits":"",
            "expected_major_credits":"",
            "last_hint_sig":""
            }
            allu [u ]=st 
            self .config_store .save ()
        return st 

    def _save_targets_store (self ,st :dict )->None :
        allu =self .config_store .data .setdefault ("targets_by_user",{})
        if isinstance (allu ,dict ):
            allu [str (self .username or "")]=st 
        self .config_store .save ()

    def _build_target_controls (self ,parent ):
        st =self ._get_targets_store ()
        body =self ._stat_card (parent ,"目标设定 / 预期投入",header_fg =COLOR_TEXT ,header_font =("Microsoft YaHei UI",11 ,"bold"))

        self .var_t_avg =tk .StringVar (value =str (st .get ("avg_gpa_target","")or ""))
        self .var_t_w =tk .StringVar (value =str (st .get ("w_gpa_target","")or ""))
        self .var_t_43 =tk .StringVar (value =str (st .get ("gpa43_target","")or ""))
        self .var_t_credits =tk .StringVar (value =str (st .get ("expected_credits","")or ""))
        self .var_t_major_credits =tk .StringVar (value =str (st .get ("expected_major_credits","")or ""))

        tk .Label (body ,text ="均绩目标",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (row =0 ,column =0 ,sticky ="w")
        ttk .Entry (body ,textvariable =self .var_t_avg ,width =12 ).grid (row =0 ,column =1 ,sticky ="w",padx =(8 ,0 ))

        tk .Label (body ,text ="加权均绩目标",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (row =1 ,column =0 ,sticky ="w",pady =(10 ,0 ))
        ttk .Entry (body ,textvariable =self .var_t_w ,width =12 ).grid (row =1 ,column =1 ,sticky ="w",padx =(8 ,0 ),pady =(10 ,0 ))

        tk .Label (body ,text ="4.3分制目标",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (row =2 ,column =0 ,sticky ="w",pady =(10 ,0 ))
        ttk .Entry (body ,textvariable =self .var_t_43 ,width =12 ).grid (row =2 ,column =1 ,sticky ="w",padx =(8 ,0 ),pady =(10 ,0 ))

        tk .Label (body ,text ="预期投入学分数",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (row =3 ,column =0 ,sticky ="w",pady =(10 ,0 ))
        ttk .Entry (body ,textvariable =self .var_t_credits ,width =12 ).grid (row =3 ,column =1 ,sticky ="w",padx =(8 ,0 ),pady =(10 ,0 ))

        
        tk .Label (body ,text ="预期其中主修学分",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (row =4 ,column =0 ,sticky ="w",pady =(10 ,0 ))
        ttk .Entry (body ,textvariable =self .var_t_major_credits ,width =12 ).grid (row =4 ,column =1 ,sticky ="w",padx =(8 ,0 ),pady =(10 ,0 ))

        ttk .Button (body ,text ="保存目标",style ="Accent.TButton",command =self ._save_targets_and_maybe_hint ).grid (
        row =5 ,column =0 ,columnspan =3 ,sticky ="we",pady =(12 ,0 )
        )

        
        ttk .Separator (body ,orient ="horizontal").grid (row =6 ,column =0 ,columnspan =3 ,sticky ="we",pady =(12 ,10 ))

        tk .Label (body ,text ="目标进度（按“预期投入学分”估算）",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,
        font =("Microsoft YaHei UI",9 ,"bold")).grid (row =7 ,column =0 ,columnspan =3 ,sticky ="w")

        self .lbl_target_avg =tk .Label (body ,text ="均绩：-",bg =COLOR_CARD ,fg =COLOR_TEXT ,justify ="left",anchor ="w",wraplength =340 )
        self .lbl_target_avg .grid (row =8 ,column =0 ,columnspan =3 ,sticky ="we",pady =(6 ,0 ))

        self .lbl_target_w =tk .Label (body ,text ="加权均绩：-",bg =COLOR_CARD ,fg =COLOR_TEXT ,justify ="left",anchor ="w",wraplength =340 )
        self .lbl_target_w .grid (row =9 ,column =0 ,columnspan =3 ,sticky ="we",pady =(6 ,0 ))

        self .lbl_target_43 =tk .Label (body ,text ="4.3分制：-",bg =COLOR_CARD ,fg =COLOR_TEXT ,justify ="left",anchor ="w",wraplength =340 )
        self .lbl_target_43 .grid (row =10 ,column =0 ,columnspan =3 ,sticky ="we",pady =(6 ,0 ))

        for i in range (3 ):
            body .grid_columnconfigure (i ,weight =1 )


    def _save_targets_and_maybe_hint (self ):
        st =self ._get_targets_store ()

        avg_t =(self .var_t_avg .get ()or "").strip ()
        w_t =(self .var_t_w .get ()or "").strip ()
        g43_t =(self .var_t_43 .get ()or "").strip ()
        cr_t =(self .var_t_credits .get ()or "").strip ()
        mcr_t =(self .var_t_major_credits .get ()or "").strip ()

        def _try_float (s :str )->Optional [float ]:
            try :
                if s =="":
                    return None 
                return float (s )
            except Exception :
                return None 

        E =_try_float (cr_t )
        M =_try_float (mcr_t )

        
        if (E is not None )and (M is not None ):
            if E <0 or M <0 :
                messagebox .showerror ("参数错误","预期学分与主修学分不能为负数。")
                return 
            if M -E >1e-9 :
                messagebox .showerror ("参数错误","“预期其中主修学分”不能大于“预期投入学分数”。")
                return 

        sig =json .dumps ({"a":avg_t ,"w":w_t ,"g43":g43_t ,"cr":cr_t },ensure_ascii =False ,sort_keys =True )

        
        st ["avg_gpa_target"]=avg_t 
        st ["w_gpa_target"]=w_t 
        st ["gpa43_target"]=g43_t 
        st ["expected_credits"]=cr_t 
        st ["expected_major_credits"]=mcr_t 

        
        last_sig =str (st .get ("last_hint_sig","")or "")
        should_hint =(sig !=last_sig )

        
        wc_view =self ._get_view_weights ()
        cur_avg_gpa =compute_metrics (self .view_courses ,wc_view ,weighted =False )[1 ]
        cur_w_gpa =compute_metrics (self .view_courses ,wc_view ,weighted =True )[1 ]
        cur_43 =compute_gpa_43 (self .view_courses ,wc_view )

        def _try_float (s :str )->Optional [float ]:
            try :
                if s =="":
                    return None 
                return float (s )
            except Exception :
                return None 

        msgs :List [str ]=[]

        
        crv =_try_float (cr_t )
        if should_hint and crv is not None :
        
            if abs ((crv *2.0 )-round (crv *2.0 ))>1e-6 :
                msgs .append ("真的有这样学分的课程咩... (´・ω・`)")
            if crv <=0 :
                msgs .append ("好想让时光倒流... (；´д｀)")
            if crv >200 :
                msgs .append ("学分大胃袋？！ (ﾟДﾟ)")

                
        def _check_target (tv :Optional [float ],curv :float ,mx :float ,title :str ):
            if tv is None :
                return 
            if tv <=0 :
                msgs .append (f"{title } 目标 ≤ 0：这是要躺平到量子态吗？(｡•́︿•̀｡)")
                return 
            if tv >mx :
                msgs .append (f"{title } 目标 {tv :.2f} 有点超纲啦～最高也就 {mx :.1f} 哦 (￣▽￣;)")
                return 
            if tv <curv -1e-9 :
                msgs .append (f"{title } 目标 {tv :.2f} 已经被你超过啦！要不要再大胆一点点？(≧▽≦)")

        if should_hint :
            _check_target (_try_float (avg_t ),cur_avg_gpa ,5.0 ,"均绩(5.0制)")
            _check_target (_try_float (w_t ),cur_w_gpa ,5.5 ,"加权均绩(最高5.5)")
            _check_target (_try_float (g43_t ),cur_43 ,4.3 ,"4.3分制")

        if should_hint and msgs :
            messagebox .showinfo ("小提醒 (≧▽≦)","\n".join (msgs ))

            
        st ["last_hint_sig"]=sig 
        self ._save_targets_store (st )

        
        self ._refresh_target_progress_view ()

        self ._log (f"{now_str ()}：已保存目标设定。")


    def _apply_theme (self ):
        style =ttk .Style (self )
        try :
            style .theme_use ("clam")
        except Exception :
            pass 

        self .option_add ("*Font",("Microsoft YaHei UI",10 ))

        style .configure ("TButton",padding =8 )
        style .configure ("TEntry",padding =6 )
        style .configure ("TCombobox",padding =6 )

        
        style .configure ("Accent.TButton",padding =9 ,background =ACCENT ,foreground ="#FFFFFF")
        style .map (
        "Accent.TButton",
        background =[("active",ACCENT_HOVER ),("disabled",ACCENT_DISABLED )],
        foreground =[("disabled","#E5E7EB")]
        )

        
    def _build_login (self ):
        self .login_frame =tk .Frame (self ,bg =COLOR_BG )
        self .login_frame .pack (fill ="both",expand =True )

        card =tk .Frame (self .login_frame ,bg =COLOR_CARD ,highlightthickness =1 ,highlightbackground =COLOR_BORDER )
        card .pack (expand =True )

        inner =tk .Frame (card ,bg =COLOR_CARD )
        inner .pack (padx =28 ,pady =22 )

        title =tk .Label (inner ,text ="登录教务网",bg =COLOR_CARD ,fg =COLOR_TEXT ,
        font =("Microsoft YaHei UI",18 ,"bold"))
        title .grid (row =0 ,column =0 ,columnspan =2 ,sticky ="w",pady =(0 ,14 ))

        tk .Label (inner ,text ="学号",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ).grid (row =1 ,column =0 ,sticky ="w")
        self .var_user =tk .StringVar ()
        ent_user =ttk .Entry (inner ,textvariable =self .var_user ,width =32 )
        ent_user .grid (row =2 ,column =0 ,columnspan =2 ,sticky ="we",pady =(6 ,0 ))

        tk .Label (inner ,text ="密码",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ).grid (row =3 ,column =0 ,sticky ="w",pady =(14 ,0 ))
        self .var_pass =tk .StringVar ()
        self .ent_pass =ttk .Entry (inner ,textvariable =self .var_pass ,width =32 ,show ="*")
        self .ent_pass .grid (row =4 ,column =0 ,columnspan =2 ,sticky ="we",pady =(6 ,0 ))

        self .var_showpass =tk .BooleanVar (value =False )
        chk =tk .Checkbutton (
        inner ,
        text ="密码可见",
        variable =self .var_showpass ,
        command =self ._toggle_password ,
        bg =COLOR_CARD ,
        fg =COLOR_TEXT ,
        activebackground =COLOR_CARD ,
        activeforeground =COLOR_TEXT ,
        selectcolor =COLOR_CARD ,
        relief ="flat",
        highlightthickness =0 
        )
        chk .grid (row =5 ,column =0 ,sticky ="w",pady =(10 ,0 ))

        
        self .var_remember =tk .BooleanVar (value =False )
        chk2 =tk .Checkbutton (
        inner ,
        text ="保存账号和密码（本地）",
        variable =self .var_remember ,
        bg =COLOR_CARD ,
        fg =COLOR_TEXT ,
        activebackground =COLOR_CARD ,
        activeforeground =COLOR_TEXT ,
        selectcolor =COLOR_CARD ,
        relief ="flat",
        highlightthickness =0 
        )
        chk2 .grid (row =5 ,column =1 ,sticky ="e",pady =(10 ,0 ))

        
        enabled ,su ,sp =self .config_store .get_saved_login ()
        if enabled and su :
            self .var_user .set (su )
            self .var_pass .set (sp )
            self .var_remember .set (True )

        btn_row =tk .Frame (inner ,bg =COLOR_CARD )
        btn_row .grid (row =6 ,column =0 ,columnspan =2 ,sticky ="we",pady =(16 ,0 ))
        btn_row .grid_columnconfigure (0 ,weight =1 )
        btn_row .grid_columnconfigure (1 ,weight =1 )

        self .btn_login =ttk .Button (btn_row ,text ="登录",style ="Accent.TButton",command =self ._login_click )
        self .btn_login .grid (row =0 ,column =0 ,sticky ="we")

        self .btn_clear_saved =ttk .Button (btn_row ,text ="清除已保存",command =self ._clear_saved_login )
        self .btn_clear_saved .grid (row =0 ,column =1 ,sticky ="we",padx =(10 ,0 ))

        self .lbl_status =tk .Label (inner ,text ="",bg =COLOR_CARD ,fg =COLOR_DANGER )
        self .lbl_status .grid (row =7 ,column =0 ,columnspan =2 ,sticky ="w",pady =(12 ,0 ))

        hint ="提示：保存仅在本机本地文件中存储（轻度编码，不是强加密）。"
        tk .Label (inner ,text =hint ,bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,
        font =("Microsoft YaHei UI",9 )).grid (row =8 ,column =0 ,columnspan =2 ,sticky ="w",pady =(18 ,0 ))

        inner .grid_columnconfigure (0 ,weight =1 )
        inner .grid_columnconfigure (1 ,weight =1 )

        ent_user .focus_set ()

    def _clear_saved_login (self ):
        self .config_store .clear_saved_login ()
        self .var_remember .set (False )
        self .lbl_status .configure (text ="已清除本地保存的账号密码。",fg =COLOR_SUBTEXT )

    def _toggle_password (self ):
        self .ent_pass .configure (show =""if self .var_showpass .get ()else "*")

    def _login_click (self ):
        username =self .var_user .get ().strip ()
        password =self .var_pass .get ()
        if not username or not password :
            self .lbl_status .configure (text ="请输入学号和密码。",fg =COLOR_DANGER )
            return 

            
        remember =bool (self .var_remember .get ())

        self .btn_login .configure (state ="disabled")
        self .lbl_status .configure (text ="正在登录并拉取成绩…",fg =COLOR_SUBTEXT )

        def worker ():
            raw ,ok ,msg ,meta =fetch_data (username ,password )
            self .net_q .put ({
            "type":"login_result",
            "ok":ok ,
            "msg":msg ,
            "meta":meta ,
            "username":username ,
            "password":password ,
            "remember":remember ,
            "raw":raw 
            })

        threading .Thread (target =worker ,daemon =True ).start ()

        
    def _build_main (self ):
        self .main_frame =tk .Frame (self ,bg =COLOR_BG )
        self .main_frame .pack (fill ="both",expand =True ,padx =12 ,pady =12 )

        
        left_wrap =tk .Frame (self .main_frame ,bg =COLOR_BG ,width =400 )
        left_wrap .pack (side ="left",fill ="y",padx =(0 ,12 ))
        left_wrap .pack_propagate (False )

        left =tk .Frame (left_wrap ,bg =COLOR_BG )
        left .pack (fill ="both",expand =True )

        title =tk .Label (left ,text ="成绩统计",bg =COLOR_BG ,fg =COLOR_TEXT ,font =("Microsoft YaHei UI",11 ,"bold"))
        title .pack (anchor ="w",pady =(0 ,8 ))

        self .stats_scroll =ScrollableFrame (left ,height =680 ,bg =COLOR_BG )
        self .stats_scroll .pack (fill ="both",expand =True )

        
        right =tk .Frame (self .main_frame ,bg =COLOR_BG )
        right .pack (side ="left",fill ="both",expand =True )

        topbar =tk .Frame (right ,bg =COLOR_BG )
        topbar .pack (fill ="x")

        self .btn_sync =ttk .Button (topbar ,text ="同步教务网",style ="Accent.TButton",command =self ._sync_click )
        self .btn_sync .pack (side ="left")

        self .btn_reset_type =ttk .Button (topbar ,text ="重置课程类型",command =self ._reset_type_click )
        self .btn_reset_type .pack (side ="left",padx =(10 ,0 ))

        
        sim_box =tk .Frame (topbar ,bg =COLOR_BG )
        sim_box .pack (side ="left",padx =(16 ,0 ))

        self .var_sim_enabled =tk .BooleanVar (value =False )
        tk .Checkbutton (
        sim_box ,
        text ="启用模拟",
        variable =self .var_sim_enabled ,
        command =self ._toggle_sim_mode ,
        bg =COLOR_BG ,
        fg =COLOR_TEXT ,
        activebackground =COLOR_BG ,
        activeforeground =COLOR_TEXT ,
        selectcolor =COLOR_BG ,
        relief ="flat",
        highlightthickness =0 
        ).pack (side ="left")

        self .var_sim_profile =tk .StringVar (value ="主配置")
        self .cmb_sim_profile =ttk .Combobox (sim_box ,textvariable =self .var_sim_profile ,state ="disabled",width =14 )
        self .cmb_sim_profile .pack (side ="left",padx =(8 ,0 ))
        self .cmb_sim_profile .bind ("<<ComboboxSelected>>",lambda _e =None :self ._switch_sim_profile ())

        self .btn_sim_new =ttk .Button (sim_box ,text ="新建",state ="disabled",command =self ._new_sim_profile )
        self .btn_sim_new .pack (side ="left",padx =(8 ,0 ))

        self .btn_sim_dup =ttk .Button (sim_box ,text ="复制",state ="disabled",command =self ._dup_sim_profile )
        self .btn_sim_dup .pack (side ="left",padx =(6 ,0 ))

        self .btn_sim_del =ttk .Button (sim_box ,text ="删除",state ="disabled",command =self ._del_sim_profile )
        self .btn_sim_del .pack (side ="left",padx =(6 ,0 ))

        self .btn_sim_add_course =ttk .Button (sim_box ,text ="新增课程",state ="disabled",command =self ._add_sim_course )
        self .btn_sim_add_course .pack (side ="left",padx =(10 ,0 ))

        self .lbl_sync_meta =tk .Label (
        topbar ,
        text ="最近成功同步：-｜上次请求耗时：-",
        bg =COLOR_BG ,
        fg =COLOR_SUBTEXT ,
        font =("Microsoft YaHei UI",9 )
        )
        self .lbl_sync_meta .pack (side ="right")

        ttk .Separator (right ,orient ="horizontal").pack (fill ="x",pady =10 )

        
        filterbar =tk .Frame (right ,bg =COLOR_BG )
        filterbar .pack (fill ="x")

        fb_card =tk .Frame (filterbar ,bg =COLOR_CARD ,highlightthickness =1 ,highlightbackground =COLOR_BORDER )
        fb_card .pack (fill ="x")

        inner =tk .Frame (fb_card ,bg =COLOR_CARD )
        inner .pack (fill ="x",padx =12 ,pady =10 )

        tk .Label (inner ,text ="范围",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ).grid (row =0 ,column =0 ,sticky ="w")
        self .var_range =tk .StringVar (value =TYPE_ALL )
        self .cmb_range =ttk .Combobox (inner ,textvariable =self .var_range ,state ="readonly",width =14 )
        self .cmb_range .grid (row =0 ,column =1 ,padx =(8 ,16 ),sticky ="w")

        tk .Label (inner ,text ="类型",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ).grid (row =0 ,column =2 ,sticky ="w")
        self .var_type =tk .StringVar (value =TYPE_ALL )
        self .cmb_type =ttk .Combobox (inner ,textvariable =self .var_type ,state ="readonly",width =14 )
        self .cmb_type .grid (row =0 ,column =3 ,padx =(8 ,16 ),sticky ="w")

        tk .Label (inner ,text ="阈值",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ).grid (row =0 ,column =4 ,sticky ="w")
        self .var_score_op =tk .StringVar (value ="不限")
        self .cmb_score_op =ttk .Combobox (inner ,textvariable =self .var_score_op ,state ="readonly",width =7 ,
        values =["不限","≥","≤"])
        self .cmb_score_op .grid (row =0 ,column =5 ,padx =(8 ,6 ),sticky ="w")

        self .var_score_val =tk .StringVar (value ="")
        self .ent_score_val =ttk .Entry (inner ,textvariable =self .var_score_val ,width =10 )
        self .ent_score_val .grid (row =0 ,column =6 ,sticky ="w")

        self .btn_apply_filter =ttk .Button (inner ,text ="应用",style ="Accent.TButton",command =self ._refresh_cards )
        self .btn_apply_filter .grid (row =0 ,column =7 ,padx =(12 ,0 ),sticky ="e")

        
        tk .Label (inner ,text ="课程搜索",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ).grid (row =1 ,column =0 ,sticky ="w",pady =(10 ,0 ))
        self .var_query =tk .StringVar (value ="")
        ent_q =ttk .Entry (inner ,textvariable =self .var_query ,width =32 )
        ent_q .grid (row =1 ,column =1 ,columnspan =6 ,sticky ="we",padx =(8 ,6 ),pady =(10 ,0 ))

        ttk .Button (inner ,text ="清空",command =lambda :(self .var_query .set (""),self ._refresh_cards ())).grid (
        row =1 ,column =7 ,sticky ="e",padx =(12 ,0 ),pady =(10 ,0 )
        )

        inner .grid_columnconfigure (6 ,weight =1 )
        inner .grid_columnconfigure (7 ,weight =0 )

        def _on_query_enter (_evt =None ):
            self ._refresh_cards ()
        ent_q .bind ("<Return>",_on_query_enter )

        
        cards_frame =tk .Frame (right ,bg =COLOR_BG )
        cards_frame .pack (fill ="both",expand =True ,pady =(10 ,10 ))

        cards_title =tk .Label (cards_frame ,text ="成绩列表",bg =COLOR_BG ,fg =COLOR_TEXT ,
        font =("Microsoft YaHei UI",11 ,"bold"))
        cards_title .pack (anchor ="w",pady =(0 ,8 ))

        cards_card =tk .Frame (cards_frame ,bg =COLOR_BG )
        cards_card .pack (fill ="both",expand =True )

        self .cards_scroll =ScrollableFrame (cards_card ,height =420 ,bg =COLOR_BG )
        self .cards_scroll .pack (fill ="both",expand =True )

        
        query_frame =tk .Frame (right ,bg =COLOR_BG )
        query_frame .pack (fill ="x")

        q_title =tk .Label (query_frame ,text ="自动查询（定时检查新成绩）",bg =COLOR_BG ,fg =COLOR_TEXT ,
        font =("Microsoft YaHei UI",11 ,"bold"))
        q_title .pack (anchor ="w",pady =(0 ,8 ))

        q_card =tk .Frame (query_frame ,bg =COLOR_CARD ,highlightthickness =1 ,highlightbackground =COLOR_BORDER )
        q_card .pack (fill ="x")

        q_inner =tk .Frame (q_card ,bg =COLOR_CARD )
        q_inner .pack (fill ="x",padx =12 ,pady =10 )

        tk .Label (q_inner ,text ="查询频率（秒，≥5）",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ).grid (row =0 ,column =0 ,sticky ="w")
        self .var_interval =tk .StringVar (value ="30")
        ttk .Entry (q_inner ,textvariable =self .var_interval ,width =10 ).grid (row =0 ,column =1 ,padx =(8 ,16 ),sticky ="w")

        self .btn_start =ttk .Button (q_inner ,text ="查查我的",style ="Accent.TButton",command =self ._start_polling )
        self .btn_start .grid (row =0 ,column =2 ,sticky ="w")

        self .btn_stop =ttk .Button (q_inner ,text ="不查了喵",command =self ._stop_polling ,state ="disabled")
        self .btn_stop .grid (row =0 ,column =3 ,padx =(10 ,0 ),sticky ="w")

        tk .Label (q_inner ,text ="日志",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ).grid (row =1 ,column =0 ,sticky ="w",pady =(10 ,0 ))
        self .txt_log =ScrolledText (q_inner ,height =6 ,wrap ="word",font =("Consolas",9 ))
        self .txt_log .grid (row =2 ,column =0 ,columnspan =10 ,sticky ="we",pady =(6 ,0 ))
        q_inner .grid_columnconfigure (9 ,weight =1 )

        
        self ._build_weights_controls (self .stats_scroll .inner )
        self ._build_target_controls (self .stats_scroll .inner )
        self ._refresh_filter_options ()
        self ._render_stats ()
        self ._refresh_cards ()
        self ._log (f"{now_str ()}：进入主界面。")

        # -------------------------
        
        # -------------------------
    def _get_sim_store (self )->dict :
        allu =self .config_store .data .get ("sim_by_user",{})
        if not isinstance (allu ,dict ):
            allu ={}
            self .config_store .data ["sim_by_user"]=allu 
        u =str (self .username or "")
        st =allu .get (u )
        if not isinstance (st ,dict ):
            st ={"enabled":False ,"active_id":"","profiles":{}}
            allu [u ]=st 
            self .config_store .save ()
        if not isinstance (st .get ("profiles"),dict ):
            st ["profiles"]={}
        return st 

    def _save_sim_store (self ,st :dict )->None :
        allu =self .config_store .data .setdefault ("sim_by_user",{})
        if isinstance (allu ,dict ):
            allu [str (self .username or "")]=st 
        self .config_store .save ()

    def _serialize_courses (self ,courses :List [Course ])->List [dict ]:
        payload =[]
        for c in courses :
            payload .append ({
            "name":c .name ,
            "credits":float (c .credits ),
            "score_text":str (c .score_text or ""),
            "semester":c .semester ,
            "semester_index":int (c .semester_index ),
            "course_type":c .course_type ,
            "source_major_flag":bool (c .source_major_flag ),
            "course_code":str (c .course_code or "")
            })
        return payload 

    def _deserialize_courses (self ,payload :List [dict ])->List [Course ]:
        res :List [Course ]=[]
        for it in (payload or []):
            if not isinstance (it ,dict ):
                continue 
            res .append (Course (
            name =str (it .get ("name","")or ""),
            credits =safe_float (it .get ("credits",0.0 ),0.0 ),
            score_text =str (it .get ("score_text","")or ""),
            semester =str (it .get ("semester","未知学期")or "未知学期"),
            semester_index =int (safe_float (it .get ("semester_index",0 ),0 )),
            course_type =str (it .get ("course_type",TYPE_NONMAJOR )or TYPE_NONMAJOR ),
            source_major_flag =bool (it .get ("source_major_flag",False )),
            course_code =str (it .get ("course_code","")or "")
            ))
        res .sort (key =lambda c :(c .semester_index ,c .name ))
        return res 

    def _get_view_weights (self )->WeightsConfig :
        if self ._view_weights is not None :
            return self ._view_weights 
        return self .config_store .get_weights (self .username )

    def _refresh_sim_profile_options (self )->None :
        st =self ._get_sim_store ()
        profiles =st .get ("profiles",{})if isinstance (st .get ("profiles"),dict )else {}

        names =["主配置"]
        for pid ,p in profiles .items ():
            if not isinstance (p ,dict ):
                continue 
            nm =str (p .get ("name",pid )or pid )
            names .append (nm )

        self .cmb_sim_profile .configure (values =names )

        cur =self .var_sim_profile .get ()
        if cur not in names :
            self .var_sim_profile .set ("主配置")

    def _toggle_sim_mode (self )->None :
        enabled =bool (self .var_sim_enabled .get ())
        st =self ._get_sim_store ()
        st ["enabled"]=enabled 

        self ._sim_enabled =enabled 

        
        profiles =st .get ("profiles",{})
        if enabled and isinstance (profiles ,dict )and not profiles :
            pid =f"sim_{int (time .time ())}"
            wc0 =self .config_store .get_weights (self .username )
            profiles [pid ]={
            "name":"模拟配置 1",
            "courses":self ._serialize_courses (self .courses ),
            "weights":{
            "nonmajor_weight":float (wc0 .nonmajor_weight ),
            "core_multiplier":float (wc0 .core_multiplier ),
            "core_mode":wc0 .core_mode ,
            "retake_policy":wc0 .retake_policy ,
            }
            }
            st ["active_id"]=pid 
            self ._save_sim_store (st )

        self ._refresh_sim_profile_options ()

        
        state ="readonly"if enabled else "disabled"
        btn_state ="normal"if enabled else "disabled"
        self .cmb_sim_profile .configure (state =state )
        self .btn_sim_new .configure (state =btn_state )
        self .btn_sim_dup .configure (state =btn_state )
        self .btn_sim_del .configure (state =btn_state )
        self .btn_sim_add_course .configure (state =btn_state )

        if not enabled :
        
            self .var_sim_profile .set ("主配置")
            self .view_courses =self .courses 
            self ._view_weights =None 

            self ._refresh_filter_options ()
            self ._render_stats ()
            self ._refresh_cards ()
            return 

            
            
        self ._switch_sim_profile (force =True )

    def _switch_sim_profile (self ,force :bool =False )->None :
        if not self ._sim_enabled and not force :
            return 

        st =self ._get_sim_store ()
        profiles =st .get ("profiles",{})if isinstance (st .get ("profiles"),dict )else {}

        sel_name =self .var_sim_profile .get ()
        if sel_name =="主配置":
            self .view_courses =self .courses 
            self ._view_weights =None 
            self ._sim_active_id =""
            st ["active_id"]=""
            self ._save_sim_store (st )
            self ._refresh_filter_options ()
            self ._render_stats ()
            self ._refresh_cards ()
            return 

            # name -> id
        pid_match =""
        for pid ,p in profiles .items ():
            if not isinstance (p ,dict ):
                continue 
            if str (p .get ("name",pid )or pid )==sel_name :
                pid_match =pid 
                break 
        if not pid_match :
            return 

        st ["active_id"]=pid_match 
        self ._save_sim_store (st )

        p =profiles .get (pid_match ,{})
        if not isinstance (p ,dict ):
            return 

        self ._sim_active_id =pid_match 
        self .view_courses =self ._deserialize_courses (p .get ("courses",[])or [])

        w =p .get ("weights",{})if isinstance (p .get ("weights"),dict )else {}
        rp =w .get ("retake_policy",RETAKE_BEST )
        if rp not in (RETAKE_BEST ,RETAKE_FIRST ):
            rp =RETAKE_BEST 
        self ._view_weights =WeightsConfig (
        nonmajor_weight =safe_float (w .get ("nonmajor_weight",0.3 ),0.3 ),
        core_multiplier =safe_float (w .get ("core_multiplier",1.2 ),1.2 ),
        core_mode =w .get ("core_mode","gpa")if w .get ("core_mode","gpa")in ("gpa","credits")else "gpa",
        retake_policy =rp 
        )

        self ._refresh_filter_options ()
        self ._render_stats ()
        self ._refresh_cards ()

    def _new_sim_profile (self )->None :
        st =self ._get_sim_store ()
        profiles =st .get ("profiles",{})
        if not isinstance (profiles ,dict ):
            profiles ={}
            st ["profiles"]=profiles 

        name =simpledialog .askstring ("新建模拟配置","给这份模拟配置起个名字：",parent =self )
        if not name :
            return 

        pid =f"sim_{int (time .time ())}"
        wc =self .config_store .get_weights (self .username )
        profiles [pid ]={
        "name":name .strip (),
        "courses":self ._serialize_courses (self .courses ),
        "weights":{
        "nonmajor_weight":float (wc .nonmajor_weight ),
        "core_multiplier":float (wc .core_multiplier ),
        "core_mode":wc .core_mode ,
        "retake_policy":wc .retake_policy 
        }
        }
        st ["active_id"]=pid 
        self ._save_sim_store (st )

        self ._refresh_sim_profile_options ()
        self .var_sim_profile .set (name .strip ())
        self ._switch_sim_profile (force =True )

    def _dup_sim_profile (self )->None :
        if not self ._sim_enabled :
            return 
        st =self ._get_sim_store ()
        profiles =st .get ("profiles",{})
        if not isinstance (profiles ,dict )or not profiles :
            return 

        cur =st .get ("active_id","")or ""
        if not cur or cur not in profiles :
            return 

        name =simpledialog .askstring ("复制模拟配置","复制后新配置的名字：",parent =self )
        if not name :
            return 

        src =profiles .get (cur ,{})
        if not isinstance (src ,dict ):
            return 

        pid =f"sim_{int (time .time ())}"
        profiles [pid ]={
        "name":name .strip (),
        "courses":list (src .get ("courses",[])or []),
        "weights":dict (src .get ("weights",{})or {})
        }
        st ["active_id"]=pid 
        self ._save_sim_store (st )

        self ._refresh_sim_profile_options ()
        self .var_sim_profile .set (name .strip ())
        self ._switch_sim_profile (force =True )

    def _del_sim_profile (self )->None :
        if not self ._sim_enabled :
            return 
        st =self ._get_sim_store ()
        profiles =st .get ("profiles",{})
        if not isinstance (profiles ,dict )or not profiles :
            return 
        cur =st .get ("active_id","")or ""
        if not cur or cur not in profiles :
            return 

        if not messagebox .askyesno ("删除模拟配置","真的要删除当前模拟配置吗？(；´д｀)\n\n不会影响主配置。"):
            return 

        try :
            del profiles [cur ]
        except Exception :
            profiles [cur ]={}

        st ["active_id"]=""
        self ._save_sim_store (st )

        self ._refresh_sim_profile_options ()
        self .var_sim_profile .set ("主配置")
        self ._switch_sim_profile (force =True )

    def _persist_current_sim_view (self )->None :
        if not self ._sim_enabled :
            return 
        st =self ._get_sim_store ()
        profiles =st .get ("profiles",{})
        if not isinstance (profiles ,dict ):
            return 
        pid =st .get ("active_id","")or ""
        if not pid or pid not in profiles :
            return 
        p =profiles .get (pid ,{})
        if not isinstance (p ,dict ):
            return 

        p ["courses"]=self ._serialize_courses (self .view_courses )

        if self ._view_weights is not None :
            p ["weights"]={
            "nonmajor_weight":float (self ._view_weights .nonmajor_weight ),
            "core_multiplier":float (self ._view_weights .core_multiplier ),
            "core_mode":self ._view_weights .core_mode ,
            "retake_policy":self ._view_weights .retake_policy 
            }

        profiles [pid ]=p 
        st ["profiles"]=profiles 
        self ._save_sim_store (st )

    def _add_sim_course (self )->None :
        if not self ._sim_enabled :
            return 

        name =simpledialog .askstring ("新增课程（模拟）","课程名：",parent =self )
        if not name :
            return 
        credits =simpledialog .askfloat ("新增课程（模拟）","学分：",parent =self ,minvalue =0.0 )
        if credits is None :
            return 
        sem_idx =simpledialog .askinteger ("新增课程（模拟）","学期序号（1~12）：",parent =self ,minvalue =1 ,maxvalue =MAX_SEMESTER_INDEX )
        if sem_idx is None :
            return 
        score =simpledialog .askstring ("新增课程（模拟）","成绩（如 92 / 良好 / 合格）：",parent =self )
        if score is None :
            return 

        semester_text =f"第{sem_idx }学期（模拟）"

        self .view_courses .append (Course (
        name =name .strip (),
        credits =float (credits ),
        score_text =str (score ).strip (),
        semester =semester_text ,
        semester_index =int (sem_idx ),
        course_type =TYPE_NONMAJOR ,
        source_major_flag =False ,
        course_code =""
        ))
        self .view_courses .sort (key =lambda c :(c .semester_index ,c .name ))

        self ._persist_current_sim_view ()
        self ._refresh_filter_options ()
        self ._render_stats ()
        self ._refresh_cards ()

    def _delete_sim_course (self ,course :Course )->None :
        if not self ._sim_enabled :
            return 
        if not messagebox .askyesno ("删除课程（模拟）",f"要删除「{course .name }」这张模拟卡片吗？(；´∀｀)\n\n不会影响主配置。"):
            return 
        self .view_courses =[c for c in self .view_courses if c is not course ]
        self ._persist_current_sim_view ()
        self ._refresh_filter_options ()
        self ._render_stats ()
        self ._refresh_cards ()

    def _on_sim_score_change (self ,course :Course ,new_score_text :str )->None :
        if not self ._sim_enabled :
            return 
        course .score_text =str (new_score_text or "").strip ()
        self ._persist_current_sim_view ()
        self ._render_stats ()
        self ._refresh_cards ()

        
    def _stat_card (
    self ,
    parent ,
    title :str ,
    *,
    header_fg :str =COLOR_TEXT ,
    header_font :Tuple [str ,int ,str ]=("Microsoft YaHei UI",10 ,"bold")
    )->tk .Frame :
        card =tk .Frame (parent ,bg =COLOR_CARD ,highlightthickness =1 ,highlightbackground =COLOR_BORDER )
        card .pack (fill ="x",padx =2 ,pady =8 )
        header =tk .Label (card ,text =title ,bg =COLOR_CARD ,fg =header_fg ,font =header_font )
        header .pack (anchor ="w",padx =12 ,pady =(10 ,6 ))
        body =tk .Frame (card ,bg =COLOR_CARD )
        body .pack (fill ="x",padx =12 ,pady =(0 ,10 ))
        body ._row =0 # type: ignore[attr-defined]
        return body 

    def _stat_row (self ,parent ,left :str ,right :str ,bold =False ):
        row =getattr (parent ,"_row",0 )
        f =("Microsoft YaHei UI",10 ,"bold")if bold else ("Microsoft YaHei UI",10 )

        tk .Label (parent ,text =left ,bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (
        row =row ,column =0 ,sticky ="w",pady =2 
        )
        tk .Label (parent ,text =right ,bg =COLOR_CARD ,fg =COLOR_TEXT ,font =f ).grid (
        row =row ,column =1 ,sticky ="e",pady =2 
        )
        parent .grid_columnconfigure (1 ,weight =1 )
        setattr (parent ,"_row",row +1 )

    def _build_weights_controls (self ,parent ):
        wc =self .config_store .get_weights (self .username )

        body =self ._stat_card (parent ,"加权设置 / 重修规则")

        self .var_w_nonmajor =tk .StringVar (value =str (wc .nonmajor_weight ))
        self .var_w_core =tk .StringVar (value =str (wc .core_multiplier ))
        self .var_core_mode =tk .StringVar (value =wc .core_mode )
        self .var_retake =tk .StringVar (value =wc .retake_policy )

        
        self .var_stats_by_semester =tk .BooleanVar (value =False )

        
        tk .Label (
        body ,text ="非主修权重(0~1)",
        bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )
        ).grid (row =0 ,column =0 ,sticky ="w")
        ttk .Entry (body ,textvariable =self .var_w_nonmajor ,width =10 ).grid (row =0 ,column =1 ,sticky ="w",padx =(8 ,0 ))

        
        tk .Label (
        body ,text ="专业核心权重(1~2)",
        bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )
        ).grid (row =1 ,column =0 ,sticky ="w",pady =(10 ,0 ))
        ttk .Entry (body ,textvariable =self .var_w_core ,width =10 ).grid (row =1 ,column =1 ,sticky ="w",padx =(8 ,0 ),pady =(10 ,0 ))

        
        tk .Label (body ,text ="专业核心权重作用",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (
        row =2 ,column =0 ,sticky ="w",pady =(10 ,0 )
        )
        ttk .Radiobutton (body ,text ="乘在绩点上",variable =self .var_core_mode ,value ="gpa").grid (
        row =2 ,column =1 ,sticky ="w",padx =(8 ,0 ),pady =(10 ,0 )
        )
        ttk .Radiobutton (body ,text ="乘在学分上",variable =self .var_core_mode ,value ="credits").grid (
        row =3 ,column =1 ,sticky ="w",padx =(8 ,0 ),pady =(6 ,0 )
        )

        
        tk .Label (body ,text ="重修计算",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (
        row =4 ,column =0 ,sticky ="w",pady =(10 ,0 )
        )
        ttk .Radiobutton (body ,text ="取最高",variable =self .var_retake ,value =RETAKE_BEST ).grid (
        row =4 ,column =1 ,sticky ="w",padx =(8 ,0 ),pady =(10 ,0 )
        )
        ttk .Radiobutton (body ,text ="取首次",variable =self .var_retake ,value =RETAKE_FIRST ).grid (
        row =4 ,column =2 ,sticky ="w",padx =(8 ,0 ),pady =(10 ,0 )
        )

        
        chk =tk .Checkbutton (
        body ,
        text ="按学期显示",
        variable =self .var_stats_by_semester ,
        command =self ._render_stats ,
        bg =COLOR_CARD ,
        fg =COLOR_TEXT ,
        activebackground =COLOR_CARD ,
        activeforeground =COLOR_TEXT ,
        selectcolor =COLOR_CARD ,
        relief ="flat",
        highlightthickness =0 
        )
        chk .grid (row =5 ,column =0 ,columnspan =3 ,sticky ="w",pady =(12 ,0 ))

        
        ttk .Button (body ,text ="保存并重算",style ="Accent.TButton",command =self ._apply_weights ).grid (
        row =6 ,column =0 ,columnspan =4 ,sticky ="we",pady =(12 ,0 )
        )

        for i in range (4 ):
            body .grid_columnconfigure (i ,weight =1 )

        setattr (body ,"_row",0 )

    def _apply_weights (self ):
        x =safe_float (self .var_w_nonmajor .get (),-1 )
        y =safe_float (self .var_w_core .get (),-1 )
        mode =self .var_core_mode .get ()
        retake =self .var_retake .get ()

        if not (0.0 <=x <=1.0 ):
            messagebox .showerror ("参数错误","非主修权重 x 必须满足 0 <= x <= 1。")
            return 
        if not (1.0 <=y <=2.0 ):
            messagebox .showerror ("参数错误","专业核心权重 y 必须满足 1 <= y <= 2。")
            return 
        if mode not in ("gpa","credits"):
            messagebox .showerror ("参数错误","倍率作用模式无效。")
            return 
        if retake not in (RETAKE_BEST ,RETAKE_FIRST ):
            messagebox .showerror ("参数错误","重修规则无效。")
            return 

        wc =WeightsConfig (nonmajor_weight =x ,core_multiplier =y ,core_mode =mode ,retake_policy =retake )
        if self ._sim_enabled and (self .var_sim_profile .get ()!="主配置"):
        
            self ._view_weights =wc 
            self ._persist_current_sim_view ()
        else :
            self .config_store .set_weights (wc ,self .username )
            self ._view_weights =None 

        self ._log (
        f"{now_str ()}：已保存权重：非主修x={x :.2f}，核心y={y :.2f}，模式={('乘绩点'if mode =='gpa'else '乘学分')}，"
        f"重修={('取最高'if retake ==RETAKE_BEST else '取第一次')}"
        )
        self ._render_stats ()

        
    def _raw_to_courses (self ,raw_courses :List [dict ],keep_user_override :bool )->List [Course ]:
        sems =sorted ({(rc .get ("semester")or "未知学期")for rc in raw_courses },key =parse_semester_sort_key )
        sem_to_idx :Dict [str ,int ]={}
        idx =1 
        for s in sems :
            sem_to_idx [s ]=idx 
            idx +=1 
            if idx >MAX_SEMESTER_INDEX :
                break 

                
        merged :Dict [Tuple [str ,float ,str ],dict ]={}
        for rc in (raw_courses or []):
            name0 =(rc .get ("name")or "").strip ()
            credits0 =safe_float (rc .get ("credits",0.0 ),0.0 )
            sem0 =(rc .get ("semester")or "未知学期").strip ()
            score0 =str (rc .get ("score","")).strip ()
            if not name0 or not score0 :
                continue 

            credits2 =float (f"{credits0 :.2f}")
            key =(name0 ,credits2 ,sem0 )

            cur =merged .get (key )
            if cur is None :
                merged [key ]=dict (rc )
            else :
            
                cur ["is_major"]=bool (cur .get ("is_major",False ))or bool (rc .get ("is_major",False ))
                
                if not str (cur .get ("course_code","")or "").strip ():
                    cc =str (rc .get ("course_code","")or "").strip ()
                    if cc :
                        cur ["course_code"]=cc 

        courses :List [Course ]=[]
        for rc in merged .values ():
            name =(rc .get ("name")or "").strip ()
            credits =safe_float (rc .get ("credits",0.0 ),0.0 )
            score =str (rc .get ("score","")).strip ()
            sem =(rc .get ("semester")or "未知学期").strip ()
            is_major =bool (rc .get ("is_major",False ))

            if not name or not score :
                continue 

            sem_idx =sem_to_idx .get (sem ,0 )
            code =str (rc .get ("course_code","")or "").strip ()
            k =course_key (name ,credits ,sem ,code )

            default_type =TYPE_MAJOR if is_major else TYPE_NONMAJOR 
            if keep_user_override :
                ov =self .config_store .get_override_type (k ,self .username )
                ctype =ov if ov else default_type 
            else :
                ctype =default_type 

            courses .append (Course (
            name =name ,
            credits =credits ,
            score_text =score ,
            semester =sem ,
            semester_index =sem_idx ,
            course_type =ctype ,
            source_major_flag =is_major ,
            course_code =code 
            ))

        courses .sort (key =lambda c :(c .semester_index ,c .name ))
        return courses 

    def _snapshot_courses (self ):
        ensure_dir (SNAPSHOT_DIR )
        payload =[]
        for c in self .courses :
            payload .append ({
            "name":c .name ,
            "credits":c .credits ,
            "score":c .score_text ,
            "semester":c .semester ,
            "semester_index":c .semester_index ,
            "course_type":c .course_type ,
            "course_code":c .course_code ,
            "source_major_flag":c .source_major_flag 
            })
        fp =os .path .join (SNAPSHOT_DIR ,f"courses_{datetime .now ().strftime ('%Y%m%d_%H%M%S')}.json")
        try :
            with open (fp ,"w",encoding ="utf-8")as f :
                json .dump (payload ,f ,ensure_ascii =False ,indent =2 )
        except Exception :
            pass 

    def _refresh_filter_options (self ):
        max_sem =max ([c .semester_index for c in self .view_courses ],default =0 )
        max_year =(max_sem +1 )//2 if max_sem >0 else 0 

        range_vals =[TYPE_ALL ]
        if max_year >0 :
            range_vals .extend ([f"第{y }学年"for y in range (1 ,max_year +1 )])
        if max_sem >0 :
            range_vals .extend ([f"第{s }学期"for s in range (1 ,max_sem +1 )])

        type_vals =[TYPE_ALL ,TYPE_CORE ,"仅主修（含核心）",TYPE_NONMAJOR ,TYPE_INVISIBLE ]

        self .cmb_range .configure (values =range_vals )
        self .cmb_type .configure (values =type_vals )

        if self .var_range .get ()not in range_vals :
            self .var_range .set (TYPE_ALL )
        if self .var_type .get ()not in type_vals :
            self .var_type .set (TYPE_ALL )

    def _smart_threshold (self )->Tuple [Optional [str ],Optional [float ]]:
        
        op =self .var_score_op .get ()
        if op not in ("≥","≤"):
            return None ,None 
        sval =(self .var_score_val .get ()or "").strip ()
        if not sval :
            return None ,None 
        try :
            v =float (sval )
        except Exception :
            return None ,None 
        if v <0 :
            return None ,None 
        return ("gpa",v )if v <=10 else ("score",v )

    def _filter_courses (self )->List [Course ]:
        res =list (self .view_courses )

        r =self .var_range .get ()
        if r !=TYPE_ALL and r .startswith ("第"):
            if r .endswith ("学年"):
                try :
                    yy =int (r .replace ("第","").replace ("学年",""))
                    sem_a =2 *yy -1 
                    sem_b =2 *yy 
                    res =[c for c in res if c .semester_index in (sem_a ,sem_b )]
                except Exception :
                    pass 
            elif r .endswith ("学期"):
                try :
                    ss =int (r .replace ("第","").replace ("学期",""))
                    res =[c for c in res if c .semester_index ==ss ]
                except Exception :
                    pass 

        t =self .var_type .get ()
        if t ==TYPE_CORE :
            res =[c for c in res if c .course_type ==TYPE_CORE ]
        elif t =="仅主修（含核心）":
            res =[c for c in res if c .course_type in (TYPE_MAJOR ,TYPE_CORE )]
        elif t ==TYPE_NONMAJOR :
            res =[c for c in res if c .course_type ==TYPE_NONMAJOR ]
        elif t ==TYPE_INVISIBLE :
            res =[c for c in res if c .course_type ==TYPE_INVISIBLE ]


        kind ,thr =self ._smart_threshold ()
        op =self .var_score_op .get ()
        if kind and thr is not None :
            if kind =="gpa":
                if op =="≥":
                    res =[c for c in res if convert_grade (c .score_text )[1 ]>=thr ]
                else :
                    res =[c for c in res if convert_grade (c .score_text )[1 ]<=thr ]
            else :
                if op =="≥":
                    res =[c for c in res if convert_grade (c .score_text )[0 ]>=thr ]
                else :
                    res =[c for c in res if convert_grade (c .score_text )[0 ]<=thr ]

        q =""
        if hasattr (self ,"var_query"):
            q =(self .var_query .get ()or "").strip ().lower ()

        if q :
            def _match (c :Course )->bool :
                name =(c .name or "").strip ().lower ()
                if q in name :
                    return True 
                ini =pinyin_initials (c .name )
                return q in ini 

            res =[c for c in res if _match (c )]

        return res 


    def _clear_cards (self ):
        for w in self .cards_scroll .inner .winfo_children ():
            w .destroy ()

    def _refresh_cards (self ):
    
        y0 =None 
        try :
            y0 =self .cards_scroll .canvas .yview ()[0 ]
        except Exception :
            y0 =None 

            
        try :
            self .cards_scroll .canvas .itemconfig (self .cards_scroll .inner_id ,state ="hidden")
        except Exception :
            pass 

        try :
            self ._clear_cards ()
            shown =self ._filter_courses ()
            if not shown :
                tk .Label (self .cards_scroll .inner ,text ="没有符合条件的课程。",fg =COLOR_SUBTEXT ,bg =COLOR_BG ).pack (
                anchor ="w",pady =10 
                )
                return 

            pending =set (getattr (self ,"new_course_pending_keys",set ()))
            for c in shown :
                k =course_key (c .name ,c .credits ,c .semester ,c .course_code )
                base_c =None 
                if self ._sim_enabled and (self .var_sim_profile .get ()!="主配置"):
                    k_main =course_key (c .name ,c .credits ,c .semester ,c .course_code )
                    base_c =self .course_by_key .get (k_main )

                card =CourseCard (
                self .cards_scroll .inner ,
                c ,
                self ._on_course_type_change ,
                is_new =(k in pending ),
                on_ack_new =self ._ack_new_course ,
                sim_enabled =bool (self ._sim_enabled and (self .var_sim_profile .get ()!="主配置")),
                base_score_text =(base_c .score_text if base_c else ""),
                on_sim_score_change =self ._on_sim_score_change ,
                on_delete_course =self ._delete_sim_course 
                )
                card .pack (fill ="x",pady =7 ,padx =0 )

        finally :
        
            try :
                self .cards_scroll .inner .update_idletasks ()
                self .cards_scroll .canvas .configure (scrollregion =self .cards_scroll .canvas .bbox ("all"))
                if y0 is not None :
                    self .cards_scroll .canvas .yview_moveto (y0 )
            except Exception :
                pass 

            try :
                self .cards_scroll .canvas .itemconfig (self .cards_scroll .inner_id ,state ="normal")
            except Exception :
                pass 

    def _ack_new_course (self ,course :Course ):
        k =course_key (course .name ,course .credits ,course .semester ,course .course_code )
        pending =getattr (self ,"new_course_pending_keys",set ())
        if k in pending :
            pending .remove (k )
            self .new_course_pending_keys =pending 
            self ._refresh_cards ()
            self ._log (f"{now_str ()}：已确认新增课程：{course .name }")

    def _on_course_type_change (self ,course :Course ,new_type :str ):
        if self ._sim_enabled and (self .var_sim_profile .get ()!="主配置"):
        
            course .course_type =new_type 
            self ._persist_current_sim_view ()
            self ._refresh_cards ()
            self ._render_stats ()
            self ._log (f"{now_str ()}：已修改课程类型（模拟）：[{course .name }] -> {new_type }")
            return 

        k =course_key (course .name ,course .credits ,course .semester ,course .course_code )
        if self .config_store .get_override_type (k ,self .username )==new_type :
            return 
        self .config_store .set_override_type (k ,new_type ,self .username )
        self ._refresh_cards ()
        self ._render_stats ()
        self ._log (f"{now_str ()}：已修改课程类型：[{course .name }] -> {new_type }")

    def _metric_components (self ,courses :List [Course ],wc :WeightsConfig ,kind :str )->Tuple [float ,float ,float ]:
        
        stat_list =_stat_courses_for_analysis (courses ,wc )

        if kind =="gpa43":
            den =0.0 
            num =0.0 
            for c in stat_list :
                _s ,g43 =convert_grade_43 (c .score_text )
                cr =float (c .credits )
                num +=g43 *cr 
                den +=cr 
            cur =0.0 if den <=1e-9 else round (num /den ,4 )
            return cur ,num ,den 

        if kind =="avg_gpa":
            den =0.0 
            num =0.0 
            for c in stat_list :
                _s ,g =convert_grade (c .score_text )
                cr =float (c .credits )
                num +=g *cr 
                den +=cr 
            cur =0.0 if den <=1e-9 else round (num /den ,4 )
            return cur ,num ,den 

        if kind =="w_gpa":
            den =0.0 
            num =0.0 
            for c in stat_list :
                _s ,g =convert_grade (c .score_text )
                cr =float (c .credits )

                nonmajor_x =float (wc .nonmajor_weight )if c .course_type ==TYPE_NONMAJOR else 1.0 

                if c .course_type ==TYPE_CORE :
                    if wc .core_mode =="gpa":
                        g =g *float (wc .core_multiplier )
                        w =cr *nonmajor_x 
                    else :
                        w =cr *nonmajor_x *float (wc .core_multiplier )
                else :
                    w =cr *nonmajor_x 

                num +=g *w 
                den +=w 

            cur =0.0 if den <=1e-9 else round (num /den ,4 )
            return cur ,num ,den 

        return 0.0 ,0.0 ,0.0 

    def _refresh_target_progress_view (self )->None :
        
        
        if not hasattr (self ,"lbl_target_43"):
            return 

            
        avg_line ="均绩：-"
        w_line ="加权均绩：-"
        g43_line ="4.3分制：-"

        try :
            st =self ._get_targets_store ()
            wc =self ._get_view_weights ()
            courses_ref =self .view_courses 

            def _try_float (s :str ):
                try :
                    s =(s or "").strip ()
                    if s =="":
                        return None 
                    return float (s )
                except Exception :
                    return None 

                    
            avg_t =_try_float (str (st .get ("avg_gpa_target","")or ""))
            w_t =_try_float (str (st .get ("w_gpa_target","")or ""))
            g43_t =_try_float (str (st .get ("gpa43_target","")or ""))

            
            E =_try_float (str (st .get ("expected_credits","")or ""))
            M =_try_float (str (st .get ("expected_major_credits","")or ""))
            e_txt ="-"if E is None else f"{E :.1f}"

            
            cur_avg =float (compute_metrics (courses_ref ,wc ,weighted =False )[1 ])
            cur_w =float (compute_metrics (courses_ref ,wc ,weighted =True )[1 ])
            cur_43 =float (compute_gpa_43 (courses_ref ,wc ))

            
            stat_list =_stat_courses_for_analysis (courses_ref ,wc )

            
            
            den_avg =0.0 
            num_avg =0.0 

            
            den_w =0.0 
            num_w =0.0 

            # 3) 4.3 GPA：num/den = Σ(g43*cr) / Σ(cr)
            den_43 =0.0 
            num_43 =0.0 

            for c in stat_list :
                cr =float (c .credits )

                
                _s ,gpa =convert_grade (c .score_text )
                num_avg +=float (gpa )*cr 
                den_avg +=cr 

                
                gpa2 =float (gpa )
                w =cr 

                nonmajor_x =float (wc .nonmajor_weight )if c .course_type ==TYPE_NONMAJOR else 1.0 

                if c .course_type ==TYPE_CORE :
                    if wc .core_mode =="gpa":
                        gpa2 =gpa2 *float (wc .core_multiplier )
                        w =cr *nonmajor_x 
                    else :
                        w =cr *nonmajor_x *float (wc .core_multiplier )
                else :
                    w =cr *nonmajor_x 

                num_w +=gpa2 *w 
                den_w +=w 

                # 4.3 GPA
                _s43 ,g43 =convert_grade_43 (c .score_text )
                num_43 +=float (g43 )*cr 
                den_43 +=cr 

            def _need_future (target ,cur_num ,cur_den ,future_den ,mx ,note ="")->str :
                if target is None :
                    return "未设置目标"
                if future_den is None or future_den <=1e-9 :
                    return "未填写预期学分"
                    # (cur_num + need*future_den) / (cur_den + future_den) = target
                need =(float (target )*(float (cur_den )+float (future_den ))-float (cur_num ))/float (future_den )
                
                if need <0 :
                    need_txt ="0.0000（目标已达成）"
                elif need >mx :
                    need_txt =f">{mx :.4f}（不太可能）"
                else :
                    need_txt =f"{need :.4f}"
                return f"未来需均值 {need_txt }{note }"

                
                
            future_den_avg =E 
            future_den_43 =E 

            
            w_note =""
            future_den_w =None 
            if E is not None :
                x =float (wc .nonmajor_weight )
                if M is None :
                
                    future_den_w =float (E )*x 
                    w_note ="（未填主修学分，按全部非主修估算）"
                else :
                
                    if M >E :
                        future_den_w =float (E )
                        w_note ="（主修学分>总学分，已按总学分处理）"
                    else :
                        future_den_w =float (M )*1.0 +float (E -M )*x 

                        
            avg_line =(
            f"均绩：当前 {cur_avg :.4f} / 目标 {('-'if avg_t is None else f'{avg_t :.4f}')} ｜"
            f"预期学分 {e_txt } ｜{_need_future (avg_t ,num_avg ,den_avg ,future_den_avg ,5.0 )}"
            )
            w_line =(
            f"加权均绩：当前 {cur_w :.4f} / 目标 {('-'if w_t is None else f'{w_t :.4f}')} ｜"
            f"预期学分 {e_txt } ｜{_need_future (w_t ,num_w ,den_w ,future_den_w ,5.5 ,note =w_note )}"
            )
            g43_line =(
            f"4.3分制：当前 {cur_43 :.4f} / 目标 {('-'if g43_t is None else f'{g43_t :.4f}')} ｜"
            f"预期学分 {e_txt } ｜{_need_future (g43_t ,num_43 ,den_43 ,future_den_43 ,4.3 )}"
            )

        except Exception as e :
        
            g43_line =f"4.3分制：计算异常（{e .__class__ .__name__ }）"
            
            avg_line =f"均绩：计算异常（{e .__class__ .__name__ }）"
            w_line =f"加权均绩：计算异常（{e .__class__ .__name__ }）"

            
        if hasattr (self ,"lbl_target_avg"):
            self .lbl_target_avg .configure (text =avg_line )
        if hasattr (self ,"lbl_target_w"):
            self .lbl_target_w .configure (text =w_line )
        self .lbl_target_43 .configure (text =g43_line )



    def _render_stats (self ):
    
        y0 =None 
        try :
            y0 =self .stats_scroll .canvas .yview ()[0 ]
        except Exception :
            y0 =None 

            
        try :
            self .stats_scroll .canvas .itemconfig (self .stats_scroll .inner_id ,state ="hidden")
        except Exception :
            pass 

        try :
        
            children =self .stats_scroll .inner .winfo_children ()
            for w in children [2 :]:
                w .destroy ()

                
            self ._refresh_target_progress_view ()

            wc_main =self .config_store .get_weights (self .username )
            wc_view =self ._get_view_weights ()

            
            wc =wc_view 

            
            courses_ref =self .view_courses 

            header_big =("Microsoft YaHei UI",11 ,"bold")

            def _delta_color (d :float )->str :
                if d <-1e-9 :
                    return COLOR_DELTA_BAD 
                if d >1e-9 :
                    return COLOR_DELTA_GOOD 
                return COLOR_SUBTEXT 

            def _stat_row_delta (parent ,left :str ,val :float ,base :Optional [float ],*,fmt :str ="{:.4f}",bold =False ):
                if base is None :
                    self ._stat_row (parent ,left ,fmt .format (val ),bold =bold )
                    return 
                d =float (val -float (base ))
                
                row =getattr (parent ,"_row",0 )
                f =("Microsoft YaHei UI",10 ,"bold")if bold else ("Microsoft YaHei UI",10 )

                tk .Label (parent ,text =left ,bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (
                row =row ,column =0 ,sticky ="w",pady =2 
                )

                cell =tk .Frame (parent ,bg =COLOR_CARD )
                cell .grid (row =row ,column =1 ,sticky ="e",pady =2 )

                tk .Label (cell ,text =fmt .format (val ),bg =COLOR_CARD ,fg =COLOR_TEXT ,font =f ).pack (side ="left")
                tk .Label (
                cell ,
                text =f"  (Δ{d :+.4f})",
                bg =COLOR_CARD ,
                fg =_delta_color (d ),
                font =("Microsoft YaHei UI",9 ,"bold")
                ).pack (side ="left")

                parent .grid_columnconfigure (1 ,weight =1 )
                setattr (parent ,"_row",row +1 )

                

        finally :
        
            try :
                self .stats_scroll .inner .update_idletasks ()
                self .stats_scroll .canvas .configure (scrollregion =self .stats_scroll .canvas .bbox ("all"))
                if y0 is not None :
                    self .stats_scroll .canvas .yview_moveto (y0 )
            except Exception :
                pass 

            try :
                self .stats_scroll .canvas .itemconfig (self .stats_scroll .inner_id ,state ="normal")
            except Exception :
                pass 

                
        wc =wc_view 

        
        courses_ref =self .view_courses 

        header_big =("Microsoft YaHei UI",11 ,"bold")

        def _delta_color (d :float )->str :
            if d <-1e-9 :
                return COLOR_DELTA_BAD 
            if d >1e-9 :
                return COLOR_DELTA_GOOD 
            return COLOR_SUBTEXT 

        def _stat_row_delta (parent ,left :str ,val :float ,base :Optional [float ],*,fmt :str ="{:.4f}",bold =False ):
            if base is None :
                self ._stat_row (parent ,left ,fmt .format (val ),bold =bold )
                return 
            d =float (val -float (base ))
            
            row =getattr (parent ,"_row",0 )
            f =("Microsoft YaHei UI",10 ,"bold")if bold else ("Microsoft YaHei UI",10 )

            tk .Label (parent ,text =left ,bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 )).grid (
            row =row ,column =0 ,sticky ="w",pady =2 
            )

            cell =tk .Frame (parent ,bg =COLOR_CARD )
            cell .grid (row =row ,column =1 ,sticky ="e",pady =2 )

            tk .Label (cell ,text =fmt .format (val ),bg =COLOR_CARD ,fg =COLOR_TEXT ,font =f ).pack (side ="left")
            tk .Label (
            cell ,
            text =f"  (Δ{d :+.4f})",
            bg =COLOR_CARD ,
            fg =_delta_color (d ),
            font =("Microsoft YaHei UI",9 ,"bold")
            ).pack (side ="left")

            parent .grid_columnconfigure (1 ,weight =1 )
            setattr (parent ,"_row",row +1 )

            
        comparing =bool (self ._sim_enabled and (self .var_sim_profile .get ()!="主配置"))

        
        body =self ._stat_card (self .stats_scroll .inner ,"总览",header_fg =COLOR_TEXT ,header_font =header_big )

        total_credits_view =credits_sum_unique (courses_ref ,wc_view )
        avg_score_view ,avg_gpa_view =compute_metrics (courses_ref ,wc_view ,weighted =False )
        w_score_view ,w_gpa_view =compute_metrics (courses_ref ,wc_view ,weighted =True )
        gpa_43_view =compute_gpa_43 (courses_ref ,wc_view )

        if comparing :
            total_credits_main =credits_sum_unique (self .courses ,wc_main )
            avg_score_main ,avg_gpa_main =compute_metrics (self .courses ,wc_main ,weighted =False )
            w_score_main ,w_gpa_main =compute_metrics (self .courses ,wc_main ,weighted =True )
            gpa_43_main =compute_gpa_43 (self .courses ,wc_main )
        else :
            total_credits_main =None 
            avg_score_main =None 
            avg_gpa_main =None 
            w_score_main =None 
            w_gpa_main =None 
            gpa_43_main =None 

            
        if total_credits_main is None :
            self ._stat_row (body ,"修读学分",f"{total_credits_view :.1f}",bold =True )
        else :
            _stat_row_delta (body ,"修读学分",float (total_credits_view ),float (total_credits_main ),fmt ="{:.1f}",bold =True )

        _stat_row_delta (body ,"总百分制均绩",float (avg_score_view ),avg_score_main ,fmt ="{:.4f}")
        _stat_row_delta (body ,"总五级制均绩",float (avg_gpa_view ),avg_gpa_main ,fmt ="{:.4f}")
        _stat_row_delta (body ,"加权总百分制均绩",float (w_score_view ),w_score_main ,fmt ="{:.4f}")
        _stat_row_delta (body ,"加权总五级制均绩",float (w_gpa_view ),w_gpa_main ,fmt ="{:.4f}")
        _stat_row_delta (body ,"4.3分制均绩",float (gpa_43_view ),gpa_43_main ,fmt ="{:.4f}")

        
        by_semester =bool (getattr (self ,"var_stats_by_semester",tk .BooleanVar (value =False )).get ())

        if by_semester :
            sem_groups =group_by_semester (courses_ref )
            sem_groups_main =group_by_semester (self .courses )if comparing else {}

            for sem_idx in sorted (sem_groups .keys ()):
                sem_color =SEM_COLORS [(max (1 ,sem_idx )-1 )%len (SEM_COLORS )]
                sbody =self ._stat_card (
                self .stats_scroll .inner ,
                f"第{sem_idx }学期",
                header_fg =sem_color ,
                header_font =header_big 
                )
                cs =sem_groups [sem_idx ]

                s_credits =credits_sum_unique (cs ,wc_view )
                s_avg_score ,s_avg_gpa =compute_metrics (cs ,wc_view ,weighted =False )
                s_w_score ,s_w_gpa =compute_metrics (cs ,wc_view ,weighted =True )
                s_gpa_43 =compute_gpa_43 (cs ,wc_view )

                if comparing and (sem_idx in sem_groups_main ):
                    cs0 =sem_groups_main [sem_idx ]
                    b_credits =credits_sum_unique (cs0 ,wc_main )
                    b_avg_score ,b_avg_gpa =compute_metrics (cs0 ,wc_main ,weighted =False )
                    b_w_score ,b_w_gpa =compute_metrics (cs0 ,wc_main ,weighted =True )
                    b_gpa_43 =compute_gpa_43 (cs0 ,wc_main )
                else :
                    b_credits =b_avg_score =b_avg_gpa =b_w_score =b_w_gpa =b_gpa_43 =None 

                _stat_row_delta (sbody ,"修读学分",float (s_credits ),b_credits ,fmt ="{:.1f}",bold =True )
                _stat_row_delta (sbody ,"百分制均绩",float (s_avg_score ),b_avg_score ,fmt ="{:.4f}")
                _stat_row_delta (sbody ,"五级制均绩",float (s_avg_gpa ),b_avg_gpa ,fmt ="{:.4f}")
                _stat_row_delta (sbody ,"加权百分制均绩",float (s_w_score ),b_w_score ,fmt ="{:.4f}")
                _stat_row_delta (sbody ,"加权五级制均绩",float (s_w_gpa ),b_w_gpa ,fmt ="{:.4f}")
                _stat_row_delta (sbody ,"4.3分制均绩",float (s_gpa_43 ),b_gpa_43 ,fmt ="{:.4f}")
        else :
            year_groups =group_by_academic_year (courses_ref )
            year_groups_main =group_by_academic_year (self .courses )if comparing else {}

            for year in sorted (year_groups .keys ()):
                upper_sem_idx =2 *year -1 
                year_color =SEM_COLORS [(max (1 ,upper_sem_idx )-1 )%len (SEM_COLORS )]
                ybody =self ._stat_card (
                self .stats_scroll .inner ,
                f"第{year }学年",
                header_fg =year_color ,
                header_font =header_big 
                )
                cs =year_groups [year ]

                y_credits =credits_sum_unique (cs ,wc_view )
                y_avg_score ,y_avg_gpa =compute_metrics (cs ,wc_view ,weighted =False )
                y_w_score ,y_w_gpa =compute_metrics (cs ,wc_view ,weighted =True )
                y_gpa_43 =compute_gpa_43 (cs ,wc_view )

                if comparing and (year in year_groups_main ):
                    cs0 =year_groups_main [year ]
                    b_credits =credits_sum_unique (cs0 ,wc_main )
                    b_avg_score ,b_avg_gpa =compute_metrics (cs0 ,wc_main ,weighted =False )
                    b_w_score ,b_w_gpa =compute_metrics (cs0 ,wc_main ,weighted =True )
                    b_gpa_43 =compute_gpa_43 (cs0 ,wc_main )
                else :
                    b_credits =b_avg_score =b_avg_gpa =b_w_score =b_w_gpa =b_gpa_43 =None 

                _stat_row_delta (ybody ,"修读学分",float (y_credits ),b_credits ,fmt ="{:.1f}",bold =True )
                _stat_row_delta (ybody ,"百分制均绩",float (y_avg_score ),b_avg_score ,fmt ="{:.4f}")
                _stat_row_delta (ybody ,"五级制均绩",float (y_avg_gpa ),b_avg_gpa ,fmt ="{:.4f}")
                _stat_row_delta (ybody ,"加权百分制均绩",float (y_w_score ),b_w_score ,fmt ="{:.4f}")
                _stat_row_delta (ybody ,"加权五级制均绩",float (y_w_gpa ),b_w_gpa ,fmt ="{:.4f}")
                _stat_row_delta (ybody ,"4.3分制均绩",float (y_gpa_43 ),b_gpa_43 ,fmt ="{:.4f}")

                
        try :
            ana =self ._stat_card (self .stats_scroll .inner ,"趋势 / 分布 / 课程贡献",header_fg =COLOR_TEXT ,header_font =header_big )

            stat_courses =_stat_courses_for_analysis (courses_ref ,wc )

            
            sem_groups =group_by_semester (courses_ref )
            sem_x =[]
            gpa_unw =[]
            gpa_w =[]
            score_unw =[]
            score_w =[]
            for sem_idx in sorted (sem_groups .keys ()):
                cs =sem_groups [sem_idx ]
                a_score ,a_gpa =compute_metrics (cs ,wc ,weighted =False )
                w_score2 ,w_gpa2 =compute_metrics (cs ,wc ,weighted =True )
                sem_x .append (int (sem_idx ))
                score_unw .append (float (a_score ))
                gpa_unw .append (float (a_gpa ))
                score_w .append (float (w_score2 ))
                gpa_w .append (float (w_gpa2 ))

            tk .Label (ana ,text ="GPA 学期趋势（不加权 vs 加权）",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 ,"bold")).grid (row =0 ,column =0 ,sticky ="w")
            c1 =tk .Canvas (ana ,width =340 ,height =120 ,bg =COLOR_CARD ,highlightthickness =1 ,highlightbackground =COLOR_BORDER )
            c1 .grid (row =1 ,column =0 ,sticky ="we",pady =(6 ,10 ))
            c1 .update_idletasks ()
            draw_dual_line_chart (
            c1 ,
            sem_x ,
            gpa_unw ,
            gpa_w ,
            title ="GPA（不加权 vs 加权）",
            label_a ="不加权",
            label_b ="加权"
            )

            tk .Label (ana ,text ="百分制 学期趋势（不加权 vs 加权）",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 ,"bold")).grid (row =2 ,column =0 ,sticky ="w")
            c2 =tk .Canvas (ana ,width =340 ,height =120 ,bg =COLOR_CARD ,highlightthickness =1 ,highlightbackground =COLOR_BORDER )
            c2 .grid (row =3 ,column =0 ,sticky ="we",pady =(6 ,10 ))
            c2 .update_idletasks ()
            draw_dual_line_chart (
            c2 ,
            sem_x ,
            score_unw ,
            score_w ,
            title ="百分制（不加权 vs 加权）",
            label_a ="不加权",
            label_b ="加权"
            )

            
            scores =[convert_grade (c .score_text )[0 ]for c in stat_courses ]
            bins =_score_bins (scores )
            tk .Label (ana ,text ="分数段分布",bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,font =("Microsoft YaHei UI",9 ,"bold")).grid (row =4 ,column =0 ,sticky ="w")
            c3 =tk .Canvas (ana ,width =340 ,height =120 ,bg =COLOR_CARD ,highlightthickness =1 ,highlightbackground =COLOR_BORDER )
            c3 .grid (row =5 ,column =0 ,sticky ="we",pady =(6 ,10 ))
            c3 .update_idletasks ()
            draw_bar_chart (c3 ,bins ,title ="门数")

            
            
            
            
            N =5 
            base_gpa_unw =compute_metrics (self .view_courses ,wc ,weighted =False )[1 ]
            base_gpa_w =compute_metrics (self .view_courses ,wc ,weighted =True )[1 ]

            def _delta_color (d :float )->str :
                if d <-1e-9 :
                    return COLOR_DELTA_BAD 
                if d >1e-9 :
                    return COLOR_DELTA_GOOD 
                return COLOR_SUBTEXT 

            def _render_top_list (
            parent ,
            start_row :int ,
            title :str ,
            lst :List [Tuple [Course ,float ]],
            *,
            delta_label :str ="ΔGPA",
            wrap :int =250 
            )->int :
                tk .Label (
                parent ,text =title ,
                bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,
                font =("Microsoft YaHei UI",9 ,"bold")
                ).grid (row =start_row ,column =0 ,sticky ="w")

                box =tk .Frame (parent ,bg =COLOR_CARD )
                box .grid (row =start_row +1 ,column =0 ,sticky ="we",pady =(4 ,10 ))
                box .grid_columnconfigure (0 ,weight =1 )

                if not lst :
                    tk .Label (
                    box ,text ="（无）",
                    bg =COLOR_CARD ,fg =COLOR_SUBTEXT ,
                    anchor ="w",justify ="left"
                    ).grid (row =0 ,column =0 ,sticky ="w")
                    return start_row +2 

                for i ,(c ,d )in enumerate (lst ):
                    line =tk .Frame (box ,bg =COLOR_CARD )
                    line .grid (row =i ,column =0 ,sticky ="we",pady =2 )
                    line .grid_columnconfigure (0 ,weight =1 )

                    tk .Label (
                    line ,
                    text =f"{c .name }｜{c .semester }",
                    bg =COLOR_CARD ,
                    fg =COLOR_TEXT ,
                    anchor ="w",
                    justify ="left",
                    wraplength =wrap 
                    ).grid (row =0 ,column =0 ,sticky ="w")

                    tk .Label (
                    line ,
                    text =f"{delta_label } {float (d ):+.4f}",
                    bg =COLOR_CARD ,
                    fg =_delta_color (float (d )),
                    anchor ="e",
                    justify ="right",
                    font =("Microsoft YaHei UI",10 ,"bold")
                    ).grid (row =0 ,column =1 ,sticky ="e",padx =(10 ,0 ))

                return start_row +2 

            def _course_contrib (weighted :bool )->Tuple [List [Tuple [Course ,float ]],List [Tuple [Course ,float ]]]:
                base =base_gpa_w if weighted else base_gpa_unw 
                deltas :List [Tuple [Course ,float ]]=[]

                stat_list =_stat_courses_for_analysis (self .view_courses ,wc )
                for i ,c in enumerate (stat_list ):
                    other =stat_list [:i ]+stat_list [i +1 :]
                    gpa_without =compute_metrics (other ,wc ,weighted =weighted )[1 ]
                    delta =float (base -gpa_without )
                    deltas .append ((c ,delta ))

                    
                down =sorted ([x for x in deltas if x [1 ]<-1e-9 ],key =lambda t :t [1 ])[:N ]
                
                up =sorted ([x for x in deltas if x [1 ]>1e-9 ],key =lambda t :t [1 ],reverse =True )[:N ]
                return down ,up 

            down_unw ,up_unw =_course_contrib (False )
            down_w ,up_w =_course_contrib (True )

            r =6 
            r =_render_top_list (ana ,r ,"不加权：拉低均绩 Top N（移除后 GPA 上升）",down_unw )
            r =_render_top_list (ana ,r ,"不加权：拉高均绩 Top N（移除后 GPA 下降）",up_unw )
            r =_render_top_list (ana ,r ,"加权：拉低均绩 Top N（移除后 GPA 上升）",down_w )
            r =_render_top_list (ana ,r ,"加权：拉高均绩 Top N（移除后 GPA 下降）",up_w )

            
            def _gpa43_of_list (lst :List [Course ])->float :
                total_credits =0.0 
                sum_gpa =0.0 
                for cc in lst :
                    _s ,g43 =convert_grade_43 (cc .score_text )
                    cr =float (cc .credits )
                    sum_gpa +=g43 *cr 
                    total_credits +=cr 
                if total_credits <=1e-9 :
                    return 0.0 
                return round (sum_gpa /total_credits ,4 )

            stat_list43 =_stat_courses_for_analysis (courses_ref ,wc )
            base_gpa43 =_gpa43_of_list (stat_list43 )

            deltas43 :List [Tuple [Course ,float ]]=[]
            for i ,c in enumerate (stat_list43 ):
                other =stat_list43 [:i ]+stat_list43 [i +1 :]
                gpa43_without =_gpa43_of_list (other )
                delta43 =float (base_gpa43 -gpa43_without )
                deltas43 .append ((c ,delta43 ))

            down_43 =sorted ([x for x in deltas43 if x [1 ]<-1e-9 ],key =lambda t :t [1 ])[:N ]
            up_43 =sorted ([x for x in deltas43 if x [1 ]>1e-9 ],key =lambda t :t [1 ],reverse =True )[:N ]

            r =_render_top_list (
            ana ,
            r ,
            "4.3分制：拉低均绩 Top N（移除后 GPA43 上升）",
            down_43 ,
            delta_label ="ΔGPA43",
            wrap =250 
            )
            r =_render_top_list (
            ana ,
            r ,
            "4.3分制：拉高均绩 Top N（移除后 GPA43 下降）",
            up_43 ,
            delta_label ="ΔGPA43",
            wrap =250 
            )

            ana .grid_columnconfigure (0 ,weight =1 )

        except Exception :
            pass 


            
    def _sync_click (self ):
        if self ._fetch_inflight :
            return 
        if not messagebox .askyesno ("确认同步","将重新从教务网拉取成绩并重建所有卡片。\n\n确认继续？"):
            return 
        self ._log (f"{now_str ()}：开始同步教务网…")
        self ._fetch_inflight =True 

        def worker ():
            raw ,ok ,msg ,meta =fetch_data (self .username ,self .password )
            self .net_q .put ({"type":"sync_result","ok":ok ,"msg":msg ,"meta":meta ,"raw":raw })

        threading .Thread (target =worker ,daemon =True ).start ()

    def _reset_type_click (self ):
        if not messagebox .askyesno ("确认重置","将按教务网主修/非主修结果覆盖你的课程类型选择（包括专业核心也会被重置）。\n\n确认继续？"):
            return 
        self .config_store .clear_overrides (self .username )
        for c in self .courses :
            c .course_type =TYPE_MAJOR if c .source_major_flag else TYPE_NONMAJOR 
        self ._refresh_cards ()
        self ._render_stats ()
        self ._log (f"{now_str ()}：已重置课程类型（按教务网默认）。")


        
    def _start_polling (self ):
        if self .polling :
            return 
        try :
            interval =int (self .var_interval .get ().strip ())
        except Exception :
            messagebox .showerror ("参数错误","请输入有效的整数秒数。")
            return 
        if interval <5 :
            messagebox .showerror ("参数错误","查询频率必须 ≥ 5 秒。")
            return 

        self .poll_interval_sec =interval 
        self .polling =True 
        self .btn_start .configure (state ="disabled")
        self .btn_stop .configure (state ="normal")
        self ._log (f"{now_str ()}：已开始自动查询，频率 {interval }s。")
        self .after (0 ,self ._poll_once )

    def _stop_polling (self ):
        self .polling =False 
        self .btn_start .configure (state ="normal")
        self .btn_stop .configure (state ="disabled")
        self ._log (f"{now_str ()}：已停止自动查询。")

    def _poll_once (self ):
        if not self .polling :
            return 
        if self ._fetch_inflight :
            self .after (self .poll_interval_sec *1000 ,self ._poll_once )
            return 

        self ._fetch_inflight =True 
        self ._log (f"{now_str ()}：开始查询…")

        def worker ():
            raw ,ok ,msg ,meta =fetch_data (self .username ,self .password )
            self .net_q .put ({"type":"poll_result","ok":ok ,"msg":msg ,"meta":meta ,"raw":raw })

        threading .Thread (target =worker ,daemon =True ).start ()


        
    def _process_net_queue (self ):
        try :
            while True :
                item =self .net_q .get_nowait ()
                self ._handle_net_result (item )
        except Empty :
            pass 
        finally :
            self .after (120 ,self ._process_net_queue )

    def _handle_net_result (self ,item :dict ):
        t =item .get ("type")

        if t =="login_result":
            ok =bool (item .get ("ok"))
            msg =item .get ("msg","")
            meta =item .get ("meta",{})or {}
            self .last_request_elapsed =float (meta .get ("elapsed",0.0 )or 0.0 )

            if not ok :
                self .btn_login .configure (state ="normal")
                self .lbl_status .configure (text =f"登录失败：{msg }",fg =COLOR_DANGER )
                return 

            self .username =item .get ("username")
            self .password =item .get ("password")

            remember =bool (item .get ("remember",False ))
            if remember :
                self .config_store .set_saved_login (True ,self .username ,self .password )

            raw =item .get ("raw",[])or []
            self .courses =self ._raw_to_courses (raw ,keep_user_override =True )
            self .course_by_key ={course_key (c .name ,c .credits ,c .semester ,c .course_code ):c for c in self .courses }

            
            self .view_courses =self .courses 
            self ._view_weights =None 

            self ._snapshot_courses ()

            self .last_success_sync_time =now_str ()

            self .login_frame .destroy ()
            self ._build_main ()
            if hasattr (self ,"lbl_sync_meta"):
                self .lbl_sync_meta .configure (
                text =f"最近成功同步：{self .last_success_sync_time }｜上次请求耗时：{self .last_request_elapsed :.3f}s"
                )
            self ._log (f"{now_str ()}：登录成功。{msg }（耗时 {self .last_request_elapsed :.3f}s）")

        elif t =="sync_result":
            ok =bool (item .get ("ok"))
            msg =item .get ("msg","")
            raw =item .get ("raw",[])or []
            meta =item .get ("meta",{})or {}
            self .last_request_elapsed =float (meta .get ("elapsed",0.0 )or 0.0 )
            self ._fetch_inflight =False 

            if not ok :
                et =str (meta .get ("error_type","")or "")
                title ="同步失败"
                if et =="timeout":
                    title ="网络超时"
                elif et =="auth":
                    title ="认证失败"
                elif et =="api":
                    title ="接口变更/解析失败"
                messagebox .showerror (title ,msg )
                self ._log (f"{now_str ()}：同步失败：{msg }（耗时 {self .last_request_elapsed :.3f}s）")
                return 

            old_keys =set (self .course_by_key .keys ())

            self .courses =self ._raw_to_courses (raw ,keep_user_override =True )
            self .course_by_key ={course_key (c .name ,c .credits ,c .semester ,c .course_code ):c for c in self .courses }

            
            if not (self ._sim_enabled and (getattr (self ,"var_sim_profile",tk .StringVar (value ="主配置")).get ()!="主配置")):
                self .view_courses =self .courses 
                self ._view_weights =None 
            self ._snapshot_courses ()

            new_keys =set (self .course_by_key .keys ())
            added =sorted (list (new_keys -old_keys ))
            if added :
                self .new_course_pending_keys .update (added )

            self .last_success_sync_time =now_str ()
            if hasattr (self ,"lbl_sync_meta"):
                self .lbl_sync_meta .configure (
                text =f"最近成功同步：{self .last_success_sync_time }｜上次请求耗时：{self .last_request_elapsed :.3f}s"
                )

            self ._refresh_filter_options ()
            self ._render_stats ()
            self ._refresh_cards ()
            self ._log (f"{now_str ()}：同步完成。{msg }（耗时 {self .last_request_elapsed :.3f}s）")

            if added :
                self ._notify_new_grades (added )

        elif t =="poll_result":
            ok =bool (item .get ("ok"))
            msg =item .get ("msg","")
            raw =item .get ("raw",[])or []
            meta =item .get ("meta",{})or {}
            self .last_request_elapsed =float (meta .get ("elapsed",0.0 )or 0.0 )
            self ._fetch_inflight =False 

            if not ok :
                et =str (meta .get ("error_type","")or "")
                if et =="timeout":
                    self ._log (f"{now_str ()}：查询失败（网络超时）：{msg }（耗时 {self .last_request_elapsed :.3f}s）")
                elif et =="auth":
                    self ._log (f"{now_str ()}：查询失败（认证失败）：{msg }（耗时 {self .last_request_elapsed :.3f}s）")
                elif et =="api":
                    self ._log (f"{now_str ()}：查询失败（接口变更/解析失败）：{msg }（耗时 {self .last_request_elapsed :.3f}s）")
                else :
                    self ._log (f"{now_str ()}：查询失败：{msg }（耗时 {self .last_request_elapsed :.3f}s）")

                if self .polling :
                    self .after (self .poll_interval_sec *1000 ,self ._poll_once )
                return 

            self .last_success_sync_time =now_str ()
            if hasattr (self ,"lbl_sync_meta"):
                self .lbl_sync_meta .configure (
                text =f"最近成功同步：{self .last_success_sync_time }｜上次请求耗时：{self .last_request_elapsed :.3f}s"
                )

            new_courses_all =self ._raw_to_courses (raw ,keep_user_override =True )
            new_map ={course_key (c .name ,c .credits ,c .semester ,c .course_code ):c for c in new_courses_all }

            old_keys =set (self .course_by_key .keys ())
            new_keys =set (new_map .keys ())
            added =sorted (list (new_keys -old_keys ))

            if added :
                self .new_course_pending_keys .update (added )

                added_names =[new_map [k ].name for k in added if k in new_map ]
                self ._log (f"{now_str ()}：发现新成绩：{', '.join (added_names )}（耗时 {self .last_request_elapsed :.3f}s）")

                self .courses =new_courses_all 
                self .course_by_key =new_map 

                self ._snapshot_courses ()
                self ._refresh_filter_options ()
                self ._render_stats ()
                self ._refresh_cards ()

                self ._notify_new_grades (added )
            else :
                self ._log (f"{now_str ()}：无新成绩。（耗时 {self .last_request_elapsed :.3f}s）")

            if self .polling :
                self .after (self .poll_interval_sec *1000 ,self ._poll_once )

        else :
            self ._fetch_inflight =False 

    def _notify_new_grades (self ,keys :List [str ]):
        title ="新成绩通知"
        lines =[]
        for k in keys :
            c =self .course_by_key .get (k )
            if not c :
                continue 
            if is_binary_score (c .score_text ):
                lines .append (f"{c .name }｜{c .semester }｜成绩 {c .score_text }｜GPA 不计")
            else :
                score ,gpa =convert_grade (c .score_text )
                lines .append (f"{c .name }｜{c .semester }｜分数 {score :.1f}｜GPA {gpa :.1f}")

        message ="新增课程出分：\n"+("\n".join (lines )if lines else "（详情见列表）")

        if PLYER_AVAILABLE :
            try :
                notification .notify (title =title ,message =message ,timeout =10 )
                return 
            except Exception :
                pass 
        messagebox .showinfo (title ,message )

    def _log (self ,text :str ):
        if not hasattr (self ,"txt_log"):
            return 
        self .txt_log .insert ("end",text +"\n")
        self .txt_log .see ("end")
        try :
            lines =int (self .txt_log .index ("end-1c").split (".")[0 ])
            if lines >500 :
                self .txt_log .delete ("1.0","120.0")
        except Exception :
            pass 

            
if __name__ =="__main__":
    ensure_dir (OUTPUT_DIR )
    ensure_dir (SNAPSHOT_DIR )
    app =GradeApp ()
    app .mainloop ()