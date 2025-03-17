const

  NODE_NUM : 2;

type

  NODE : scalarset(NODE_NUM);

  CACHE_STATE : enum {cache_i, cache_s, cache_e};

  NODE_CMD : enum {node_none, node_get, node_getx};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
  end;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : NODE;
    HomeHeadPtr : boolean;
    ShrVld : boolean;
    ShrSet : array [NODE] of boolean;
    HomeShrSet : boolean;
    InvSet : array [NODE] of boolean;
    HomeInvSet : boolean;
  end;

  UNI_CMD : enum {uni_none, uni_get, uni_getx, uni_put, uni_putx, uni_nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  INV_CMD : enum {inv_none, inv_inv, inv_invack};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {rp_none, rp_replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {wb_none, wb_wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  SHWB_CMD : enum {shwb_none, shwb_shwb, shwb_fack};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  NAKC_CMD : enum {nakc_none, nakc_nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
    Proc : array [NODE] of NODE_STATE;
    HomeProc : NODE_STATE;
    Dir : DIR_STATE;
    UniMsg : array [NODE] of UNI_MSG;
    HomeUniMsg : UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    HomeInvMsg : INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    HomeRpMsg : RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
  end;

var

  sta : STATE;


ruleset h : NODE do
startstate "Init"
  sta.Dir.Pending := false;
  sta.Dir.Local := false;
  sta.Dir.Dirty := false;
  sta.Dir.HeadVld := false;
  sta.Dir.HeadPtr := h;
  sta.Dir.HomeHeadPtr := true;
  sta.Dir.ShrVld := false;
  sta.WbMsg.Cmd := wb_none;
  sta.WbMsg.Proc := h;
  sta.WbMsg.HomeProc := true;
  sta.ShWbMsg.Cmd := shwb_none;
  sta.ShWbMsg.Proc := h;
  sta.ShWbMsg.HomeProc := true;
  sta.NakcMsg.Cmd := nakc_none;
  for p : NODE do
    sta.Proc[p].ProcCmd := node_none;
    sta.Proc[p].InvMarked := false;
    sta.Proc[p].CacheState := cache_i;
    sta.Dir.ShrSet[p] := false;
    sta.Dir.InvSet[p] := false;
    sta.UniMsg[p].Cmd := uni_none;
    sta.UniMsg[p].Proc := h;
    sta.UniMsg[p].HomeProc := true;
    sta.InvMsg[p].Cmd := inv_none;
    sta.RpMsg[p].Cmd := rp_none;
  end;
  sta.HomeProc.ProcCmd := node_none;
  sta.HomeProc.InvMarked := false;
  sta.HomeProc.CacheState := cache_i;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeUniMsg.Cmd := uni_none;
  sta.HomeUniMsg.Proc := h;
  sta.HomeUniMsg.HomeProc := true;
  sta.HomeInvMsg.Cmd := inv_none;
  sta.HomeRpMsg.Cmd := rp_none;
endstartstate;
endruleset;


ruleset src : NODE do
rule "PI_Remote_Get"
  sta.Proc[src].ProcCmd = node_none &
  sta.Proc[src].CacheState = cache_i
==>
begin
  sta.Proc[src].ProcCmd := node_get;
  sta.UniMsg[src].Cmd := uni_get;
  sta.UniMsg[src].HomeProc := true;
endrule;
endruleset;

rule "PI_Local_Get_Get"
  sta.HomeProc.ProcCmd = node_none &
  sta.HomeProc.CacheState = cache_i &
  sta.Dir.Pending = false & sta.Dir.Dirty = true
==>
begin
  sta.HomeProc.ProcCmd := node_get;
  sta.Dir.Pending := true;
  sta.HomeUniMsg.Cmd := uni_get;
  sta.HomeUniMsg.Proc := sta.Dir.HeadPtr;
  sta.HomeUniMsg.HomeProc := sta.Dir.HomeHeadPtr;
endrule;

rule "PI_Local_Get_Put"
  sta.HomeProc.ProcCmd = node_none &
  sta.HomeProc.CacheState = cache_i &
  sta.Dir.Pending = false & sta.Dir.Dirty = false
==>
begin
  sta.Dir.Local := true;
  sta.HomeProc.ProcCmd := node_none;
  if (sta.HomeProc.InvMarked = true) then
    sta.HomeProc.InvMarked := false;
    sta.HomeProc.CacheState := cache_i;
  else
    sta.HomeProc.CacheState := cache_s;
  end;
endrule;

ruleset src : NODE do
rule "PI_Remote_GetX"
  sta.Proc[src].ProcCmd = node_none &
  sta.Proc[src].CacheState = cache_i
==>
begin
  sta.Proc[src].ProcCmd := node_getx;
  sta.UniMsg[src].Cmd := uni_getx;
  sta.UniMsg[src].HomeProc := true;
endrule;
endruleset;

rule "PI_Local_GetX_GetX"
  sta.HomeProc.ProcCmd = node_none &
  ( sta.HomeProc.CacheState = cache_i |
    sta.HomeProc.CacheState = cache_s ) &
  sta.Dir.Pending = false & sta.Dir.Dirty = true
==>
begin
  sta.HomeProc.ProcCmd := node_getx;
  sta.Dir.Pending := true;
  sta.HomeUniMsg.Cmd := uni_getx;
  sta.HomeUniMsg.Proc := sta.Dir.HeadPtr;
  sta.HomeUniMsg.HomeProc := sta.Dir.HomeHeadPtr;
endrule;

rule "PI_Local_GetX_PutX_HeadVld"
  sta.HomeProc.ProcCmd = node_none &
  ( sta.HomeProc.CacheState = cache_i |
    sta.HomeProc.CacheState = cache_s ) &
  sta.Dir.Pending = false & sta.Dir.Dirty = false & sta.Dir.HeadVld = true
==>
begin
  sta.Dir.Local := true;
  sta.Dir.Dirty := true;

  sta.Dir.Pending := true;
  sta.Dir.HeadVld := false;
  sta.Dir.ShrVld := false;

  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;

  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;

  sta.HomeProc.ProcCmd := node_none;
  sta.HomeProc.InvMarked := false;
  sta.HomeProc.CacheState := cache_e;
endrule;

rule "PI_Local_GetX_PutX"
  sta.HomeProc.ProcCmd = node_none &
  ( sta.HomeProc.CacheState = cache_i |
    sta.HomeProc.CacheState = cache_s ) &
  sta.Dir.Pending = false & sta.Dir.Dirty = false & sta.Dir.HeadVld = false
==>
begin
  sta.Dir.Local := true;
  sta.Dir.Dirty := true;

  sta.HomeProc.ProcCmd := node_none;
  sta.HomeProc.InvMarked := false;
  sta.HomeProc.CacheState := cache_e;
endrule;

ruleset dst : NODE do
rule "PI_Remote_PutX"
  sta.Proc[dst].ProcCmd = node_none &
  sta.Proc[dst].CacheState = cache_e
==>
begin
  sta.Proc[dst].CacheState := cache_i;
  sta.WbMsg.Cmd := wb_wb;
  sta.WbMsg.Proc := dst;
  sta.WbMsg.HomeProc := false;
endrule;
endruleset;

rule "PI_Local_PutX"
  sta.HomeProc.ProcCmd = node_none &
  sta.HomeProc.CacheState = cache_e
==>
begin
  if (sta.Dir.Pending = true) then
    sta.HomeProc.CacheState := cache_i;
    sta.Dir.Dirty := false;
  else
    sta.HomeProc.CacheState := cache_i;
    sta.Dir.Local := false;
    sta.Dir.Dirty := false;
  end;
endrule;

ruleset src : NODE do
rule "PI_Remote_Replace"
  sta.Proc[src].ProcCmd = node_none &
  sta.Proc[src].CacheState = cache_s
==>
begin
  sta.Proc[src].CacheState := cache_i;
  sta.RpMsg[src].Cmd := rp_replace;
endrule;
endruleset;

rule "PI_Local_Replace"
  sta.HomeProc.ProcCmd = node_none &
  sta.HomeProc.CacheState = cache_s
==>
begin
  sta.Dir.Local := false;
  sta.HomeProc.CacheState := cache_i;
endrule;

ruleset dst : NODE do
rule "NI_Nak"
  sta.UniMsg[dst].Cmd = uni_nak
==>
begin
  sta.UniMsg[dst].Cmd := uni_none;
  sta.Proc[dst].ProcCmd := node_none;
  sta.Proc[dst].InvMarked := false;
endrule;
endruleset;

rule "NI_Nak_Home"
  sta.HomeUniMsg.Cmd = uni_nak
==>
begin
  sta.HomeUniMsg.Cmd := uni_none;
  sta.HomeProc.ProcCmd := node_none;
  sta.HomeProc.InvMarked := false;
endrule;

rule "NI_Nak_Clear"
  sta.NakcMsg.Cmd = nakc_nakc
==>
begin
  sta.NakcMsg.Cmd := nakc_none;
  sta.Dir.Pending := false;
endrule;

ruleset src : NODE do
rule "NI_Local_Get_Nak"
  sta.UniMsg[src].Cmd = uni_get &
  sta.UniMsg[src].HomeProc = true &
  sta.RpMsg[src].Cmd != rp_replace &
  ( sta.Dir.Pending = true |
    sta.Dir.Dirty = true & sta.Dir.Local = true & sta.HomeProc.CacheState != cache_e |
    sta.Dir.Dirty = true & sta.Dir.Local = false & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false)
==>
begin
  sta.UniMsg[src].Cmd := uni_nak;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Get"
  sta.UniMsg[src].Cmd = uni_get &
  sta.UniMsg[src].HomeProc = true &
  sta.RpMsg[src].Cmd != rp_replace &
  sta.Dir.Pending = false & sta.Dir.Dirty = true & sta.Dir.Local = false &
  (sta.Dir.HeadPtr != src | sta.Dir.HomeHeadPtr = true)
==>
begin
  sta.Dir.Pending := true;
  sta.UniMsg[src].Cmd := uni_get;
  sta.UniMsg[src].Proc := sta.Dir.HeadPtr;
  sta.UniMsg[src].HomeProc := sta.Dir.HomeHeadPtr;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Put_Head"
  sta.UniMsg[src].Cmd = uni_get &
  sta.UniMsg[src].HomeProc = true &
  sta.RpMsg[src].Cmd != rp_replace &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true
==>
begin
  sta.Dir.ShrVld := true;
  sta.Dir.ShrSet[src] := true;
  for p : NODE do
    if (p = src)  then
      sta.Dir.InvSet[p] := true;
    else
      sta.Dir.InvSet[p] := sta.Dir.ShrSet[p];
    end;
  end;
  sta.Dir.HomeInvSet := sta.Dir.HomeShrSet;
  sta.UniMsg[src].Cmd := uni_put;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Put"
  sta.UniMsg[src].Cmd = uni_get &
  sta.UniMsg[src].HomeProc = true &
  sta.RpMsg[src].Cmd != rp_replace &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = false
==>
begin
    sta.Dir.HeadVld := true;
    sta.Dir.HeadPtr := src;
    sta.Dir.HomeHeadPtr := false;
    sta.UniMsg[src].Cmd := uni_put;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Put_Dirty"
  sta.UniMsg[src].Cmd = uni_get &
  sta.UniMsg[src].HomeProc = true &
  sta.RpMsg[src].Cmd != rp_replace &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = true & sta.Dir.Local = true & sta.HomeProc.CacheState = cache_e
==>
begin
  sta.Dir.Dirty := false;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.HomeProc.CacheState := cache_s;
  sta.UniMsg[src].Cmd := uni_put;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Nak"
  src != dst &
  sta.UniMsg[src].Cmd = uni_get &
  sta.UniMsg[src].Proc = dst & sta.UniMsg[src].HomeProc = false &
  sta.Proc[dst].CacheState != cache_e
==>
begin
  sta.UniMsg[src].Cmd := uni_nak;
  sta.NakcMsg.Cmd := nakc_nakc;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Remote_Get_Nak_Home"
  sta.HomeUniMsg.Cmd = uni_get &
  sta.HomeUniMsg.Proc = dst & sta.HomeUniMsg.HomeProc = false &
  sta.Proc[dst].CacheState != cache_e
==>
begin
  sta.HomeUniMsg.Cmd := uni_nak;
  sta.NakcMsg.Cmd := nakc_nakc;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Put"
  src != dst &
  sta.UniMsg[src].Cmd = uni_get &
  sta.UniMsg[src].Proc = dst & sta.UniMsg[src].HomeProc = false &
  sta.Proc[dst].CacheState = cache_e
==>
begin
  sta.Proc[dst].CacheState := cache_s;
  sta.UniMsg[src].Cmd := uni_put;
  sta.ShWbMsg.Cmd := shwb_shwb;
  sta.ShWbMsg.Proc := src;
  sta.ShWbMsg.HomeProc := false;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Remote_Get_Put_Home"
  sta.HomeUniMsg.Cmd = uni_get &
  sta.HomeUniMsg.Proc = dst & sta.HomeUniMsg.HomeProc = false &
  sta.Proc[dst].CacheState = cache_e
==>
begin
  sta.Proc[dst].CacheState := cache_s;
  sta.HomeUniMsg.Cmd := uni_put;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_Nak"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  ( sta.Dir.Pending = true |
    sta.Dir.Dirty = true & sta.Dir.Local = true & sta.HomeProc.CacheState != cache_e |
    sta.Dir.Dirty = true & sta.Dir.Local = false & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false)
==>
begin
  sta.UniMsg[src].Cmd := uni_nak;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_GetX"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false & sta.Dir.Dirty = true & sta.Dir.Local = false &
  (sta.Dir.HeadPtr != src | sta.Dir.HomeHeadPtr = true)
==>
begin
  sta.Dir.Pending := true;
  sta.UniMsg[src].Cmd := uni_getx;
  sta.UniMsg[src].Proc := sta.Dir.HeadPtr;
  sta.UniMsg[src].HomeProc := sta.Dir.HomeHeadPtr;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_1"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = false & sta.Dir.Local = true & sta.HomeProc.ProcCmd = node_get
==>
begin
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    sta.Dir.InvSet[p] := false;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
  sta.HomeProc.InvMarked := true;
endrule;
endruleset;



ruleset src : NODE do
rule "NI_Local_GetX_PutX_2"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = false & sta.Dir.Local = true & sta.HomeProc.ProcCmd != node_get
==>
begin
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    sta.Dir.InvSet[p] := false;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_3"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = false & sta.Dir.Local = false
==>
begin
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    sta.Dir.InvSet[p] := false;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_4"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false & sta.Dir.HomeShrSet = false &
  forall p : NODE do p != src -> sta.Dir.ShrSet[p] = false end &
  sta.Dir.Local = true & sta.HomeProc.ProcCmd = node_get
==>
begin
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    sta.Dir.InvSet[p] := false;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
  sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_5"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false & sta.Dir.HomeShrSet = false &
  forall p : NODE do p != src -> sta.Dir.ShrSet[p] = false end &
  sta.Dir.Local = true & sta.HomeProc.ProcCmd != node_get
==>
begin
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    sta.Dir.InvSet[p] := false;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_6"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false & sta.Dir.HomeShrSet = false &
  forall p : NODE do p != src -> sta.Dir.ShrSet[p] = false end &
  sta.Dir.Local = false
==>
begin
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    sta.Dir.InvSet[p] := false;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_7"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & (sta.Dir.HeadPtr != src | sta.Dir.HomeHeadPtr = true) &
  sta.Dir.Local = true & sta.HomeProc.ProcCmd != node_get
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_7_NODE_Get"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & (sta.Dir.HeadPtr != src | sta.Dir.HomeHeadPtr = true) &
  sta.Dir.Local = true & sta.HomeProc.ProcCmd = node_get
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
  sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_8_Home"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false &
  sta.Dir.HomeShrSet = true &
  sta.Dir.Local = true & sta.HomeProc.ProcCmd != node_get
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_8_Home_NODE_Get"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false &
  sta.Dir.HomeShrSet = true &
  sta.Dir.Local = true & sta.HomeProc.ProcCmd = node_get
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
  sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE; pp : NODE do
rule "NI_Local_GetX_PutX_8"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false &
  sta.Dir.ShrSet[pp] = true &
  sta.Dir.Local = true & sta.HomeProc.ProcCmd != node_get
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
endrule;
endruleset;

ruleset src : NODE; pp : NODE do
rule "NI_Local_GetX_PutX_8_NODE_Get"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false &
  sta.Dir.ShrSet[pp] = true &
  sta.Dir.Local = true & sta.HomeProc.ProcCmd = node_get
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
  sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_9"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & (sta.Dir.HeadPtr != src | sta.Dir.HomeHeadPtr = true) &
  sta.Dir.Local = false
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;

  sta.UniMsg[src].Cmd := uni_putx;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_10_Home"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false &
  sta.Dir.HomeShrSet = true &
  sta.Dir.Local = false
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;

  sta.UniMsg[src].Cmd := uni_putx;
endrule;
endruleset;

ruleset src : NODE; pp : NODE do
rule "NI_Local_GetX_PutX_10"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = false & sta.Dir.HeadVld = true & sta.Dir.HeadPtr = src & sta.Dir.HomeHeadPtr = false &
  sta.Dir.ShrSet[pp] = true &
  sta.Dir.Local = false
==>
begin
  sta.Dir.Pending := true;
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    if ( p != src &
         ( sta.Dir.ShrVld = true & sta.Dir.ShrSet[p] = true |
           sta.Dir.HeadVld = true & sta.Dir.HeadPtr = p & sta.Dir.HomeHeadPtr = false) ) then
      sta.Dir.InvSet[p] := true;
      sta.InvMsg[p].Cmd := inv_inv;
    else
      sta.Dir.InvSet[p] := false;
      sta.InvMsg[p].Cmd := inv_none;
    end;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.HomeInvMsg.Cmd := inv_none;

  sta.UniMsg[src].Cmd := uni_putx;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX_11"
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].HomeProc = true &
  sta.Dir.Pending = false &
  sta.Dir.Dirty = true & sta.Dir.Local = true & sta.HomeProc.CacheState = cache_e
==>
begin
  sta.Dir.Local := false;
  sta.Dir.Dirty := true;
  sta.Dir.HeadVld := true;
  sta.Dir.HeadPtr := src;
  sta.Dir.HomeHeadPtr := false;
  sta.Dir.ShrVld := false;
  for p : NODE do
    sta.Dir.ShrSet[p] := false;
    sta.Dir.InvSet[p] := false;
  end;
  sta.Dir.HomeShrSet := false;
  sta.Dir.HomeInvSet := false;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.HomeProc.CacheState := cache_i;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_Nak"
  src != dst &
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].Proc = dst & sta.UniMsg[src].HomeProc = false &
  sta.Proc[dst].CacheState != cache_e
==>
begin
  sta.UniMsg[src].Cmd := uni_nak;
  sta.NakcMsg.Cmd := nakc_nakc;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Remote_GetX_Nak_Home"
  sta.HomeUniMsg.Cmd = uni_getx &
  sta.HomeUniMsg.Proc = dst & sta.HomeUniMsg.HomeProc = false &
  sta.Proc[dst].CacheState != cache_e
==>
begin
  sta.HomeUniMsg.Cmd := uni_nak;
  sta.NakcMsg.Cmd := nakc_nakc;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_PutX"
  src != dst &
  sta.UniMsg[src].Cmd = uni_getx &
  sta.UniMsg[src].Proc = dst & sta.UniMsg[src].HomeProc = false &
  sta.Proc[dst].CacheState = cache_e
==>
begin
  sta.Proc[dst].CacheState := cache_i;
  sta.UniMsg[src].Cmd := uni_putx;
  sta.ShWbMsg.Cmd := shwb_fack;
  sta.ShWbMsg.Proc := src;
  sta.ShWbMsg.HomeProc := false;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Remote_GetX_PutX_Home"
  sta.HomeUniMsg.Cmd = uni_getx &
  sta.HomeUniMsg.Proc = dst & sta.HomeUniMsg.HomeProc = false &
  sta.Proc[dst].CacheState = cache_e
==>
begin
  sta.Proc[dst].CacheState := cache_i;
  sta.HomeUniMsg.Cmd := uni_putx;
endrule;
endruleset;

rule "NI_Local_Put"
  sta.HomeUniMsg.Cmd = uni_put
==>
begin
  sta.HomeUniMsg.Cmd := uni_none;
  sta.Dir.Pending := false;
  sta.Dir.Dirty := false;
  sta.Dir.Local := true;
  sta.HomeProc.ProcCmd := node_none;
  if (sta.HomeProc.InvMarked = true) then
    sta.HomeProc.InvMarked := false;
    sta.HomeProc.CacheState := cache_i;
  else
    sta.HomeProc.CacheState := cache_s;
  end;
endrule;

ruleset dst : NODE do
rule "NI_Remote_Put"
  sta.UniMsg[dst].Cmd = uni_put
==>
begin
  sta.UniMsg[dst].Cmd := uni_none;
  sta.Proc[dst].ProcCmd := node_none;
  if (sta.Proc[dst].InvMarked = true) then
    sta.Proc[dst].InvMarked := false;
    sta.Proc[dst].CacheState := cache_i;
  else
    sta.Proc[dst].CacheState := cache_s;
  end;
endrule;
endruleset;

rule "NI_Local_PutXAcksDone"
  sta.HomeUniMsg.Cmd = uni_putx
==>
begin
  sta.HomeUniMsg.Cmd := uni_none;
  sta.Dir.Pending := false;
  sta.Dir.Local := true;
  sta.Dir.HeadVld := false;
  sta.HomeProc.ProcCmd := node_none;
  sta.HomeProc.InvMarked := false;
  sta.HomeProc.CacheState := cache_e;
endrule;

ruleset dst : NODE do
rule "NI_Remote_PutX"
  sta.UniMsg[dst].Cmd = uni_putx &
  sta.Proc[dst].ProcCmd = node_getx
==>
begin
  sta.UniMsg[dst].Cmd := uni_none;
  sta.Proc[dst].ProcCmd := node_none;
  sta.Proc[dst].InvMarked := false;
  sta.Proc[dst].CacheState := cache_e;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Inv"
  sta.InvMsg[dst].Cmd = inv_inv
==>
begin
  sta.InvMsg[dst].Cmd := inv_invack;
  sta.Proc[dst].CacheState := cache_i;
  if (sta.Proc[dst].ProcCmd = node_get) then
    sta.Proc[dst].InvMarked := true;
  end;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck_exists_Home"
  sta.InvMsg[src].Cmd = inv_invack &
  sta.Dir.Pending = true & sta.Dir.InvSet[src] = true &
  sta.Dir.HomeInvSet = true
==>
begin
  sta.InvMsg[src].Cmd := inv_none;
  sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset src : NODE; pp : NODE do
rule "NI_InvAck_exists"
  sta.InvMsg[src].Cmd = inv_invack &
  sta.Dir.Pending = true & sta.Dir.InvSet[src] = true &
  (pp != src & sta.Dir.InvSet[pp] = true)
==>
begin
  sta.InvMsg[src].Cmd := inv_none;
  sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck_1"
  sta.InvMsg[src].Cmd = inv_invack &
  sta.Dir.Pending = true & sta.Dir.InvSet[src] = true &
  sta.Dir.Local = true & sta.Dir.Dirty = false &
  sta.Dir.HomeInvSet = false & forall p : NODE do p = src | sta.Dir.InvSet[p] = false end
==>
begin
  sta.InvMsg[src].Cmd := inv_none;
  sta.Dir.InvSet[src] := false;
  sta.Dir.Pending := false;
  sta.Dir.Local := false;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck_2"
  sta.InvMsg[src].Cmd = inv_invack &
  sta.Dir.Pending = true & sta.Dir.InvSet[src] = true &
  sta.Dir.Local = false &
  sta.Dir.HomeInvSet = false & forall p : NODE do p = src | sta.Dir.InvSet[p] = false end
==>
begin
  sta.InvMsg[src].Cmd := inv_none;
  sta.Dir.InvSet[src] := false;
  sta.Dir.Pending := false;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck_3"
  sta.InvMsg[src].Cmd = inv_invack &
  sta.Dir.Pending = true & sta.Dir.InvSet[src] = true &
  sta.Dir.Dirty = true &
  sta.Dir.HomeInvSet = false & forall p : NODE do p = src | sta.Dir.InvSet[p] = false end
==>
begin
  sta.InvMsg[src].Cmd := inv_none;
  sta.Dir.InvSet[src] := false;
  sta.Dir.Pending := false;
endrule;
endruleset;

rule "NI_Wb"
  sta.WbMsg.Cmd = wb_wb
==>
begin
  sta.WbMsg.Cmd := wb_none;
  sta.Dir.Dirty := false;
  sta.Dir.HeadVld := false;
endrule;

rule "NI_FAck"
  sta.ShWbMsg.Cmd = shwb_fack
==>
begin
  sta.ShWbMsg.Cmd := shwb_none;
  sta.Dir.Pending := false;
  if (sta.Dir.Dirty = true) then
    sta.Dir.HeadPtr := sta.ShWbMsg.Proc;
    sta.Dir.HomeHeadPtr := sta.ShWbMsg.HomeProc;
  end;
endrule;

rule "NI_ShWb"
  sta.ShWbMsg.Cmd = shwb_shwb
==>
begin
  sta.ShWbMsg.Cmd := shwb_none;
  sta.Dir.Pending := false;
  sta.Dir.Dirty := false;
  sta.Dir.ShrVld := true;
  for p : NODE do
    if (sta.ShWbMsg.Proc = p & sta.ShWbMsg.HomeProc = false) | sta.Dir.ShrSet[p] = true then
      sta.Dir.ShrSet[p] := true;
      sta.Dir.InvSet[p] := true;
    else
      sta.Dir.ShrSet[p] := false;
      sta.Dir.InvSet[p] := false;
    end;
  end;
  if (sta.ShWbMsg.HomeProc = true | sta.Dir.HomeShrSet = true) then
    sta.Dir.HomeShrSet := true;
    sta.Dir.HomeInvSet := true;
  else
    sta.Dir.HomeShrSet := false;
    sta.Dir.HomeInvSet := false;
  end;
endrule;

ruleset src : NODE do
rule "NI_Replace"
  sta.RpMsg[src].Cmd = rp_replace
==>
begin
  sta.RpMsg[src].Cmd := rp_none;
  if (sta.Dir.ShrVld = true) then
    sta.Dir.ShrSet[src] := false;
    sta.Dir.InvSet[src] := false;
  end;
endrule;
endruleset;

rule "NI_Replace_Home"
  sta.HomeRpMsg.Cmd = rp_replace
==>
begin
  sta.HomeRpMsg.Cmd := rp_none;
  if (sta.Dir.ShrVld = true) then
    sta.Dir.HomeShrSet := false;
    sta.Dir.HomeInvSet := false;
  end;
endrule;

