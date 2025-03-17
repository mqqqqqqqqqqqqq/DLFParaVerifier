const

  NODE_NUM : 2;

type

  NODE : scalarset(NODE_NUM);

  OTHER : enum {Other};

  CACHE_STATE : enum {i_em, s_em, e_em};

  CACHE : record
    State : CACHE_STATE;
  end;

  MSG_CMD1: enum {empty1_em, reqs_em, reqe_em};

  MSG_CMD2: enum {empty2_em, inv_em, gnts_em, gnte_em};

  MSG_CMD3: enum {empty3_em, invack_em};

  MSG1 : record
    Cmd : MSG_CMD1;
  end;

  MSG2 : record
    Cmd : MSG_CMD2;
  end;

  MSG3 : record
    Cmd : MSG_CMD3;
  end;

var

  cache : array [NODE] of CACHE;
  chan1 : array [NODE] of MSG1;
  chan2 : array [NODE] of MSG2;
  chan3 : array [NODE] of MSG3;
  invset : array [NODE] of boolean;
  shrset : array [NODE] of boolean;
  exgntd : boolean;
  curcmd : MSG_CMD1;

startstate "Init"
begin
  for i : NODE do
    chan1[i].Cmd := empty1_em;
    chan2[i].Cmd := empty2_em;
    chan3[i].Cmd := empty3_em;
    cache[i].State := i_em;
    invset[i] := false;
    shrset[i] := false;
  end;
  exgntd := false;
  curcmd := empty1_em;
endstartstate;

ruleset i : NODE do
rule "RecvGntE"
  chan2[i].Cmd = gnte_em
==>
begin
  cache[i].State := e_em;
  chan2[i].Cmd := empty2_em;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvGntS"
  chan2[i].Cmd = gnts_em
==>
begin
  cache[i].State := s_em;
  chan2[i].Cmd := empty2_em;
endrule;
endruleset;

ruleset i : NODE do
rule "SendGntE"
  curcmd = reqe_em &
  chan2[i].Cmd = empty2_em &
  exgntd = false &
  forall j : NODE do
    shrset[j] = false
  end
==>
begin
  chan2[i].Cmd := gnte_em;
  shrset[i] := true;
  exgntd := true;
  curcmd := empty1_em;
endrule;
endruleset;

ruleset i : NODE do
rule "SendGntS"
  curcmd = reqs_em &
  chan2[i].Cmd = empty2_em &
  exgntd = false
==>
begin
  chan2[i].Cmd := gnts_em;
  shrset[i] := true;
  curcmd := empty1_em;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvInvAck1"
  chan3[i].Cmd = invack_em &
  curcmd != empty1_em &
  exgntd = true
==>
begin
  chan3[i].Cmd := empty3_em;
  shrset[i] := false;
  exgntd := false;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvInvAck2"
  chan3[i].Cmd = invack_em &
  curcmd != empty1_em &
  exgntd = false
==>
begin
  chan3[i].Cmd := empty3_em;
  shrset[i] := false;
endrule;
endruleset;

ruleset i : NODE do
rule "SendInvAck"
  chan2[i].Cmd = inv_em &
  chan3[i].Cmd = empty3_em
==>
begin
  chan2[i].Cmd := empty2_em;
  chan3[i].Cmd := invack_em;
  cache[i].State := i_em;
endrule;
endruleset;

ruleset i : NODE do
rule "SendInv"
  chan2[i].Cmd = empty2_em &
  invset[i] = true &
  ( curcmd = reqe_em | curcmd = reqs_em & exgntd = true )
==>
begin
  chan2[i].Cmd := inv_em;
  invset[i] := false;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvReqE"
  curcmd = empty1_em &
  chan1[i].Cmd = reqe_em
==>
begin
  curcmd := reqe_em;
  chan1[i].Cmd := empty1_em;
  for j : NODE do
    invset[j] := shrset[j];
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvReqS"
  curcmd = empty1_em &
  chan1[i].Cmd = reqs_em
==>
begin
  curcmd := reqs_em;
  chan1[i].Cmd := empty1_em;
  for j : NODE do
    invset[j] := shrset[j];
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "SendReqE"
  chan1[i].Cmd = empty1_em &
  (cache[i].State = i_em | cache[i].State = s_em)
==>
begin
  chan1[i].Cmd := reqe_em;
endrule;
endruleset;

ruleset i : NODE do
rule "SendReqS"
  chan1[i].Cmd = empty1_em &
  cache[i].State = i_em
==>
begin
  chan1[i].Cmd := reqs_em;
endrule;
endruleset;