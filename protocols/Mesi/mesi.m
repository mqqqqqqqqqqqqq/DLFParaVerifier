
const

  NODE_NUM : 2;

type

  NODE : 1..NODE_NUM;

  LOCATION: enum {MM, E, S, I};

var

  state : array [NODE] of LOCATION;

startstate "Init"
  for i : NODE do
    state[i] := I;
  endfor;
endstartstate;

ruleset i : NODE do
rule "t1"
  state[i] = E
==>
begin
  state[i] := MM;
endrule;
endruleset;

ruleset i : NODE do
rule "t2"
  state[i] = I
==>
begin
  state[i] := S;
  for j : NODE do
    if (j != i & state[j] = I) then
      state[j] := I;
    end;
    if (j != i & state[j] != I) then
      state[j] := S;
  end;
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "t3"
  state[i] = S
==>
begin
  state[i] := E;
  for j : NODE do
    if (j != i) then
      state[j] := I;
    end;
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "t4"
  state[i] = MM
==>
begin
  state[i] := E;
  for j : NODE do
    if (j != i) then
      state[j] := I;
    end;
  end;
endrule;
endruleset;

