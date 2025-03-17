const 
    NODE_NUM : 2;

type 
    NODE : scalarset(NODE_NUM);
    locationType: enum{m_em, ostatus_em, e_em, s_em, i_em};

var 
    sta : array[NODE] of locationType;

startstate "Init"
 for i: NODE do
    sta[i] := i_em; 
  endfor; 
endstartstate;

ruleset i : NODE do
rule "t1"
    sta[i] = e_em ==>
begin
    sta[i] := m_em;
endrule;endruleset;

ruleset i : NODE do
rule "t2"
    sta[i] = i_em ==>
begin
	sta[i] := s_em;
    for j: NODE do
        if (j != i & sta[j] = e_em) then
          sta[j] := s_em;
        end;
        if (j != i & sta[j] = m_em) then 
            sta[j] := ostatus_em;
        end;
    endfor;
endrule;
endruleset;

ruleset i : NODE do
rule "t3"
    sta[i] = s_em ==>
begin
	sta[i] := e_em;
    for j: NODE do
    	if (j != i) then sta[j] := i_em;
    end;
    endfor;
endrule;
endruleset;

ruleset i : NODE do
rule "t4"
    sta[i] = ostatus_em
==>
begin
	sta[i] := e_em;
    for j: NODE do
    	if (j != i) then sta[j] := i_em;
    	end;
    endfor;
endrule;endruleset;

ruleset i : NODE do
rule "t5"
    sta[i] = i_em 
==>
begin
	sta[i] := e_em;
    for j: NODE do
    	if (j != i) then sta[j] := i_em;
    	end;
    endfor;
endrule;
endruleset;


