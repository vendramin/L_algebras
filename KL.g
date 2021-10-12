create_file := function(n)
  local m,f,k,lines,perms,tmp1,tmp2;

  tmp1 := "";
  tmp2 := "";

  perms := AsList(SymmetricGroup(n-1)){[2..Factorial(n-1)]};;

  for k in perms do
    Append(tmp1, Concatenation(String(ListPerm(k,n)),",\n"));
    Append(tmp2, Concatenation(String(ListPerm(Inverse(k),n)),",\n"));
  od;

  lines := [ 
  "language ESSENCE' 1.0\n",
  Concatenation("letting n be ", String(n), "\n"),
  "letting perms be [\n", tmp1, "]\n",
  "letting inverses be [\n", tmp2, "]\n",
  "find M : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
  "such that\n",
  "forAll x : int(1..n) .",
  "  M[n,x]=x,\n",
  "forAll x : int(1..n) .",
  "  M[x,x]=n,\n",
  "forAll x : int(1..n) .",
  "  M[x,n]=n,\n",
  "forAll x,y,z : int(1..n) .", 
  "  M[M[x,y],M[x,z]]=M[M[y,x],M[y,z]],\n",
  "forAll x,y : int(1..n) .",
  "  M[x,M[y,x]]=n,\n",
  "forAll x : int(1..n-1) .",
  "  forAll y: int(x+1..n) .",
  "    M[x,y]+M[y,x]<2*n,\n",
  ];

   Add(lines, Concatenation("forAll p : int(1..", String(Size(perms)), ") .\n\\
    flatten( [ M[i,j] | i : int(1..n), j : int(1..n)] )\n\\
    <=lex flatten( [ inverses[p,M[perms[p,i],perms[p,j]]] | i : int(1..n), j : int(1..n)] ),"));

  Add(lines, "\ntrue\n");
  return lines;
end;

create_files := function(n)
  local f,x,s; 
  s := create_file(n);
  f := IO_File(Concatenation("KL", String(n), ".eprime"), "w");
  for x in s do
    IO_WriteLine(f, x);
  od;
  IO_Flush(f);
  IO_Close(f);
end;

#twist_matrix := function(obj, f)
#  local i,j,m,n;
#  n := Size(obj);
#  m := NullMat(n,n);
#  for i in [1..n] do
#    for j in [1..n] do
#      if obj[i^Inverse(f)][j^Inverse(f)] <> 0 then
#        m[i][j] := obj[i^Inverse(f)][j^Inverse(f)]^f;
#      fi;
#    od;
#  od;
#  return m;
#end;

#is_minimal := function(m, centralizer)
#  local p;
#  for p in centralizer do
#    if Flat(m) > Flat(twist_matrix(m, p)) then
#      return false;
#      fi;
#  od;
#  return true;
#end;

#is_Lalgebra := function(m)
#  local x,y,n;
#  n := Size(m);
#  for x in [1..n] do
#    for y in [1..n-1] do
#      if (m[x][y] = n and m[y][x] = n) and not x=y then
#        return false;
#      fi;
#    od;
#  od;
#  return true;
#end;

keep_KL := function(n, filename)
  local l, k, x, m, f, done;
    
  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
      #if is_Lalgebra(m) then
        k := k+1;
        Add(l, m);
      #fi; 
    fi;
  od; 
  Print("I found ", k, " solutions\n");  
  return l; 
end;



#keep_minimal := function(n, filename, group)
#  local l, k, x, m, f, done;
#    
#  l := [];
#  k := 0;
#
#  f := IO_File(filename, "r");
#  done := false;
#
#  while not done do
#    x := IO_ReadLine(f);
#    if StartsWith(x, "Created information file") then
#      done := true;
#    elif StartsWith(x, "Solution") then
#      m := EvalString(String(x{[46..Size(x)]}));
#      if is_minimal(m, group) then
#        k := k+1;
#        Add(l, m);
#      fi; 
#    fi;
#  od; 
#  Print("I found ", k, " solutions\n");  
#  return l; 
#end;

read_file := function(n, filename, T)
  local l, k, x, m, f, done;
    
  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
      k := k+1;
      Add(l, m);
    fi;
  od; 
  Print("I found ", k, " solutions\n");  
  return l;
end;

construct_KL := function(n)
  local m, l,T,k,s,f,x,t,output, t0, t1, mytime;

  t0 := NanosecondsSinceEpoch();

  t := [];
  m := 0;
  s := "savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  LogTo();
  LogTo(Concatenation("KL", String(n), ".log"));

  create_files(n);

  Print("Running savilerow. ");
  output := Concatenation("output", String(n));
  Exec(Concatenation(s, "KL", String(n), ".eprime >", output));
  for x in keep_KL(n, output) do 
    #SymmetricGroup(n-1)) do
    Add(t, x);
    m := m+1;
  od;

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", m, " KL-algebras in ", mytime, "ms (=", StringTime(mytime), ")\n");

  f := IO_File(Concatenation("KL", String(n), ".g"), "w");
  IO_WriteLine(f, Concatenation("KL", String(n), " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),",")); 
  od;
  IO_WriteLine(f, "];");
  IO_Flush(f);
  IO_Close(f);
end;


