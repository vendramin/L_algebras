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
  f := IO_File(Concatenation("L", String(n), ".eprime"), "w");
  for x in s do
    IO_WriteLine(f, x);
  od;
  IO_Flush(f);
  IO_Close(f);
end;

enumerate_L := function(n)
  local m, done,l,T,s,f,x,t,output, t0, t1, mytime;

  t0 := NanosecondsSinceEpoch();

  t := [];
  m := 0;
  s := "savilerow -run-solver -all-solutions -solutions-to-null ";

  LogTo();
  LogTo(Concatenation("L", String(n), ".log"));

  create_files(n);

  Print("Running savilerow. ");
  Exec(Concatenation(s, "L", String(n), ".eprime"));

  f := IO_File(Concatenation("L", String(n), ".eprime.info"), "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "SolverSolutionsFound:") then
      done := true;
      m := EvalString(String(x{[22..Size(x)]}));
    fi;
  od; 
 
  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("There are ", m, " L-algebras in ", mytime, "ms (=", StringTime(mytime), ")\n");

  IO_Flush(f);
  IO_Close(f);
end;


