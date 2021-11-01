leq := function(obj, x, y)
  return (obj[x][y] = Size(obj));
end;

interval := function(obj, x)
  return Filtered([1..Size(obj)], y->leq(obj, y, x));
end;

is_selfsimilar := function(obj)
  local n,m;
  n := Size(obj);
  m := NullMat(n,n);
end;

is_semiregular := function(obj)
  local x,y,z,n;
  n := Size(obj);
  for x in [1..n] do
    for y in [1..n] do
      for z in [1..n] do
        if not obj[obj[obj[x][y]][z]][obj[obj[y][x]][z]] = obj[obj[obj[x][y]][z]][z] then 
          return false;
        fi;
      od;
    od;
  od;
  return true;
end;

is_hilbert := function(obj)
  local x,y,z,n;
  n := Size(obj);
  for x in [1..n] do
    for y in [1..n] do
      for z in [1..n] do
        if not obj[x][obj[y][z]] = obj[obj[x][y]][obj[x][z]] then
          return false;
        fi;
      od;
    od;
  od;
  return true;
end;

is_dualBCK := function(obj)
  local x,y,z,n;
  n := Size(obj);
  for x in [1..n] do
    for y in [1..n] do
      for z in [1..n] do
        if not obj[x][obj[y][z]] = obj[obj[y][x]][z] then
          return false;
        fi;
      od;
    od;
  od;
  return true;
end;

is_KL := function(obj)
  local x,y,n;
  n := Size(obj);
  for x in [1..n] do
    for y in [1..n] do
      if not obj[x][obj[y][x]]=n then
        return false;
      fi;
    od;
  od;
  return true;
end;

is_CL := function(obj)
  local x,y,z,n;
  n := Size(obj);
  for x in [1..n] do
    for y in [1..n] do
      for z in [1..n] do
        if not obj[obj[x][obj[y][z]]][obj[y][obj[x][z]]] = n then
          return false;
        fi;
      od;
    od;
  od;
  return true;
end;

is_prime := function(obj)
  local x, p, n;
  n := Size(obj);
  for p in [1..n] do
    if not ForAll([1..n], x->leq(obj, x, p) or obj[x][p]=p) then 
      return false;
    fi;
  od;
  return true;
end;

is_linear := function(obj)
  local x, y, n;
  n := Size(obj);
  for x in [1..n] do
    for y in [1..n] do
      if not (obj[x][y] = n or obj[y][x]=n) then
        return false;
      fi;
    od;
  od;
  return true;
end;

is_discrete := function(obj)
  local x,y,n;
  n := Size(obj);
  for x in [1..n] do
    for y in [1..n] do
      if (leq(obj, x, y) and not x=y) and y <> n then
        return false;
      fi;
    od;
  od;
  return true;
end;

is_regular := function(obj)
  local x,y,z,n ;
  n := Size(obj);
  if not is_semiregular(obj) then
    return false;
  fi;
  for x in [1..n] do
    for y in [1..n] do
      if leq(obj, x, y) and Number([1..n], z->leq(obj, x,z) and obj[z][x]=y)=0 then
        return false;
       fi;
    od;
  od;
   return true;
end;

is_ideal := function(obj, subset)
  local n, x, y;

  n := Size(obj);
  
  if not n in subset then
    return false;
  fi;
  
  for x in subset do
    for y in [1..n] do
      if obj[x][y] in subset and not y in subset then
        return false;
      fi;
      if not obj[obj[x][y]][y] in subset then
        return false;
      fi;
      if obj[y][x] in subset and not obj[y][obj[x][y]] in subset then
        return false;
      fi;
    od;
  od;
  return true;
end;

ideals := function(obj)
  local c, l, n, subset;
  n := Size(obj);
  l := [];
  for c in IteratorOfCombinations([1..n]) do
    if not n in c then
      continue;
    fi;
    if is_ideal(obj, c) then
      Add(l, c);
    fi;
  od;
  return l;
end;

joint := function(obj, I, J)
  local l;  
  l := Filtered(ideals(obj), x->IsSubset(x, Union(I,J)));
  return Iterated(l, Intersection);
end;

is_distributive := function(obj)
  local l, x, y, z;
  l := ideals(obj);
  for x in l do
    for y in l do
      for z in l do
        if not Intersection(x, joint(obj, y, z)) = joint(obj, Intersection(x, y), Intersection(x, z)) then
          return false;
        fi;
      od;
    od;
  od;
  return true;
end;
