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


