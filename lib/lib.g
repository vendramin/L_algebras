logical_unit := function(obj)
  return obj[1][1];
end;

leq := function(obj, x, y)
  return (obj[x][y] = Size(obj));
end;

interval := function(obj, x)
  return Filtered([1..Size(obj)], y->leq(obj, y, x));
end;

down_set := function(obj, y)
  return Filtered([1..Size(obj)], z->leq(obj, z, y));
end;

is_selfsimilar := function(obj)
  local n, y;
  n := Size(obj);
  for y in [1..n] do
    if Size(Set(down_set(obj, y))) <> n then
      return false;
    fi;
  od;
  return true;
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

# Is an element of an L-algebra prime?
is_prime_element := function(obj, p)
  local n;
  n := Size(obj);
  if p=n then 
    return false;
  fi;
  return ForAll([1..n], x->leq(obj, x, p) or obj[x][p]=p);
end;

prime_elements := function(obj)
  return Filtered([1..Size(obj)], z->is_prime_element(obj, z));
end;

# Is an L-algebra prime?
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
      if not obj[y][x] in subset or not obj[y][obj[x][y]] in subset then
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

ideal_generated_by := function(obj, subset)
  local f;
  f := Filtered(ideals(obj), x->not Intersection(subset, x) = []);
  return Iterated(f, Intersection);
end;

principal_ideal := function(obj, x)
  return ideal_generated_by(obj, [x]);
end;

# computes the dot product of ideals I and J
# By definition, it is the largest ideal K of X 
# such that X cap I is included in J
dot := function(obj, I, J)
  local l, f;

  l := ideals(obj);
  f := Filtered(l, K->IsSubset(J, Intersection(K, I)));
  Sort(f, function(u,v) return Size(u) < Size(v); end);
  return Set(Reversed(f)[1]);
end;

spatial_locale := function(obj)
  local l, x, y, i, j, m;

  l := List(ideals(obj), Set);
  m := NullMat(Size(l), Size(l));

  for x in l do
    i := Position(l, x);
    for y in l do
      j := Position(l, y);
      m[i][j] := Position(l, dot(obj, x, y));
    od;
  od;
  return m;
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

is_simple := function(obj)
  if Size(ideals(obj))=2 then
    return true;
  else
    return false;
  fi;
end;

poset := function(obj)
  local l, x, y, n;
  n := Size(obj);
  l := [];
  for x in [1..n] do
    for y in [1..n] do
      if obj[x][y] = n then
        Add(l, [x, y]);
      fi;
    od;
  od;
  return Set(l);
end;

is_prime_ideal := function(obj, subset)
  local x, l;

  if not is_ideal(obj, subset) then
    return false;
  fi;

  if Size(subset)=Size(obj) then
    return false;
  fi;

  l := ideals(obj);

  for x in l do
    if not (IsSubset(x, subset) or IsSubset(dot(obj, x, subset), subset)) then
      return false;
    fi;
  od;
  return true;
end;

prime_ideals := function(obj)
  return Filtered(ideals(obj), x->is_prime_ideal(obj, x));
end;


is_quasi_prime := function(obj, x)
  local I, J, l;
  
  if x = logical_unit(obj) then
    return false;
  fi;

  l := ideals(obj);
  
  for I in l do
    for J in l do
      if x in joint(obj, I, J) and not x in Union(I, J) then
        return false;
      fi;
    od;
  od;
  return true;
end;

quasi_prime_elements := function(obj)
  return Filtered([1..Size(obj)], x->is_quasi_prime(obj, x));
end;

spec := function(obj)
  return prime_ideals(obj);
end;

is_dense := function(obj, x)
  local y;
  for y in [1..Size(obj)] do
    if obj[x][y] = y and leq(obj, y, x) then
      return true;
    fi;
  od;
  return false;
end;

dense_elements := function(obj)
  return Filtered([1..Size(obj)], x->is_dense(obj, x));
end;

is_regular := function(obj, x)
  local y;
  for y in dense_elements(obj) do
    if not obj[y][x] = x then
      return false;
    fi;
  od;
  return true;
end;

regular_elements := function(obj)
  return Filtered([1..Size(obj)], x->is_regular(obj, x));
end;

is_subLalgebra := function(obj, subset)
  local x, y;
  for x in subset do
    for y in subset do
      if not obj[x][y] in subset then 
        return false;
      fi;
    od;
  od;
  return true;
end;

is_invariant := function(obj, subset)
  local x, y;
  for x in [1..Size(obj)] do
    for y in subset do
      if not obj[x][y] in subset then 
        return false;
      fi;
    od;
  od;
  return true;
end;

