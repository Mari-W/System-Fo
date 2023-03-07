import os
from pathlib import Path
import shutil
import sys
from typing import Optional

FUN_PREFIX = "--[latex]"

def fun(s: str) -> Optional[tuple[str, Optional[str]]]:
  s = ''.join(s.split())
  if not s.startswith(FUN_PREFIX):
    return None
  s = s[len(FUN_PREFIX):]
  if s.endswith(")"):
    s = s[:-1]
    s = s.split("(")
    if s.__len__() != 2:
      print("expected 'fun(arg)'")
      exit(1)
    return s[0], s[1]
  else:
    return s, None

def rm_whitespace(l: list[str]) -> list[str]:
  while l[0].isspace():
    l = l[1:]
  while l[-1].isspace():
    l = l[:-1]
  return l

if __name__ == "__main__":
  path = sys.argv[1].strip()
  name = path.split("/")[-1].split(".")[0]
  with open(path.__str__(), "r") as file:
    lines = file.readlines()
    cmd, prefix = fun(lines[0])

    assert cmd == "prefix"
    end, _ = fun(lines[-1])
    assert end == "end"
    out = ""
    cur_fn, cur_arg = fun(lines[1])
    cur_lines = []
    
    for line in lines[2:]:
      maybe_fn = fun(line)
      if maybe_fn:
        if cur_fn == "hide":
          out +="\\begin{code}[hide]\n"
          out += "".join(rm_whitespace(cur_lines))
          out += "\\end{code}\n"
        elif cur_fn == "inline":
          if not cur_arg:
            print("expected name for inline code")
            exit(1)
          out +="\\newcommand{\\" + prefix + cur_arg + "}[0]{\\begin{code}[inline]\n"
          out += "".join(rm_whitespace(cur_lines))
          out += "\\end{code}}\n"
        elif cur_fn == "block":
          if not cur_arg:
            print("expected name for inline code")
            exit(1)
          out +="\\newcommand{\\" + prefix + cur_arg + "}[0]{\\begin{code}\n"
          out += "".join(rm_whitespace(cur_lines))
          out += "\\end{code}}\n"
        else:
          print("expected fun 'inline(name)'|'block(name)'|'hide'")
        cur_fn, cur_arg = maybe_fn
        cur_lines = []
      else:
        cur_lines.append(line)
    with open(name + ".lagda", "w+") as f:
      f.write(out)