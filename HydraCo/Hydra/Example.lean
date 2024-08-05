import HydraCo.Hydra.Def
open Hydra

def head := node []
def hyd1 h := node [h]
def hyd2 h h' := node [h,h']
def hyd3 h h' h'' := node [h,h',h'']

def Hy :=
  hyd3
    head
    (hyd2
      (hyd1 (hyd2 head head))
      head)
    head

#eval hSize Hy
#eval hHeight Hy
#eval hMaxDegree Hy
