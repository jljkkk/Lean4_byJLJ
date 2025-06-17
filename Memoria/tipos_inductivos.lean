import Mathlib.Tactic

inductive Season where
  | spring : Season
  | summer : Season
  | fall : Season
  | winter : Season
  deriving Repr

open Season
#eval fall

def next ( d : Season) : Season :=
    match d with
    | spring => summer
    | summer => fall
    | fall => winter
    | winter => spring

#eval next ( next fall )


def numberOfSeason ( d : Season) : Nat :=
    match d with
    | spring => 1
    | summer => 2
    | fall => 3
    | winter => 4

#eval numberOfSeason (next fall)
