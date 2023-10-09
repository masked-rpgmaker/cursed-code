import Cursed.Basic

open IO

namespace Cursed.IO

def printlnTake (c : Child)  (t : Toy) := println s!"{c} pegou {t}"

def printlnPass (c : Child) (t : Toy) := println s!"{c} passou {t} para trás"
