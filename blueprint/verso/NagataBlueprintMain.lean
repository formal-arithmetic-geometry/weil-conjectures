import VersoManual
import VersoBlueprint.PreviewManifest
import NagataBlueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc NagataBlueprint)
    args
    (extensionImpls := by exact extension_impls%)
