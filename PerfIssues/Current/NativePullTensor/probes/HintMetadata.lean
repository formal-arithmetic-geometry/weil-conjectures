module

import all WeilConjectures.WeilSheaf.Native.NativePullTensor

open Lean Lean.Meta CategoryTheory

universe u₁ v₁ u₂ v₂

def auditRegularObjMeta {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) (X : C) : D :=
  F.obj X

abbrev auditAbbrevObjMeta {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) (X : C) : D :=
  F.obj X

run_meta do
  for name in [`CategoryTheory.Functor.obj, ``auditRegularObjMeta,
      ``auditAbbrevObjMeta] do
    match (← getConstInfo name) with
    | .defnInfo d => logInfo m!"{name}: level params {d.levelParams}"
    | _ => logInfo m!"{name}: other"
