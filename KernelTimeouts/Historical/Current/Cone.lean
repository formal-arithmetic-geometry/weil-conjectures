import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs

set_option diagnostics true
set_option maxHeartbeats 0

open CategoryTheory Limits MonoidalCategory Opposite

namespace CurrentConeProbe

universe u

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)
  (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))

noncomputable def B00_sorry :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := sorry

noncomputable def B00_real :
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) :=
  letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
  ((tensorLeft K).mapCone (DerivedCategory.quotPowCone J I)).extend (ρ_ K).inv

noncomputable def B10_sorry :
    Cone (DerivedCategory.derivedCompletionDiagram J I K) := sorry

noncomputable def B10_real :
    Cone (DerivedCategory.derivedCompletionDiagram J I K) :=
  letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
  ((tensorLeft K).mapCone (DerivedCategory.quotPowCone J I)).extend (ρ_ K).inv

noncomputable def B01_sorry :
    letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) := sorry

noncomputable def B01_real :
    letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
    Cone (DerivedCategory.quotPowFunctor J I ⋙ tensorLeft K) :=
  letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
  ((tensorLeft K).mapCone (DerivedCategory.quotPowCone J I)).extend (ρ_ K).inv

noncomputable def B11_sorry :
    letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
    Cone (DerivedCategory.derivedCompletionDiagram J I K) := sorry

noncomputable def B11_real :
    letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
    Cone (DerivedCategory.derivedCompletionDiagram J I K) :=
  letI := (DerivedCategory.sheafTensorStructure J R).monoidalCategory
  ((tensorLeft K).mapCone (DerivedCategory.quotPowCone J I)).extend (ρ_ K).inv

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in [`CurrentConeProbe.B00_sorry, `CurrentConeProbe.B00_real,
      `CurrentConeProbe.B10_sorry, `CurrentConeProbe.B10_real,
      `CurrentConeProbe.B01_sorry, `CurrentConeProbe.B01_real,
      `CurrentConeProbe.B11_sorry, `CurrentConeProbe.B11_real] do
    let some info := env.find? name
      | throwError "declaration not found: {name}"
    let some value := info.value? (allowOpaque := true)
      | throwError "value not found: {name}"
    let t0 ← IO.monoMsNow
    let checkedType := Kernel.check env {} info.type
    let t1 ← IO.monoMsNow
    let checkedValue := Kernel.check env {} value
    let t2 ← IO.monoMsNow
    let final := match checkedValue with
      | .ok inferred => Kernel.isDefEq env {} inferred info.type
      | .error e => .error e
    let t3 ← IO.monoMsNow
    let finalOk := final.toOption == some true
    logInfo m!"{name}: type={t1-t0}ms value={t2-t1}ms final={t3-t2}ms ok={finalOk}"

end CurrentConeProbe
