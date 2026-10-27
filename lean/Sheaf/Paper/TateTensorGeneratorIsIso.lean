/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TateTensorGeneratorMap
import Sheaf.Paper.TateTensorGeneratorLocalIsIso

/-! Fixed-level root-generator comparison for the integral Tate tensor.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-isiso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- A morphism with the prescribed root-generator formula is invertible.

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport, Step 2,
local rank-one argument in the ordinary quotient comparison.
(blueprint: lem-pur-tate-tensor-generator-isiso)

Proof: choose the common pro-etale covering with compatible primitive roots,
using invertibility of ell. The integral root limit is free on that root family:
the inverse coordinate map takes a compatible section to its compatible residue
coordinates. Scalar extension modulo ell^(n+1) therefore has that family's finite
image as basis. The finite Tate tensor also has the corresponding tensor of
primitive roots as basis. The prescribed formula with coefficient one sends
this basis to this basis, so the morphism is locally an isomorphism of rank-one
modules. Its local inverses agree on overlaps by their inverse laws and glue,
giving a two-sided inverse. Degree zero uses the coefficient unit and the empty
scheme uses the unique morphism. -/
theorem tateTensorQuotient_generator_isIso
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    (f : (realization T ell n).obj (finiteSheaf T ell n d) ⟶ quotientLine T ell n d)
    (hf : GeneratorCompatible T ell n d f) : IsIso f := by
  have hlocal := tateTensorQuotient_generator_local_isIso T ell hT n d f hf
  let F := SheafOfModules.toSheaf
    ((adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op n)))
  haveI : IsIso (F.map f) := by
    apply Sheaf.isIso_of_isIso_app_of_mem
      (J := ProEt.topology T) (F.map f)
    intro X
    refine ⟨⊤, (ProEt.topology T).top_mem _, ?_⟩
    intro Y g _
    letI := hlocal (op Y)
    change IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map (f.val.app (op Y)))
    infer_instance
  exact isIso_of_reflects_iso f F

end AlgebraicGeometry.Scheme.PurityIntegralTower
