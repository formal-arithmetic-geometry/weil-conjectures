/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.PurityTransport.CondensedTateLineTrivializations
import WeilConjectures.CategoryTheory.DerivedCategory.CondensedDualSingle
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-!
# Constructibility of the root-normalized signed Tate tensor

Source: latest blueprint, def-wf-tate-twist, exact heart restriction.
(blueprint: lem-dl-a1-signed-tate-tensor-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.DeligneLaumon.AffineLine.TateTwist

private theorem positiveLine_lisse (ell : ℕ) [Fact ell.Prime]
    (c : PurityTransport.Coefficient ell) (X : Scheme.{u})
    [∀ x : X, Invertible (ell : X.residueField x)] (n : ℕ) :
    IsLisseCoefficientModule (c.obj ell)
      (c.line ell X n) := by
  obtain ⟨C, hC⟩ := PurityTransport.line_locally_unit ell c X
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨e⟩ := hC i n
  exact ⟨1, ⟨e ≪≫ (biproductUniqueIso (fun _ : Fin 1 ↦
    Mod.regular (condensedRingObj (c.obj ell) (C.X i)))).symm⟩⟩

/-- Tensor with the specified signed root line preserves the constructible coefficient
heart on a Noetherian scheme where ell is invertible.
Source: def-wf-tate-twist, exact heart restriction
(blueprint: lem-dl-a1-signed-tate-tensor-constructible).
Proof: the compatible-root cover trivializes every positive power. The ordinary
linear dual of a locally free module is locally free, giving negative powers.
The recorded signed-line comparison transfers this to the actual Tate line.
Constructibility with finite constant models agrees with native constructibility
for Qbar_ell on a Noetherian scheme. Tensor with a locally free module preserves
native constructibility. Symmetry gives the stated order of the two factors.
The argument includes rank zero, exponent zero and the empty scheme. -/
theorem signedTate_tensor_constructible (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) [IsNoetherian X]
    [∀ x : X, Invertible (ell : X.residueField x)] (m : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) X M) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) X
      (M ⊗ CondensedRing.StrictWeilCondensed.tateLine ell .closure X m) := by
  have hc := (adicConstructibilityPredicateComparison ell X
    (Profinite.padicAlgClRingObj ell) .algebraicClosure).1
  exact (hc _).mp (((signedLine_locallyFree ell .closure X m).isConstructibleModuleObject_tensorObj
    ((hc M).mpr hM)).of_iso (β_ _ _))

end WeilConjectures.DeligneLaumon.AffineLine.TateTwist
