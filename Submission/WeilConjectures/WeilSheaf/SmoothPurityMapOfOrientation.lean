/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.TraceFormula.PurityTensorMap
public import Submission.WeilConjectures.WeilSheaf.LowerShriek
public import Submission.WeilConjectures.WeilSheaf.TateTwist
public import Submission.WeilConjectures.WeilSheaf.TateTwistNativeTensor
public import Submission.WeilConjectures.WeilSheaf.UpperShriek
public import Submission.WeilConjectures.WeilSheaf.UpperShriekGeometric
public import Submission.WeilConjectures.WeilSheaf.UpperShriekUnitTensorMap
public import Submission.WeilConjectures.WeilSheaf.UpperStarConstant
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import Submission.WeilConjectures.TraceFormula.PurityDevissage

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3


/-! Construction of the smooth purity map from a supplied Weil orientation. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

section Geometric

open ProEtale MonoidalCategory

variable [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

/-- A diagram lemma for `exists_natTrans_forget_eq_upperShriekUnitTensorMap`:
if `G (H p)` is `ψ' ≫ u ≫ φ'⁻¹`, then `G (H (a ≫ p)) ≫ φ` is
`(G (H a) ≫ ψ' ≫ u ≫ φ'⁻¹ ≫ φ ≫ u⁻¹) ≫ u`. -/
private lemma comp_map_comp_hom_eq_of_eq {A B C : Type*} [Category* A] [Category* B]
    [Category* C] (H : A ⥤ B) (G : B ⥤ C) {S T R : A} {P Q : C} (a : S ≅ T) (p : T ⟶ R)
    {φ φ' : G.obj (H.obj R) ≅ Q} {ψ' : G.obj (H.obj T) ≅ P} {u : P ≅ Q}
    (h : G.map (H.map p) = (ψ'.hom ≫ u.hom) ≫ φ'.inv) :
    G.map (H.map (a.hom ≫ p)) ≫ φ.hom =
      (G.mapIso (H.mapIso a) ≪≫ ψ' ≪≫ u ≪≫ φ'.symm ≪≫ φ ≪≫ u.symm).hom ≫ u.hom := by
  simp [h]

/-- An isomorphism of the constant factor induces an isomorphism of product functors. -/
private def prodConstIsoOfIso {C : Type*} [Category* C] {P Q : C} (e : P ≅ Q) :
    (𝟭 C).prod' ((Functor.const C).obj P) ≅
      (𝟭 C).prod' ((Functor.const C).obj Q) :=
  NatIso.ofComponents (fun K ↦ Iso.prod (Iso.refl K) e) (fun _ ↦ by
    ext <;> simp)

end Geometric

end WeilComplex

end AlgebraicGeometry
