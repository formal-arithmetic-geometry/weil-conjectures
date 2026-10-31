/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateEvaluationData
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows

/-! # Restriction of the local proper/open refinement seed

Source: Stacks 0F7B and 07A6; whole-tower restriction and mate normalization.
(blueprint: lem-pur-strict-refinement-seed-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived
attribute [local instance 5000] AlgebraicGeometry.ProEtale.StrictTower.towers_hasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.StrictTower.towers_hasDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] U J R G

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Restriction preserves the local proper/open seed before any further proper image.
Source: Stacks 0F7B (lemma-shriek-proper-and-open), open case, and 07A6;
strict constant-tower adaptation of the restriction-square proof, first step.
(blueprint: lem-pur-strict-refinement-seed-restriction).
Proof: factor the square through its fibre product. The induced lift is clopen.
Coefficient restriction retains the underlying sections, so it preserves both the
open-unit comparison and the projector (identity on the image, zero on its
complement). It therefore preserves alpha. The unit-normalized proper restriction
square transports the geometric units and counits; the mate formula consequently
transports gamma. Its identity-proper normalization transports rId as well. This
proves the first equation. For arithmetic selection the same ordinary equations
hold at every retained level, including transitions and differentials. Positive
selection is exact and preserves K-injectives. Derive these equations with the
specified composite units, obtaining exactly reindexProper and reindexOpen.
This proves the second equation on strict diagrams before finite evaluation. -/
theorem strictRefinementSeedRestriction
    {X W T : Scheme.{u}} (k : X ⟶ W) (j : X ⟶ T) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion j] [QuasiCompact k] [QuasiCompact j]
    [IsProper p] (h : k ≫ p = (𝟙 X) ≫ j) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
    let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
    let sA := Functor.whiskerRight (rId A X).inv (J A j) ≫ gamma A k (𝟙 X) p j h
    let sB := Functor.whiskerRight (rId B X).inv (J B j) ≫ gamma B k (𝟙 X) p j h
    (∀ N : Derived B X,
      sA.app ((U l E F i X).obj N) ≫
          (R A p).map ((openRestriction l E F i k).hom.app N) ≫
          (properRestriction l E F i p).inv.app ((J B k).obj N) =
        (openRestriction l E F i j).hom.app N ≫ (U l E F i T).map (sB.app N)) ∧
    ∀ (e : ℕ) (he : 1 ≤ e) (N : Derived B X),
      (subsequence l F T e).map (sB.app N) ≫
          (reindexProper l F p e he).hom.app ((J B k).obj N) ≫
          (R B p).map ((reindexOpen l F k e).hom.app N) =
        (reindexOpen l F j e).hom.app N ≫ sB.app ((subsequence l F X e).obj N) := by
  sorry

end WeilConjectures.PurStrictScalar
