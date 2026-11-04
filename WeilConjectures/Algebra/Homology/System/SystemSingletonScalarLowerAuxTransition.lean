/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic
public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarLowerAux

/-! # The derived transition on the ringed sequence site

The localized strict transition, transported to the vertical sequence site, together with
its transpose formula for the canonical lower-singleton maps.
Source: Zheng, Construction 4.1; Stacks 0FND
(blueprint: lem-pur-system-singleton-scalar-lower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The derived transition between vertical evaluations of the sequence site, transported
from the strict derived transition along the canonical exact-functor compositors.
Source: Zheng 4.1; Stacks 015F (blueprint: lem-pur-system-singleton-scalar-lower). -/
def singletonSequenceDerivedTransition (R : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {n m : ℕ}
    (h : n ≤ m) :
    (systemSequenceEvaluation R m).mapDerivedCategory ⟶
      (systemSequenceEvaluation R n).mapDerivedCategory ⋙
        (systemRestriction R h).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence R).inverse
      (systemEvaluation R m)).hom ≫
    Functor.whiskerLeft (strictSystemSequenceEquivalence R).inverse.mapDerivedCategory
      (systemDerivedTransition R h) ≫
    Functor.whiskerRight (Functor.mapDerivedCategoryCompIso
      (strictSystemSequenceEquivalence R).inverse (systemEvaluation R n)).inv
      (systemRestriction R h).mapDerivedCategory

/-- The ordinary transition between vertical evaluations of the sequence site.
Source: Zheng 4.1 (blueprint: lem-pur-system-singleton-scalar-lower). -/
abbrev singletonSequenceTransition (R : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {n m : ℕ}
    (h : n ≤ m) :
    systemSequenceEvaluation R m ⟶ systemSequenceEvaluation R n ⋙ systemRestriction R h :=
  Functor.whiskerLeft (strictSystemSequenceEquivalence R).inverse (strictSystemTransition R h)

/-- The transported derived transition is represented by the ordinary transition.
Source: Zheng 4.1; Stacks 015F (blueprint: lem-pur-system-singleton-scalar-lower).
Proof: cancel the compositors against the factorization maps, move the strict derived
transition across the inverse-equivalence factorization by naturality, and apply the
representative formula for the strict derived transition. -/
theorem singletonSequenceDerivedTransition_rep (R : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {n m : ℕ}
    (h : n ≤ m) (K : CochainComplex (systemSequenceModules R) ℤ) :
    (singletonSequenceDerivedTransition R h).app (DerivedCategory.Q.obj K) ≫
      (systemRestriction R h).mapDerivedCategory.map
        ((systemSequenceEvaluation R n).mapDerivedCategoryFactors.hom.app K) ≫
      (systemRestriction R h).mapDerivedCategoryFactors.hom.app
        (((systemSequenceEvaluation R n).mapHomologicalComplex (.up ℤ)).obj K) =
    (systemSequenceEvaluation R m).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (singletonSequenceTransition R h) (.up ℤ)).app K) := by
  let E := strictSystemSequenceEquivalence R
  have hcn : (Functor.mapDerivedCategoryCompIso E.inverse (systemEvaluation R n)).hom.app
        (DerivedCategory.Q.obj K) ≫
      (systemEvaluation R n).mapDerivedCategory.map
        (E.inverse.mapDerivedCategoryFactors.hom.app K) ≫
      (systemEvaluation R n).mapDerivedCategoryFactors.hom.app
        ((E.inverse.mapHomologicalComplex (.up ℤ)).obj K) =
      (systemSequenceEvaluation R n).mapDerivedCategoryFactors.hom.app K :=
    Functor.mapDerivedCategoryCompIso_hom_app_factors _ _ K
  have hcm : (Functor.mapDerivedCategoryCompIso E.inverse (systemEvaluation R m)).hom.app
        (DerivedCategory.Q.obj K) ≫
      (systemEvaluation R m).mapDerivedCategory.map
        (E.inverse.mapDerivedCategoryFactors.hom.app K) ≫
      (systemEvaluation R m).mapDerivedCategoryFactors.hom.app
        ((E.inverse.mapHomologicalComplex (.up ℤ)).obj K) =
      (systemSequenceEvaluation R m).mapDerivedCategoryFactors.hom.app K :=
    Functor.mapDerivedCategoryCompIso_hom_app_factors _ _ K
  have nat := (systemDerivedTransition R h).naturality
    (E.inverse.mapDerivedCategoryFactors.hom.app K)
  rw [Functor.comp_map] at nat
  have hrep := systemDerivedTransition_rep R h ((E.inverse.mapHomologicalComplex (.up ℤ)).obj K)
  simp only [singletonSequenceDerivedTransition, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hcn, Iso.inv_hom_id_app_assoc, Functor.map_comp_assoc,
    ← reassoc_of% nat]
  erw [hrep]
  erw [reassoc_of% hcm]
  rfl

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)

/-- The canonical lower-singleton map transposes to the derived transition.
Source: Zheng 4.1; Stacks 0FND (blueprint: lem-pur-system-singleton-scalar-lower).
Proof: transpose across the derived sequence equivalence, then across the strict singleton
adjunction, and apply the strict lower transpose formula; the exact-functor compositors in
the transported adjunctions cancel against those in the transported transition. -/
theorem singletonLowerMap_transpose (R : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {n m : ℕ}
    (h : n ≤ m) (P : DerivedCategory (systemLevel R m))
    (Y : DerivedCategory (systemSequenceModules R))
    (z : (singletonSequenceDerived S T R m).obj P ⟶ Y) :
    (systemDerivedTensorAdj S R h).homEquiv P _
        ((singletonSequenceDerivedAdjunction S T R n).homEquiv _ Y
          (singletonLowerMap S T R h P ≫ z)) =
      (singletonSequenceDerivedAdjunction S T R m).homEquiv P Y z ≫
        (singletonSequenceDerivedTransition R h).app Y := by
  simp only [singletonSequenceDerivedAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv, singletonLowerMap]
  erw [Equiv.trans_apply, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left]
  erw [(systemSingleDerivedExtension R n S T).adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right]
  erw [systemSingleDerivedTranspose S T R h]
  simp [singletonSequenceDerivedTransition]
  rfl

/-- The ordinary transitions commute with the identity-on-sections restriction squares.
Source: Stacks 03DA; Zheng 4.1 (blueprint: lem-pur-system-singleton-scalar-lower).
Proof: every map in the square is a restriction map or the identity on sections. -/
theorem singletonSequenceTransition_restriction {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}}
    (a : B ⟶ D) {n m : ℕ} (h : n ≤ m) (M : systemSequenceModules D) :
    (singletonRestrictionEvaluation a m).inv.app M ≫
        (singletonSequenceTransition B h).app ((singletonSequenceRestriction a).obj M) =
      (singletonLevelRestriction a m).map ((singletonSequenceTransition D h).app M) ≫
        (systemScalarRestrictionComposition (a.app (op m)) (D.map (homOfLE h).op)
          (B.map (homOfLE h).op ≫ a.app (op n)) (a.naturality (homOfLE h).op)).hom.app
            ((systemSequenceEvaluation D n).obj M) ≫
        (systemScalarRestrictionComposition (B.map (homOfLE h).op) (a.app (op n))
          (B.map (homOfLE h).op ≫ a.app (op n)) rfl).inv.app
            ((systemSequenceEvaluation D n).obj M) ≫
        (systemRestriction B h).map ((singletonRestrictionEvaluation a n).inv.app M) := by
  ext U x
  rfl

end SheafOfModules
