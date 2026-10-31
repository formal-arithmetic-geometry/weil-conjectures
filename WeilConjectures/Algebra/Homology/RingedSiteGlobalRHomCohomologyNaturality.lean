/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! Naturality of cohomology of the ordinary Hom complex in every integer degree. -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteGlobalRHom

section External
open CochainComplex HomComplex Preadditive
variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- The map on ordinary Hom complexes induced by pre- and postcomposition.
Source: Stacks Project, Tag 08JA.
(blueprint: lem-sfb-global-rhom-external-cohomology-naturality). -/
def externalHomMap {L L' I I' : CochainComplex D ℤ} (f : L' ⟶ L) (g : I ⟶ I') :
    HomComplex L I ⟶ HomComplex L' I' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ((Cochain.ofHom f).comp a (zero_add n)).comp
        (Cochain.ofHom g) (add_zero n)
      map_zero' := by simp
      map_add' := by intros; simp }
  comm' i j _ := by
    ext a
    change δ i j (((Cochain.ofHom f).comp a (zero_add i)).comp
      (Cochain.ofHom g) (add_zero i)) =
        ((Cochain.ofHom f).comp (δ i j a) (zero_add j)).comp
          (Cochain.ofHom g) (add_zero j)
    rw [δ_comp_ofHom, δ_ofHom_comp]

omit [HasDerivedCategory D] in
/-- The cochain components of the pre- and postcomposition map.
Source: Stacks Project, Tag 08JA.
(blueprint: lem-sfb-global-rhom-external-cohomology-naturality). -/
theorem externalHomMap_v
    {L L' I I' : CochainComplex D ℤ} (f : L' ⟶ L) (g : I ⟶ I')
    (n : ℤ) (x : Cochain L I n) (p q : ℤ) (hpq : p + n = q) :
    ((externalHomMap f g).f n x).v p q hpq = f.f p ≫ x.v p q hpq ≫ g.f q := by
  change (((Cochain.ofHom f).comp x (zero_add n)).comp
    (Cochain.ofHom g) (add_zero n)).v p q hpq = _
  simp [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v]

/-- Hom-complex cohomology computes shifted derived morphisms into a K-injective.
Source: Stacks Project, Tags 08JA and 070I.
(blueprint: lem-sfb-global-rhom-external-cohomology-naturality). -/
def externalHomDerivedEquiv (L I : CochainComplex D ℤ) [I.IsKInjective] (n : ℤ) :
    (HomComplex L I).homology n ≃+
      (DerivedCategory.Q.obj L ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
  (HomComplex.homologyAddEquiv L I n).trans
    ((CohomologyClass.homAddEquiv (K := L) (L := I) (n := n)).trans
      ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
        (IsKInjective.Qh_map_bijective _ (I⟦n⟧))).trans
        { toFun := fun f ↦ ((DerivedCategory.quotientCompQhIso D).app L).inv ≫ f ≫
            ((DerivedCategory.quotientCompQhIso D).app (I⟦n⟧)).hom ≫
              (DerivedCategory.Q.commShiftIso n).hom.app I
          invFun := fun f ↦ ((DerivedCategory.quotientCompQhIso D).app L).hom ≫ f ≫
            (DerivedCategory.Q.commShiftIso n).inv.app I ≫
              ((DerivedCategory.quotientCompQhIso D).app (I⟦n⟧)).inv
          left_inv := by intro f; simp [Category.assoc]
          right_inv := by intro f; simp [Category.assoc]
          map_add' := by intros; simp only [Preadditive.comp_add, Preadditive.add_comp] }))

private def postcompData {L I I' : CochainComplex D ℤ} (f : I ⟶ I') (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (externalHomMap (𝟙 L) f))
      (HomComplex.leftHomologyData L I n) (HomComplex.leftHomologyData L I' n) where
  φK := AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.postcomp f
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  φH := (CohomologyClass.homAddEquiv (K := L) (L := I) (n := n)).toAddCommGrpIso.hom ≫
    AddCommGrpCat.ofHom
      { toFun := fun a ↦ a ≫ (HomotopyCategory.quotient D (.up ℤ)).map (f⟦n⟧')
        map_zero' := by simp
        map_add' := by intros; simp [add_comp] } ≫
    (CohomologyClass.homAddEquiv (K := L) (L := I') (n := n)).toAddCommGrpIso.inv
  commi := by
    ext z
    change (z.postcomp f).1 = (externalHomMap (𝟙 L) f).f n z.1
    simp [externalHomMap, Cocycle.postcomp]
    rfl
  commf' := by
    rw [← cancel_mono (HomComplex.leftHomologyData L I' n).i]
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    have hi : AddCommGrpCat.ofHom
        { toFun := fun z : Cocycle L I n ↦ z.postcomp f
          map_zero' := by ext; simp
          map_add' := by intros; ext; simp } ≫
        (HomComplex.leftHomologyData L I' n).i =
      (HomComplex.leftHomologyData L I n).i ≫ (externalHomMap (𝟙 L) f).f n := by
      ext z
      change (z.postcomp f).1 = (externalHomMap (𝟙 L) f).f n z.1
      simp [externalHomMap, Cocycle.postcomp]
      rfl
    rw [hi, ShortComplex.LeftHomologyData.f'_i_assoc]
    exact ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (externalHomMap (𝟙 L) f)).comm₁₂.symm
  commπ := by
    ext z
    apply (CohomologyClass.homAddEquiv (K := L) (L := I') (n := n)).injective
    change (CohomologyClass.homAddEquiv (K := L) (L := I') (n := n))
      ((CohomologyClass.homAddEquiv (K := L) (L := I') (n := n)).symm
        (CohomologyClass.toHom (CohomologyClass.mk z) ≫
          (HomotopyCategory.quotient D (.up ℤ)).map (f⟦n⟧'))) =
      CohomologyClass.toHom (CohomologyClass.mk (z.postcomp f))
    rw [AddEquiv.apply_symm_apply, CohomologyClass.toHom_mk,
      CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]

/-- The Hom-complex cohomology equivalence commutes with postcomposition.
Source: Stacks Project, Tags 08JA and 070I.
(blueprint: lem-sfb-global-rhom-external-cohomology-naturality).

Proof: on cocycles postcompose by the chain map. The cocycle-quotient homology
data identify the induced homology map with postcomposition on cohomology
classes, hence with postcomposition in the homotopy category. Apply localization
and use naturality of its factorization and shift isomorphisms. -/
theorem externalDerivedEquiv_naturality
    {L I I' : CochainComplex D ℤ} [I.IsKInjective] [I'.IsKInjective]
    (f : I ⟶ I') (n : ℤ) (x : (HomComplex L I).homology n) :
    externalHomDerivedEquiv L I' n
      (HomologicalComplex.homologyMap (externalHomMap (𝟙 L) f) n x) =
    externalHomDerivedEquiv L I n x ≫
      (DerivedCategory.Q.map f)⟦n⟧' := by
  have h := (postcompData (L := L) f n).homologyMap_eq
  change HomologicalComplex.homologyMap (externalHomMap (𝟙 L) f) n = _ at h
  have hx : HomComplex.homologyAddEquiv L I' n
      (HomologicalComplex.homologyMap (externalHomMap (𝟙 L) f) n x) =
      (CohomologyClass.homAddEquiv (K := L) (L := I') (n := n)).symm
        (CohomologyClass.homAddEquiv (HomComplex.homologyAddEquiv L I n x) ≫
          (HomotopyCategory.quotient D (.up ℤ)).map (f⟦n⟧')) := by
    rw [h]
    change (HomComplex.leftHomologyData L I' n).homologyIso.hom
      ((HomComplex.leftHomologyData L I' n).homologyIso.inv _) = _
    exact Iso.inv_hom_id_apply _ _
  dsimp only [externalHomDerivedEquiv, AddEquiv.trans_apply]
  rw [hx, AddEquiv.apply_symm_apply]
  simp only [AddEquiv.ofBijective_apply, Functor.mapAddHom_apply]
  change ((DerivedCategory.quotientCompQhIso D).app L).inv ≫
      DerivedCategory.Qh.map (_ ≫
        (HomotopyCategory.quotient D (.up ℤ)).map (f⟦n⟧')) ≫
      ((DerivedCategory.quotientCompQhIso D).app (I'⟦n⟧)).hom ≫
      (DerivedCategory.Q.commShiftIso n).hom.app I' =
    (((DerivedCategory.quotientCompQhIso D).app L).inv ≫
      DerivedCategory.Qh.map
        (CohomologyClass.homAddEquiv (HomComplex.homologyAddEquiv L I n x)) ≫
      ((DerivedCategory.quotientCompQhIso D).app (I⟦n⟧)).hom ≫
      (DerivedCategory.Q.commShiftIso n).hom.app I) ≫ (DerivedCategory.Q.map f)⟦n⟧'
  have hn := (DerivedCategory.quotientCompQhIso D).hom.naturality (f⟦n⟧')
  have hs := (DerivedCategory.Q.commShiftIso n).hom.naturality f
  dsimp only [Functor.comp_map] at hn hs
  have ht : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient D (.up ℤ)).map (f⟦n⟧')) ≫
      ((DerivedCategory.quotientCompQhIso D).app (I'⟦n⟧)).hom ≫
      (DerivedCategory.Q.commShiftIso n).hom.app I' =
    ((DerivedCategory.quotientCompQhIso D).app (I⟦n⟧)).hom ≫
      (DerivedCategory.Q.commShiftIso n).hom.app I ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ (DerivedCategory.Q.commShiftIso n).hom.app I') hn).trans
        ((Category.assoc _ _ _).trans (congrArg
          (fun t ↦ (DerivedCategory.quotientCompQhIso D).hom.app (I⟦n⟧) ≫ t) hs)))
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ ((DerivedCategory.quotientCompQhIso D).app L).inv ≫
      DerivedCategory.Qh.map
        (CohomologyClass.homAddEquiv (HomComplex.homologyAddEquiv L I n x)) ≫ t) ht

end External

end CategoryTheory.RingedSiteGlobalRHom
