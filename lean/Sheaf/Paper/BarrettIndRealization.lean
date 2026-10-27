/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Paper.BarrettOrdinaryIndRealization
import Sheaf.CategoryTheory.IndDerivedRepresentableDetection

/-! # Constructible realization in the derived ind-heart

Source: Owen Barrett, arXiv:2005.10859, Theorem 1.1; Kashiwara--Schapira,
Categories and Sheaves, §15.3. This is the ordinary constructible-heart realization.
The free Weil functor occurs only in its compatibility with inverse image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v w t wX wY tX tY
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
/-- Free induction commutes with a left adjoint intertwining two autoequivalences.
Both composites are left adjoint to the same underlying lifted right adjoint. -/
private def freeTransportIso
    {C B : Type*} [Category C] [Category B]
    (F : C ⥤ C) [F.IsEquivalence] (G : B ⥤ B) [G.IsEquivalence]
    [HasColimitsOfShape (Discrete ℤ) C] [HasColimitsOfShape (Discrete ℤ) B]
    (L : C ⥤ B) [L.IsLeftAdjoint] (e : L ⋙ G ≅ F ⋙ L) :
    L ⋙ IsoAlgebra.Free.functor G ≅
      IsoAlgebra.Free.functor F ⋙ IsoAlgebra.mapOfNatIso e := by
  let adj := Adjunction.ofIsLeftAdjoint L
  let eR := IsoAlgebra.mateIso adj e
  exact Adjunction.leftAdjointUniq
    ((adj.comp (IsoAlgebra.Free.adjunction G)).ofNatIsoRight
      (IsoAlgebra.mapOfNatIsoCompForgetIso eR).symm)
    ((IsoAlgebra.Free.adjunction F).comp
      (IsoAlgebra.mapOfNatIsoAdjunction adj e eR rfl))

namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Frobenius is an autoequivalence on ordinary ind-objects.
Source: the already recorded exactness theorem.
(blueprint: lem-zl-barrett-ind-realization). -/
@[instance]
theorem zlIndFrobenius_equivalence (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (zlIndMap (zlSmallFrobenius D l hl Ω X₀)).IsEquivalence :=
  (zlIndFrobenius_exact D l hl Ω X₀).2.2.2

/-- Forgetting is additive for the canonical chosen abelian structures.
Source: the free-forgetful adjunction preserves products.
(blueprint: lem-zl-barrett-ind-realization). -/
@[instance]
theorem zlIndForget_additive (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (IsoAlgebra.forget (zlIndMap (zlSmallFrobenius D l hl Ω X₀))).Additive := by
  obtain ⟨ha, hlim, hcolim, he⟩ := zlIndFrobenius_exact D l hl Ω X₀
  let := ha
  let := hlim
  let := hcolim
  let := he
  let : Abelian (zlIndWeilHeart D l hl Ω X₀) := zlIndWeilHeartAbelian D l hl Ω X₀
  let : Preadditive (zlIndWeilHeart D l hl Ω X₀) :=
    (zlIndWeilHeartAbelian D l hl Ω X₀).toPreadditive
  let U := IsoAlgebra.forget (zlIndMap (zlSmallFrobenius D l hl Ω X₀))
  have : U.IsRightAdjoint := (IsoAlgebra.Free.adjunction _).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products U

/-- Free Frobenius induction is additive for the canonical chosen abelian structures.
Source: additivity transports across the free-forgetful adjunction.
(blueprint: lem-zl-barrett-ind-realization). -/
@[instance]
theorem zlIndFree_additive (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (IsoAlgebra.Free.functor (zlIndMap (zlSmallFrobenius D l hl Ω X₀))).Additive := by
  obtain ⟨ha, hlim, hcolim, he⟩ := zlIndFrobenius_exact D l hl Ω X₀
  let := ha
  let := hlim
  let := hcolim
  let := he
  let : Abelian (zlIndWeilHeart D l hl Ω X₀) := zlIndWeilHeartAbelian D l hl Ω X₀
  let : Preadditive (zlIndWeilHeart D l hl Ω X₀) :=
    (zlIndWeilHeartAbelian D l hl Ω X₀).toPreadditive
  exact (IsoAlgebra.Free.adjunction _).left_adjoint_additive

/-- Free Frobenius induction is left exact for the canonical abelian structures.
Source: exact coproducts and the sum of all Frobenius iterates.
(blueprint: lem-zl-barrett-ind-realization). -/
@[instance]
theorem zlIndFree_preservesFiniteLimits (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    PreservesFiniteLimits
      (IsoAlgebra.Free.functor (zlIndMap (zlSmallFrobenius D l hl Ω X₀))) := by
  obtain ⟨ha, hlim, hcolim, he⟩ := zlIndFrobenius_exact D l hl Ω X₀
  let := ha
  let := hlim
  let := hcolim
  let := he
  let : Abelian (zlIndWeilHeart D l hl Ω X₀) := zlIndWeilHeartAbelian D l hl Ω X₀
  let : Preadditive (zlIndWeilHeart D l hl Ω X₀) :=
    (zlIndWeilHeartAbelian D l hl Ω X₀).toPreadditive
  let F := IsoAlgebra.Free.functor (zlIndMap (zlSmallFrobenius D l hl Ω X₀))
  have : F.IsLeftAdjoint := (IsoAlgebra.Free.adjunction _).isLeftAdjoint
  have : F.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels F
  exact F.preservesFiniteLimits_of_preservesHomology

/-- Termwise derived free Frobenius pairs, using the specified sum of all integer iterates.
Source: the exact integer-sum free construction.
(blueprint: lem-zl-barrett-ind-realization). -/
def zlIndDerivedFree (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [HasDerivedCategory.{w} (Ind (zlSmallHeart D l Ω hl X₀))]
    [HasDerivedCategory.{t} (zlIndWeilHeart D l hl Ω X₀)] :
    DerivedCategory.Plus (Ind (zlSmallHeart D l Ω hl X₀)) ⥤
      DerivedCategory.Plus (zlIndWeilHeart D l hl Ω X₀) := by
  let := (zlIndFrobenius_exact D l hl Ω X₀).1
  let := (zlIndFrobenius_exact D l hl Ω X₀).2.1
  let := (zlIndFrobenius_exact D l hl Ω X₀).2.2.1
  let := (zlIndFrobenius_exact D l hl Ω X₀).2.2.2
  let : Abelian (zlIndWeilHeart D l hl Ω X₀) := zlIndWeilHeartAbelian D l hl Ω X₀
  let : Preadditive (zlIndWeilHeart D l hl Ω X₀) :=
    (zlIndWeilHeartAbelian D l hl Ω X₀).toPreadditive
  let F := IsoAlgebra.Free.functor (zlIndMap (zlSmallFrobenius D l hl Ω X₀))
  let : F.IsLeftAdjoint := (IsoAlgebra.Free.adjunction _).isLeftAdjoint
  exact F.mapDerivedCategoryPlus

/-- Termwise derived forgetting of Frobenius pairs. Source: exact fixed-pair forgetting.
(blueprint: lem-zl-barrett-ind-realization). -/
def zlIndDerivedForget (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [HasDerivedCategory.{w} (Ind (zlSmallHeart D l Ω hl X₀))]
    [HasDerivedCategory.{t} (zlIndWeilHeart D l hl Ω X₀)] :
    DerivedCategory.Plus (zlIndWeilHeart D l hl Ω X₀) ⥤
      DerivedCategory.Plus (Ind (zlSmallHeart D l Ω hl X₀)) := by
  let := (zlIndFrobenius_exact D l hl Ω X₀).1
  let := (zlIndFrobenius_exact D l hl Ω X₀).2.1
  let := (zlIndFrobenius_exact D l hl Ω X₀).2.2.1
  let := (zlIndFrobenius_exact D l hl Ω X₀).2.2.2
  let : Abelian (zlIndWeilHeart D l hl Ω X₀) := zlIndWeilHeartAbelian D l hl Ω X₀
  let : Preadditive (zlIndWeilHeart D l hl Ω X₀) :=
    (zlIndWeilHeartAbelian D l hl Ω X₀).toPreadditive
  let U := IsoAlgebra.forget (zlIndMap (zlSmallFrobenius D l hl Ω X₀))
  exact U.mapDerivedCategoryPlus

/-- Termwise derived inverse image. Source: exactness of the specified ind-pullback.
(blueprint: lem-zl-barrett-ind-realization). -/
def zlIndDerivedPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [HasDerivedCategory.{tX} (zlIndWeilHeart D l hl Ω X₀)]
    [HasDerivedCategory.{tY} (zlIndWeilHeart D l hl Ω Y₀)] (f : X₀ ⟶ Y₀) :
    DerivedCategory.Plus (zlIndWeilHeart D l hl Ω Y₀) ⥤
      DerivedCategory.Plus (zlIndWeilHeart D l hl Ω X₀) := by
  let := (zlIndWeilPull_exact D l hl Ω f).1
  let := (zlIndWeilPull_exact D l hl Ω f).2.1
  let := (zlIndWeilPull_exact D l hl Ω f).2.2
  exact (zlIndWeilPull D l hl Ω f).mapDerivedCategoryPlus

/-- Barrett realization followed by the exact Yoneda embedding in the ind-heart.
It is fully faithful, has represented cohomology, and commutes with inverse image
and free Frobenius induction. The represented derived objects detect isomorphisms
in the bounded-below ind-derived category.

Source: Barrett, The derived category of the abelian category of constructible sheaves,
arXiv:2005.10859, Theorem 1.1; Kashiwara--Schapira, Categories and Sheaves, §15.3;
SGA 4, XVII, finite-type constructible direct-image and open-cover descent.
(blueprint: lem-zl-barrett-ind-realization).

Proof: for a separated finite-type scheme over the geometric algebraically closed
field, Barrett identifies its constructible derived category with the bounded derived
category of the ordinary constructible heart. The exact Yoneda inclusion of a small
abelian category into its ind-category is fully faithful on bounded derived categories:
represent a roof by a bounded complex, and replace its finitely many objects, arrows,
and exactness relations by one finite stage of the filtered ind-presentations.
Its termwise extension preserves cohomology and gives the stated formula on heart
objects. Thus every cohomology object of the realization is represented.

These realizations commute with exact inverse image, since both are obtained by
applying inverse image to complexes and then localizing quasi-isomorphisms. The
comparison on the heart is the actual Yoneda Kan unit. Finite coefficient extension
has the same termwise compatibility. All the functors and comparisons therefore
descend to common stages. For a nonseparated finite-type scheme use a finite affine
open cover. All finite intersections are separated and quasi-compact. The finite
Cech resolutions glue the fully faithful realizations and their comparison maps;
normalization on the units makes the maps agree on overlaps.

For detection, a bounded-below complex right orthogonal to all shifts of represented
heart objects is zero: induct up from its lower cohomological bound, using the bottom
truncation and the fact that representables generate the ind-heart. Apply this to
the cone to obtain the displayed isomorphism test. Finally exact free induction is
the sum of all Frobenius iterates. Inverse image commutes with these sums and its
prescribed Frobenius square identifies every summand. The resulting comparison
is the last displayed natural isomorphism. Empty schemes, zero objects, and empty
sums use the same constructions. This statement uses no direct-image functor. -/
theorem zlBarrettIndRealization
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [HasDerivedCategory.{wX} (Ind (zlSmallHeart D l Ω hl X₀))]
    [HasDerivedCategory.{wY} (Ind (zlSmallHeart D l Ω hl Y₀))]
    [HasDerivedCategory.{tX} (zlIndWeilHeart D l hl Ω X₀)]
    [HasDerivedCategory.{tY} (zlIndWeilHeart D l hl Ω Y₀)] (f : X₀ ⟶ Y₀) :
    ∃ (JX : generalAlgebraicallyClosedConstructibleCategory l Ω
        (D.geometricFiber X₀).left ⥤
        DerivedCategory.Plus (Ind (zlSmallHeart D l Ω hl X₀)))
      (JY : generalAlgebraicallyClosedConstructibleCategory l Ω
        (D.geometricFiber Y₀).left ⥤
        DerivedCategory.Plus (Ind (zlSmallHeart D l Ω hl Y₀))),
      Nonempty JX.FullyFaithful ∧ Nonempty JY.FullyFaithful ∧
      (∀ A : zlSmallHeart D l Ω hl X₀,
        Nonempty (JX.obj (AsSmall.down.obj A).obj ≅
          (DerivedCategory.Plus.singleFunctor _ 0).obj (Ind.yoneda.obj A))) ∧
      (∀ (K : generalAlgebraicallyClosedConstructibleCategory l Ω
          (D.geometricFiber Y₀).left) (n : ℤ),
        ∃ A : zlSmallHeart D l Ω hl Y₀,
          Nonempty (Ind.yoneda.obj A ≅
            (DerivedCategory.Plus.homologyFunctor _ n).obj (JY.obj K))) ∧
      Nonempty (zlPull D l hl Ω f ⋙ JX ⋙ zlIndDerivedFree D l hl Ω X₀ ≅
        JY ⋙ zlIndDerivedFree D l hl Ω Y₀ ⋙ zlIndDerivedPull D l hl Ω f) ∧
      (∀ {M N : DerivedCategory.Plus (Ind (zlSmallHeart D l Ω hl Y₀))} (g : M ⟶ N),
        (∀ B, Function.Bijective (fun h : JY.obj B ⟶ M ↦ h ≫ g)) → IsIso g) := by
  obtain ⟨ha, hlim, hcolim, hadj, JX, JY, hX, hY, hheart, hcoh, hcover, ⟨e⟩⟩ :=
    zlBarrettOrdinaryIndRealization D l hl Ω f
  let L := zlIndMap (zlSmallPull D l hl Ω f)
  let : L.Additive := ha
  let : PreservesFiniteLimits L := hlim
  let : PreservesFiniteColimits L := hcolim
  let : L.IsLeftAdjoint := hadj
  have hfree : L.mapDerivedCategoryPlus ⋙ zlIndDerivedFree D l hl Ω X₀ ≅
      zlIndDerivedFree D l hl Ω Y₀ ⋙ zlIndDerivedPull D l hl Ω f := by
    obtain ⟨haX, hlX, hcX, heX⟩ := zlIndFrobenius_exact D l hl Ω X₀
    obtain ⟨haY, hlY, hcY, heY⟩ := zlIndFrobenius_exact D l hl Ω Y₀
    let := haX
    let := hlX
    let := hcX
    let := heX
    let := haY
    let := hlY
    let := hcY
    let := heY
    let : Abelian (zlIndWeilHeart D l hl Ω X₀) := zlIndWeilHeartAbelian D l hl Ω X₀
    let : Preadditive (zlIndWeilHeart D l hl Ω X₀) :=
      (zlIndWeilHeartAbelian D l hl Ω X₀).toPreadditive
    let : Abelian (zlIndWeilHeart D l hl Ω Y₀) := zlIndWeilHeartAbelian D l hl Ω Y₀
    let : Preadditive (zlIndWeilHeart D l hl Ω Y₀) :=
      (zlIndWeilHeartAbelian D l hl Ω Y₀).toPreadditive
    let FX := IsoAlgebra.Free.functor (zlIndMap (zlSmallFrobenius D l hl Ω X₀))
    let FY := IsoAlgebra.Free.functor (zlIndMap (zlSmallFrobenius D l hl Ω Y₀))
    let P := zlIndWeilPull D l hl Ω f
    let : FX.IsLeftAdjoint := (IsoAlgebra.Free.adjunction _).isLeftAdjoint
    let : FY.IsLeftAdjoint := (IsoAlgebra.Free.adjunction _).isLeftAdjoint
    let : FX.Additive := zlIndFree_additive D l hl Ω X₀
    let : FY.Additive := zlIndFree_additive D l hl Ω Y₀
    let : P.Additive := (zlIndWeilPull_exact D l hl Ω f).1
    let := (zlIndWeilPull_exact D l hl Ω f).2.1
    let := (zlIndWeilPull_exact D l hl Ω f).2.2
    have eFree : L ⋙ FX ≅ FY ⋙ P :=
      freeTransportIso _ _ L
        (zlIndSquare (zlSmallPull D l hl Ω f)
          (zlSmallFrobenius D l hl Ω Y₀) (zlSmallFrobenius D l hl Ω X₀)
          (zlSmallSquare D l hl Ω f))
    change L.mapDerivedCategoryPlus ⋙ FX.mapDerivedCategoryPlus ≅
      FY.mapDerivedCategoryPlus ⋙ P.mapDerivedCategoryPlus
    exact (Functor.mapDerivedCategoryPlusCompIso L FX).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso eFree ≪≫
      Functor.mapDerivedCategoryPlusCompIso FY P
  refine ⟨JX, JY, hX, hY, hheart, hcoh, ?_, ?_⟩
  · exact ⟨Functor.isoWhiskerRight e (zlIndDerivedFree D l hl Ω X₀) ≪≫
      Functor.associator JY L.mapDerivedCategoryPlus (zlIndDerivedFree D l hl Ω X₀) ≪≫
      Functor.isoWhiskerLeft JY hfree⟩
  · intro M N g hg
    apply CategoryTheory.indDerived_singleYoneda_detects_iso
      (zlSmallHeart D l Ω hl Y₀) g
    intro A n
    obtain ⟨B, ⟨i⟩⟩ := hcover A n
    constructor
    · intro a b hab
      apply (cancel_epi i.hom).1
      apply (hg B).injective
      simpa only [Category.assoc] using congrArg (fun h ↦ i.hom ≫ h) hab
    · intro a
      obtain ⟨b, hb⟩ := (hg B).surjective (i.hom ≫ a)
      change b ≫ g = i.hom ≫ a at hb
      refine ⟨i.inv ≫ b, ?_⟩
      change (i.inv ≫ b) ≫ g = a
      rw [Category.assoc, hb, Iso.inv_hom_id_assoc]

end WeilConjectures
