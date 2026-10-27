/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.CommonQuotientPullbackData
import all Sheaf.Paper.RingedCoefficientPullbackComparison
import Sheaf.Paper.CommonQuotientInsertionIdentity
import Sheaf.Paper.CommonQuotientInsertionComposition
import Sheaf.Paper.CommonQuotientInsertionFinite

/-! # Common quotient reduction of geometric scalar insertion

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, 0D6D;
sites-modules.tex, Tags 03D7, 03EK, 03EL.
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison).

The coefficient inverse image identifies R' with u^{-1}R and S'_n with u^{-1}S_n.
The latter identification is equivalent to the hypothesis that J'_n is generated
by u^{-1}J_n, by exactness of inverse image. Common quotients are specified by
locally surjective quotient projections and pushout squares, never by sectionwise
surjectivity. All comparisons retain their quotient-module action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections (Mod D)
open SheafOfModules.RingedCoefficientProjection
open SheafOfModules.SuccessiveDerivedQuotient (restriction sectionTensor)
namespace SheafOfModules.CommonQuotientPullback

universe uA vA wA uB vB wB uE vE wE

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : SuccessiveDerivedQuotient.Normalization (J := J) pY)
  (nX : SuccessiveDerivedQuotient.Normalization (J := K) pX)
  (e : Comparisons g nY nX)
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
  {B' : Sheaf K CommRingCat.{r}} (a : g.rings.obj B ⟶ B')


variable (Q : CommonQuotientTowerPresentation φ)
  (b : (Functor.const ℕᵒᵖ).obj B' ⟶ Q.S ⋙ g.rings)



private def ordinaryInsertion [PreservesFiniteLimits uInv] :
    ordinarySource g φ ⟶ ordinaryTarget g (pX := pX) φ a :=
  (restrictionIso g φ).hom ≫
    Functor.whiskerLeft (g.inverse B).modules
      (Functor.whiskerRight (nX.ordinaryAdjunction a).unit
        (restriction (g.rings.map φ))) ≫
    Functor.whiskerLeft (ordinaryPullback g (pX := pX) a)
      (nX.restrictionComp (g.rings.map φ) a).hom

private theorem ordinaryInsertion_sections [PreservesFiniteLimits uInv]
    (M : Mod J B) (U : Xᵒᵖ)
    (x : ((g.inverse R).modules.obj ((restriction φ).obj M)).val.obj U) :
    ((ordinaryInsertion g nX φ a).app M).val.app U x =
      sectionTensor (pX a) ((g.inverse B).modules.obj M) U 1
        (((g.inverse R).moduleUnderlying.hom.app ((restriction φ).obj M) ≫
          (g.inverse B).moduleUnderlying.inv.app M).hom.app U x) := by
  change ((nX.restrictionComp (g.rings.map φ) a).hom.app _).val.app U
    (((nX.ordinaryAdjunction a).unit.app _).val.app U
      (((restrictionIso g φ).hom.app M).val.app U x)) = _
  rw [nX.restrictionComp_sections, nX.ordinary_unit]
  rfl


private def sourceComputations :
    DerivedCategory.Qh ⋙ source g nY φ ⟶
      (ordinarySource g φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (nY.right_factors φ).hom (g.left R) ≫
    Functor.whiskerLeft ((restriction φ).mapHomotopyCategory (.up ℤ))
      (g.inverse R).modules.mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (F := restriction φ) (G := (g.inverse R).modules)
        (Iso.refl (ordinarySource g φ)) (.up ℤ)).hom) DerivedCategory.Qh

private def pullbackComputations :
    DerivedCategory.Qh ⋙ derivedPullback g (pX := pX) a ⟶
      (ordinaryPullback g (pX := pX) a).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (g.inverse B).modules.mapDerivedCategoryFactorsh.hom
      (pX a).derived ≫
    Functor.whiskerLeft ((g.inverse B).modules.mapHomotopyCategory (.up ℤ))
      (pX a).counit ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (F := (g.inverse B).modules) (G := (pX a).ordinary)
        (Iso.refl (ordinaryPullback g (pX := pX) a)) (.up ℤ)).hom) DerivedCategory.Qh

private def targetComputations :
    DerivedCategory.Qh ⋙ target g nX φ a ⟶
      (ordinaryTarget g (pX := pX) φ a).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (pullbackComputations g a) (nX.right (g.rings.map φ ≫ a)) ≫
    Functor.whiskerLeft
      ((ordinaryPullback g (pX := pX) a).mapHomotopyCategory (.up ℤ))
      (nX.right_factors (g.rings.map φ ≫ a)).hom ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (F := ordinaryPullback g (pX := pX) a)
        (G := restriction (g.rings.map φ ≫ a))
        (Iso.refl (ordinaryTarget g (pX := pX) φ a)) (.up ℤ)).hom) DerivedCategory.Qh

private theorem sourceComputations_app (H : HomotopyCategory (Mod J B) (.up ℤ)) :
    (sourceComputations g nY φ).app H = sourceComputation g nY φ H := by
  obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  rfl

private theorem targetComputations_app (H : HomotopyCategory (Mod J B) (.up ℤ)) :
    (targetComputations g nX φ a).app H = targetComputation g nX φ a H := rfl

private theorem targetComputation_isIso [PreservesFiniteLimits uInv]
    (P : CochainComplex (Mod J B) ℤ) (hk : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := B) (P.X i)) :
    IsIso (targetComputation g nX φ a ((HomotopyCategory.quotient _ _).obj P)) := by
  obtain ⟨hi, ht⟩ := inverse_preserves_flat g nX B P hk hf
  have hc := nX.computed a
    (((g.inverse B).modules.mapHomologicalComplex (.up ℤ)).obj P) hi ht
  change IsIso ((pX a).counit.app
    (((g.inverse B).modules.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ _).obj P))) at hc
  dsimp only [targetComputation, pullbackComputation]
  infer_instance


private theorem nonempty_insertion [PreservesFiniteLimits uInv] :
    Nonempty (Insertion g nY nX φ a) := by
  let P := flatHomotopy (J := J) B
  let L := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory (Mod J B) (.up ℤ) ⥤ D J B)
  let W := (HomotopyCategory.quasiIso (Mod J B) (.up ℤ)).inverseImage P.ι
  have : L.IsLocalization W := flat_localization (J := J) B
  let t := Functor.whiskerLeft P.ι (targetComputations g nX φ a)
  have ht (H : P.FullSubcategory) : IsIso (t.app H) :=
    targetComputation_isIso g nX φ a H.obj.as H.property.1 H.property.2
  have : ∀ H, IsIso (t.app H) := ht
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let et := asIso t
  let α : L ⋙ source g nY φ ⟶ L ⋙ target g nX φ a :=
    Functor.whiskerLeft P.ι (sourceComputations g nY φ) ≫
      Functor.whiskerLeft P.ι
        (Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (ordinaryInsertion g nX φ a) (.up ℤ))
          DerivedCategory.Qh) ≫ et.inv
  let FF := Localization.fullyFaithfulWhiskeringLeft L W (D K (g.rings.obj R))
  let δ : source g nY φ ⟶ target g nX φ a := FF.preimage α
  refine ⟨⟨ordinaryInsertion g nX φ a, ordinaryInsertion_sections g nX φ a, δ, ?_⟩⟩
  intro A hk hf
  let H : P.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj A, hk, hf⟩
  have hd : δ.app (L.obj H) = α.app H :=
    NatTrans.congr_app (FF.map_preimage α) H
  change δ.app (L.obj H) ≫ et.hom.app H = _
  rw [hd]
  dsimp only [α, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change (sourceComputations g nY φ).app H.obj ≫ _ = _
  rw [sourceComputations_app]
  rfl

private def reductionTransitions {A S T : Sheaf K CommRingCat.{r}}
    (q : A ⟶ S) (t : S ⟶ T) :
    restrictedReduction nX q ⟶ restrictedReduction nX (q ≫ t) :=
  Functor.whiskerRight
      (Functor.whiskerLeft (pX q).derived (nX.adjunction t).unit) (nX.right q) ≫
    Functor.whiskerLeft ((pX q).derived ⋙ (pX t).derived) (nX.rightComp q t).hom ≫
    Functor.whiskerRight (nX.derived q t).hom (nX.right (q ≫ t))

/-- The common-quotient comparison for an arbitrary geometric inverse image and flat
coefficient extensions. `R'` and `S'_n` have been identified with the inverse images
of `R` and `S_n`, as in the statement. The target quotient squares and the commuting
B-projections specify the compatible common quotients; no flatness of a is assumed.

Source: Stacks 06YY, 0G7E, 0D6D; sites-modules.tex 04JC, 03D7, 03EK, 03EL
(blueprint: lem-weil-pbc-ringed-common-quotient-pullback-comparison).

Proof:
1. Restriction of coefficient inverse image is identified with inverse image of
restriction. Compose this comparison with the normalized ordinary scalar-extension
unit and restriction compositor. On sections this inserts 1 into the scalar tensor.
2. On flat-term K-flat complexes the target computation is invertible. Compose the
ordinary insertion with the source computation and the inverse target computation.
Fully faithful whiskering along the resolving localization descends this to the
normalized derived insertion, with its required representative square.
3. Ordinary common-quotient insertion is invertible: quotient-tower comparisons
on both sites and coefficient inverse-image comparison identify both sides with
the same quotient module functor. The adjunction units identify the reduced map
with that isomorphism. Flat restriction and ringed pullback preserve the resolving
complexes, so the normalized counits transfer this to derived quotient reduction.
Use asIso for the finite comparison and the specified coefficient comparison for
its normalized inverse, retaining the actual quotient-module action.
4. The unit square is naturality of the quotient adjunction unit. The quotient
transition is a natural transformation built from the next unit and the scalar
and restriction compositors; its naturality gives the transition square.
5. The ordinary section formulas give unreduced insertion composition and identity
normalization. Their representative squares and resolving localization transfer
these to the derived category. Apply scalar extension to obtain both finite
coherence laws. No separate quotient-level coherence argument is required. -/
theorem nonempty_comparison [PreservesFiniteLimits uInv]
    (hflat : IsFlatOnSite (J := J) (R := R)
      ((restriction φ).obj (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))))
    (hflat' : IsFlatOnSite (J := K) (R := g.rings.obj R)
      ((restriction (g.rings.map φ ≫ a)).obj
        (unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B'))))
    (hquotient : ∀ n : ℕ, IsPushout (g.rings.map φ ≫ a)
      (quotient g φ Q n) (b.app (op n)) (𝟙 _))
    (hcompatible : ∀ n : ℕ, a ≫ b.app (op n) = g.rings.map (Q.extensionProjection n)) :
    ∃ c1 : Comparison g nY nX e φ a Q, Coherence g nY nX e φ a Q c1  := by
  classical
  obtain ⟨i⟩ := nonempty_insertion g nY nX φ a
  have hfinite (n : ℕ) :=
    insertion_finite_isIso g nY nX φ a Q b hflat hflat' hquotient hcompatible i n
  let f (n : ℕ) : finiteSource g nY φ Q n ≅ finiteTarget g nX φ a Q n :=
    asIso (Functor.whiskerRight i.derived (pX (quotient g φ Q n)).derived)
  let c : Comparison g nY nX e φ a Q :=
    { insertion := i
      finite := f
      reduced_insertion := fun _ ↦ rfl
      inverse := fun n ↦ (f n).symm ≪≫
        Functor.isoWhiskerLeft (nY.right φ) (e.derived (Q.projection n)).symm
      inverse_normalization := fun _ ↦ rfl
      units := fun n M ↦ ((nX.adjunction (quotient g φ Q n)).unit.naturality
        (i.derived.app M)).symm
      transitions := fun n M ↦
        (reductionTransitions nX (quotient g φ Q (n + 1))
          (g.rings.map (Q.S.map (homOfLE (Nat.le_succ n)).op))).naturality
            (i.derived.app M) }
  refine ⟨c, ?_⟩
  constructor
  · intro Z _ _ L vInv vPush vadj _ wInv wPush wadj g2 g12 pZ nZ B2 a2 a12 θ ρ
      i2 e12 c12 d
    have h := insertion_composition g nY nX φ a g2 g12 nZ a2 a12 θ ρ
      c.insertion i2 c12.insertion d
    refine ⟨h, ?_⟩
    intro n M
    rw [c12.reduced_insertion]
    change (pZ (quotient g12 φ Q n)).derived.map (c12.insertion.derived.app M) ≫
      (pZ (quotient g12 φ Q n)).derived.map (d.target.derived.hom.app M) = _
    rw [← Functor.map_comp, h M]
  · intro iInv iPush iadj g0 a0 θ0 ρ0 e0 c0 d
    have h := insertion_identity nY φ g0 a0 θ0 ρ0 c0.insertion d
    refine ⟨h, ?_⟩
    intro n M
    rw [c0.reduced_insertion]
    change (pY (quotient g0 φ Q n)).derived.map (d.source.derived.inv.app M) ≫
      (pY (quotient g0 φ Q n)).derived.map (c0.insertion.derived.app M) ≫
      (pY (quotient g0 φ Q n)).derived.map (d.target.derived.hom.app M) = _
    rw [← Functor.map_comp, ← Functor.map_comp, h M]
    exact (pY (quotient g0 φ Q n)).derived.map_id _

end SheafOfModules.CommonQuotientPullback
