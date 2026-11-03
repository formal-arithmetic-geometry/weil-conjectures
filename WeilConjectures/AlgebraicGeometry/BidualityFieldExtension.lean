/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom

import WeilConjectures.AlgebraicGeometry.IndEtaleQcqsDirectImageBaseChange
import WeilConjectures.AlgebraicGeometry.IndEtaleAffineNeighborhoods
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
import WeilConjectures.SixFunctors.ProEtale.GenericPoint
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.GeneralFieldFiniteVerdierPreservation
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.SingleReduction
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart
import WeilConjectures.AlgebraicGeometry.IndEtaleInternalHomComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric

/-!
# Verdier biduality under separable algebraic field extension

Source: the latest blueprint, `det-pd-biduality-field-extension`, and its proof.
The comparisons below are the actual adjunction mates and tensor-Hom comparison.
In particular, the last square uses the normalized double-dual arrow of
`lem-weil-duality-pairing`, not an arbitrary arrow with the same endpoints.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The evaluation fixed by the recorded ambient pairing, in the order DK tensor K.
Its value is determined by the descended Koszul symmetry and tensor-Hom adjunction.
Source: `lem-weil-duality-pairing`; blueprint `det-pd-biduality-field-extension`,
proof, evaluation paragraph. -/
noncomputable def fieldExtensionEvaluation
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u})
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (p : AmbientDualityPairing B X W)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((derivedTensor B X).obj (((derivedHom B X).obj (op K)).obj W)).obj K ⟶ W :=
  p.choose_spec.2.choose K

/-- The canonical comparison c_K: pull back internal Hom and then apply the
canonical dualizing comparison in its second variable. There is no choice of map.
Source: blueprint `det-pd-biduality-field-extension`, proof, evaluation paragraph. -/
noncomputable def fieldExtensionDualComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' S S' : Scheme.{u}} (g : X' ⟶ X)
    (a : X ⟶ S) (a' : X' ⟶ S') (b : S' ⟶ S)
    (sq : IsPullback g a' a b)
    [HasCompactification a] [HasCompactification a'] [QuasiCompact a']
    (K : DerivedCategoryModule A X) :
    (L((g)^*[ModuleCat.{u + 1} A])).obj ((verdierDual A a).obj (op K)) ⟶
      (verdierDual A a').obj (op ((L((g)^*[ModuleCat.{u + 1} A])).obj K)) :=
  derivedHomUpperStarComparison (ModuleCat.{u + 1} A) g K (dualizingComplex A a) ≫
    ((derivedHom (ModuleCat.{u + 1} A) X').obj
      (op ((L((g)^*[ModuleCat.{u + 1} A])).obj K))).map
        (dualizingComplexBaseChangeMap A sq)

/-- The clauses of the field-extension comparison, with their specified maps.
Direct image is asserted on D+ for qcqs maps of Noetherian schemes, and exceptional
restriction is asserted for closed immersions. Evaluation is an equality for the
normalized pairing. In the last square c_K and c_DK are isomorphisms, so the square
identifies the pulled-back delta with delta upstairs via their canonical composite.
Source: blueprint `det-pd-biduality-field-extension`, full statement and proof. -/
structure FieldExtensionBidualityComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' S S' : Scheme.{u}} (g : X' ⟶ X)
    (a : X ⟶ S) (a' : X' ⟶ S') (b : S' ⟶ S)
    (sq : IsPullback g a' a b)
    [HasCompactification a] [HasCompactification a'] [QuasiCompact a']
    (p : AmbientDualityPairing (ModuleCat.{u + 1} A) X (dualizingComplex A a))
    (p' : AmbientDualityPairing (ModuleCat.{u + 1} A) X' (dualizingComplex A a'))
    (K L : DerivedCategoryModule A X) : Prop where
  /-- Sheaf-level derived direct-image exchange along the field projection. -/
  directImage : ∀ (Y : Scheme.{u}) [IsNoetherian Y] (f : Y ⟶ X)
      [QuasiCompact f] [QuasiSeparated f] (M : DerivedCategoryModule A Y),
    (∃ m : ℤ, M.IsGE m) →
      IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback f g).toCommSq).app M)
  /-- The canonical mate for closed exceptional restriction. -/
  exceptional : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      (M : DerivedCategoryModule A X),
    (∃ m : ℤ, M.IsGE m) →
      IsIso ((rightDerivedUpperShriekBaseChangeMap A
        (IsPullback.of_hasPullback i g)).app M)
  /-- Internal Hom on the stated two bounded constructible finite-Tor complexes. -/
  internalHom : IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) g K L)
  /-- The dualizing comparison is the mate of compact-support exchange at the unit. -/
  dualizing : IsIso (dualizingComplexBaseChangeMap A sq)
  /-- The specified comparison for K, needed to identify double-dual objects. -/
  dualComparison : IsIso (fieldExtensionDualComparison A g a a' b sq K)
  /-- The specified comparison for DK, not merely an abstract isomorphism of objects. -/
  iteratedDualComparison : IsIso (fieldExtensionDualComparison A g a a' b sq
    ((verdierDual A a).obj (op K)))
  /-- Compatibility with evaluation in the order DK tensor K. -/
  evaluation : let G := L((g)^*[ModuleCat.{u + 1} A])
    letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) g
    ((derivedTensor (ModuleCat.{u + 1} A) X').map
        (fieldExtensionDualComparison A g a a' b sq K)).app (G.obj K) ≫
      fieldExtensionEvaluation (ModuleCat.{u + 1} A) X' p' (G.obj K) =
      Functor.LaxMonoidal.μ G ((verdierDual A a).obj (op K)) K ≫
        G.map (fieldExtensionEvaluation (ModuleCat.{u + 1} A) X p K) ≫
          dualizingComplexBaseChangeMap A sq
  /-- The actual normalized double-dual square, with the contravariant comparison
  in the correct direction. The preceding two isomorphism clauses make this the
  canonical transport of delta_K to delta_(g*K). -/
  doubleDual : let G := L((g)^*[ModuleCat.{u + 1} A])
    G.map (AmbientDualityPairing.bidualityMap (ModuleCat.{u + 1} A) X p K) ≫
        fieldExtensionDualComparison A g a a' b sq ((verdierDual A a).obj (op K)) =
      AmbientDualityPairing.bidualityMap (ModuleCat.{u + 1} A) X' p' (G.obj K) ≫
        ((derivedHom (ModuleCat.{u + 1} A) X').map
          (fieldExtensionDualComparison A g a a' b sq K).op).app (dualizingComplex A a')

attribute [local instance] _root_.DerivedCategory.symmetricCategory'

/-- The recorded evaluation is the native closed evaluation preceded by Koszul symmetry.
The identity-adjunct normalization determines it uniquely by cancellation of the symmetry.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionEvaluation_eq
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u})
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (p : AmbientDualityPairing B X W)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    fieldExtensionEvaluation B X p K =
      (β_ (((derivedHom B X).obj (op K)).obj W) K).hom ≫
        (ihom.ev K).app W := by
  let DK := ((derivedHom B X).obj (op K)).obj W
  have hb : ((p.choose.hom.app K).app DK) = (β_ K DK).hom :=
    eq_of_heq (p.choose_spec.1 K DK)
  have he := congrArg ((derivedTensorHomAdjunction B K).homEquiv DK W).symm
    (p.choose_spec.2.choose_spec.1 K)
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_id] at he
  change ((p.choose.hom.app K).app DK) ≫ fieldExtensionEvaluation B X p K =
    (ihom.ev K).app W at he
  rw [hb] at he
  apply (cancel_epi ((β_ K DK).hom)).mp
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  exact he

/-- The recorded transpose is the native double-dual map.
Substitute the evaluation normalization into its defining adjunction equation.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionBidualityMap_eq
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u})
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (p : AmbientDualityPairing B X W)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    AmbientDualityPairing.bidualityMap B X p K = MonoidalClosed.toIhomIhom W K := by
  change p.choose_spec.2.choose_spec.2.choose K = _
  calc
    p.choose_spec.2.choose_spec.2.choose K =
        (derivedTensorHomAdjunction B (((derivedHom B X).obj (op K)).obj W)).homEquiv K W
          (fieldExtensionEvaluation B X p K) := p.choose_spec.2.choose_spec.2.choose_spec.1 K
    _ = _ := by
      change MonoidalClosed.curry (fieldExtensionEvaluation B X p K) = _
      rw [fieldExtensionEvaluation_eq]
      rfl

/-- Evaluation is compatible with a lax braided functor and a map of dualizing objects.
Move the comparison past the braiding, then use naturality of evaluation and its mate equation.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionEvaluation_natural
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.LaxBraided]
    {W : C} {W' : D} (e : G.obj W ⟶ W') (K : C) :
    (MonoidalClosed.dualComparison G e K ▷ G.obj K) ≫
        (β_ ((ihom (G.obj K)).obj W') (G.obj K)).hom ≫
          (ihom.ev (G.obj K)).app W' =
      Functor.LaxMonoidal.μ G ((ihom K).obj W) K ≫
        G.map ((β_ ((ihom K).obj W) K).hom ≫
          (ihom.ev K).app W) ≫ e := by
  rw [BraidedCategory.braiding_naturality_left_assoc,
    MonoidalClosed.dualComparison, MonoidalCategory.whiskerLeft_comp_assoc,
    ihom.ev_naturality,
    Functor.LaxMonoidal.ihomComparison_ev_assoc,
    ← Functor.LaxBraided.braided_assoc, ← G.map_comp_assoc]

/-- Apply the formal evaluation calculation to derived pullback with its canonical tensorator.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionEvaluation_comparison
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X X' : Scheme.{u}} (g : X' ⟶ X)
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)}
    {W' : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology B)}
    (p : AmbientDualityPairing B X W) (p' : AmbientDualityPairing B X' W')
    (e : (L((g)^*[B])).obj W ⟶ W')
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    let G := L((g)^*[B])
    letI := leftDerivedUpperStarMonoidal B g
    ((derivedTensor B X').map
        (derivedHomUpperStarComparison B g K W ≫
          ((derivedHom B X').obj (op (G.obj K))).map e)).app (G.obj K) ≫
      fieldExtensionEvaluation B X' p' (G.obj K) =
        Functor.LaxMonoidal.μ G (((derivedHom B X).obj (op K)).obj W) K ≫
          G.map (fieldExtensionEvaluation B X p K) ≫ e := by
  let := leftDerivedUpperStarMonoidal B g
  let := leftDerivedUpperStarLaxBraidedOfPreservesFlat B g
  dsimp only
  rw [fieldExtensionEvaluation_eq, fieldExtensionEvaluation_eq]
  exact fieldExtensionEvaluation_natural L((g)^*[B]) e K

/-- Apply the lax braided double-dual square to the normalized recorded pairing.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionBidualityMap_comparison
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X X' : Scheme.{u}} (g : X' ⟶ X)
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)}
    {W' : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology B)}
    (p : AmbientDualityPairing B X W) (p' : AmbientDualityPairing B X' W')
    (e : (L((g)^*[B])).obj W ⟶ W')
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    let G := L((g)^*[B])
    let c := fun M ↦ derivedHomUpperStarComparison B g M W ≫
      ((derivedHom B X').obj (op (G.obj M))).map e
    G.map (AmbientDualityPairing.bidualityMap B X p K) ≫
        c (((derivedHom B X).obj (op K)).obj W) =
      AmbientDualityPairing.bidualityMap B X' p' (G.obj K) ≫
        ((derivedHom B X').map (c K).op).app W' := by
  let := leftDerivedUpperStarMonoidal B g
  let := leftDerivedUpperStarLaxBraidedOfPreservesFlat B g
  dsimp only
  rw [fieldExtensionBidualityMap_eq, fieldExtensionBidualityMap_eq]
  exact MonoidalClosed.map_toIhomIhom_comp_dualComparison L((g)^*[B]) e K

/-- Transport affine ind-etale direct-image exchange from D+ to the unbounded derived category.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionDirectImageCore
    (A : Type (u + 1)) [CommRing A]
    {X X' : Scheme.{u}} (g : X' ⟶ X) [IsAffineHom g]
    (hg : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) g)
    {Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (M : DerivedCategoryModule A Y) (hM : ∃ m : ℤ, M.IsGE m) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback f g).toCommSq).app M) := by
  exact (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f g).toCommSq ⟨M, hM⟩).2
      (isIso_derivedBaseChangeMapPlus_of_affine_locally_indEtale A f g
        (affine_indEtale_neighborhoods g hg) ⟨M, hM⟩)

/-- Apply ind-etale internal-Hom exchange after converting the constructibility conventions.
Use min of the lower and upper bounds to retain an ordered interval even for the zero complex.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionInternalHomCore
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' : Scheme.{u}} [IsNoetherian X] [IsNoetherian X']
    (g : X' ⟶ X) [IsAffineHom g]
    (hg : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) g)
    (K M : DerivedCategoryModule A X)
    (hK : DerivedCategory.boundedConstructibleFiniteTor A X K)
    (hM : ∃ m : ℤ, M.IsGE m) :
    IsIso (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) g K M) := by
  have hK' : DerivedCategory.isBoundedConstructible A X K := by
    rcases hK.1.1 with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hK.1.2 i), min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi
  exact (isIso_indEtaleInternalHomComparison A g hg K M hK' hK.2 hM).1

/-- Closed exceptional exchange follows from direct-image exchange on the open complement.
The localization comparison identifies the resulting map with the specified adjunction mate.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionExceptionalCore
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' : Scheme.{u}} [IsLocallyNoetherian X]
    (g : X' ⟶ X) [IsAffineHom g]
    (hg : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) g)
    {Z Z' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {i' : Z' ⟶ X'} {gZ : Z' ⟶ Z} [IsClosedImmersion i']
    (sq : IsPullback gZ i' i g)
    (M : DerivedCategoryModule A X) (hM : ∃ m : ℤ, M.IsGE m) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap A sq).app M) := by
  let U := openComplementOfIsClosedImmersion i
  have sqU := IsPullback.of_hasPullback U.ι g
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    simp [U, openComplementOfIsClosedImmersion]
  have hij' : Disjoint (Set.range i'.base) (Set.range (pullback.snd U.ι g).base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have h₁ : i.base (gZ.base x) = g.base (i'.base x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sq.w]
    have h₂ : U.ι.base ((pullback.fst U.ι g).base y) =
        g.base ((pullback.snd U.ι g).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sqU.w]
    have hm : i.base (gZ.base x) ∈ Set.range i.base := ⟨_, rfl⟩
    rw [hij, h₁, ← hy, ← h₂] at hm
    exact hm ⟨_, rfl⟩
  apply isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso A sq sqU hij hij' M
  apply fieldExtensionDirectImageCore A g hg U.ι
  obtain ⟨m, hm⟩ := hM
  let := hm
  exact ⟨m, isGE_leftDerivedUpperStar_obj (ModuleCat.{u + 1} A) U.ι M m⟩

/-- Factor an affine finite-type scheme as closed in affine space.
Closed exchange at the bounded-below smooth dualizing input and smooth exchange compose
to the specified exceptional mate by the canonical composition law.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionShriekAffine
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] [HasInvertibleExponent A (Spec (.of k))]
    {T X X' : Scheme.{u}} [IsAffine X]
    (b : T ⟶ Spec (.of k)) [IsAffineHom b]
    (hb : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) b)
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [HasCompactification f]
    {f' : X' ⟶ T} {g : X' ⟶ X} (sq : IsPullback g f' f b)
    [HasCompactification f'] [QuasiCompact f']
    (M : DerivedCategoryModule A (Spec (.of k)))
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) (Spec (.of k)) M) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap A sq).app M) := by
  obtain ⟨n, i, hi, hi'⟩ := exists_isClosedImmersion_affineSpace_of_isAffine f
  let P := 𝔸(ULift.{u} (Fin n); Spec (.of k))
  let p : P ⟶ Spec (.of k) := P ↘ Spec (.of k)
  let := hi'
  have : HasCompactification i := (Compactification.ofIsProper i).hasCompactification
  have : HasInvertibleExponent A P := .of_hom p
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have sqp := IsPullback.of_hasPullback p b
  have sqi := IsPullback.of_bot' (hi.symm ▸ sq) sqp
  have w' := sqp.lift_snd (g ≫ i) f' (by rw [Category.assoc, hi, sq.w])
  have : HasCompactification (pullback.snd p b) := .of_isPullback sqp
  have : HasCompactification (sqp.lift (g ≫ i) f'
      (by rw [Category.assoc, hi, sq.w])) := .of_isPullback sqi
  have : QuasiCompact (sqp.lift (g ≫ i) f'
      (by rw [Category.assoc, hi, sq.w])) := by
    have : QuasiCompact (sqp.lift (g ≫ i) f'
        (by rw [Category.assoc, hi, sq.w]) ≫ pullback.snd p b) := by
      rw [w']
      infer_instance
    exact .of_comp _ (pullback.snd p b)
  have : IsClosedImmersion (sqp.lift (g ≫ i) f'
      (by rw [Category.assoc, hi, sq.w])) :=
    MorphismProperty.of_isPullback sqi inferInstance
  have : IsAffineHom (pullback.fst p b) :=
    MorphismProperty.of_isPullback sqp.flip inferInstance
  have hgb : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) (pullback.fst p b) :=
    MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback sqp.flip hb
  have hpc := boundedConstructible_rightDerivedUpperShriek A (𝟙 _) p hM
  have hclosed := fieldExtensionExceptionalCore A (pullback.fst p b) hgb i sqi
    ((R(p)^![A]).obj M) hpc.1.1
  have hsmooth := (affineSpaceAdjunction_baseChange A n (Spec (.of k))).2 sqp
  exact (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff sqi sqp sq hi w' M
    hclosed).2 inferInstance

/-- Descend the exceptional comparison from affine opens.
Pull back the cover, apply the affine calculation to each chart, and use open locality.
Source: the proof of `det-pd-biduality-field-extension`
(blueprint: det-pd-biduality-field-extension). -/
private theorem fieldExtensionShriekCore
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] [HasInvertibleExponent A (Spec (.of k))]
    {T X X' : Scheme.{u}} (b : T ⟶ Spec (.of k)) [IsAffineHom b]
    (hb : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) b)
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    {f' : X' ⟶ T} {g : X' ⟶ X} (sq : IsPullback g f' f b)
    [HasCompactification f'] [QuasiCompact f']
    (M : DerivedCategoryModule A (Spec (.of k)))
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) (Spec (.of k)) M) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap A sq).app M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  have hopen (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨U, hU, hxU⟩
  choose V hV hxV using hopen
  have (x : X) : IsAffine (V x).toScheme := hV x
  have (x : X) : QuasiCompact (V x).ι := quasiCompact_of_compactSpace _
  have (x : X) : HasCompactification ((V x).ι ≫ f) :=
    HasCompactification.comp_of_isOpenImmersion f _
  have (x : X) : HasCompactification (pullback.snd (V x).ι g ≫ f') :=
    .of_isPullback ((IsPullback.of_hasPullback (V x).ι g).paste_vert sq)
  refine isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover sq (fun x ↦ (V x).ι)
    (fun x ↦ pullback.snd (V x).ι g) (fun x ↦ pullback.fst (V x).ι g)
    (fun x ↦ IsPullback.of_hasPullback _ _) (fun x' ↦ ?_) M (fun x ↦ ?_)
  · have hx' : x' ∈ Set.range (pullback.snd (V (g.base x')).ι g) := by
      rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι]
      exact hxV (g.base x')
    obtain ⟨y, hy⟩ := hx'
    exact ⟨_, y, hy⟩
  · exact fieldExtensionShriekAffine A b hb ((V x).ι ≫ f)
      ((IsPullback.of_hasPullback (V x).ι g).paste_vert sq) M hM

/-- Separable algebraic field extension preserves all the stated comparisons and
carries the specified double-dual morphism to the specified double-dual morphism.
The coefficient exponent and characteristic conditions spell out the blueprint's
standing finite-coefficient convention. Neither field is assumed finite or perfect.

Source: latest blueprint `det-pd-biduality-field-extension`, statement and proof.

Proof: Write the extension as the filtered union of its finite separable subfields.
Their spectra are finite etale. Exact pullback is monoidal and preserves Dctf.
At each finite stage the etale sum/evaluation adjunction and compact-support
composition identify the dualizing comparison with the transpose of the pulled-back
structural counit, hence with the displayed canonical mate. For the infinite union,
continuity on affine etale test objects gives the sheaf-level qcqs direct-image
exchange on bounded-below complexes. Apply this exchange to the open complement of
a closed immersion and its localization triangle: compatibility of the open unit
and the closed counit identifies the first arrow with the displayed exceptional
mate, and the other two arrows are invertible, so that mate is invertible too.
Locally embed an affine open of X into affine N-space. Its dualizing object is
Ri! A(N)[2N]; closed exchange and the unchanged twist and dimension after field
extension identify its pullback with the same formula upstairs. Trace/counit
normalization makes this local comparison the globally defined dualizing mate.
Stratified perfect devissage and the same continuity argument give internal-Hom
exchange for a Dctf first input and a bounded-below second input; apply it to L
and to the dualizing object. Verdier duality preserves Dctf independently of
biduality, so it also applies with first input DK. Transposing the pulled-back
evaluation gives exactly c_K, and monoidality gives the displayed evaluation
equality. Transpose this equality again, using the descended Koszul symmetry:
naturality in the first Hom variable gives the displayed square with D'(c_K).
The invertibility of c_K and c_DK identifies its two normalized double-dual arrows.
-/
theorem det_pd_biduality_field_extension
    (ell : ℕ) [Fact ell.Prime]
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell : A) ^ r = 0)
    {k₀ k' : Type u} [Field k₀] [Field k'] [Algebra k₀ k']
    [Fact (ringChar k₀ ≠ ell)] [Algebra.IsAlgebraic k₀ k'] [Algebra.IsSeparable k₀ k']
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k₀))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (K L : DerivedCategoryModule A X)
    (hK : DerivedCategory.boundedConstructibleFiniteTor A X K)
    (hL : DerivedCategory.boundedConstructibleFiniteTor A X L) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))
    let X' := pullback aX b
    let g : X' ⟶ X := pullback.fst aX b
    let aX' : X' ⟶ Spec (.of k') := pullback.snd aX b
    let sq : IsPullback g aX' aX b := IsPullback.of_hasPullback aX b
    letI : QuasiCompact aX' :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    letI : LocallyOfFiniteType aX' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
    letI : IsSeparated aX' :=
      MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
    letI : HasInvertibleExponent A (Spec (.of k₀)) := by
      obtain ⟨r, hr⟩ := hA
      refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, ?_, ?_⟩
      · simpa only [Nat.cast_pow] using hr
      · have hell : (ell : k₀) ≠ 0 := fun h ↦
          (Fact.out : ringChar k₀ ≠ ell)
            (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) h)
        have hu : IsUnit ((ell ^ r : ℕ) : k₀) := by
          simpa only [Nat.cast_pow] using hell.isUnit.pow r
        simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k₀)).inv.hom
    letI : HasInvertibleExponent A (Spec (.of k')) := .of_hom b
    letI : HasCompactification aX := (NagataCompactification aX).hasCompactification
    letI : HasCompactification aX' := (NagataCompactification aX').hasCompactification
    FieldExtensionBidualityComparison A g aX aX' b sq
      (ambient_duality_pairing A aX).1 (ambient_duality_pairing A aX').1 K L := by
  intro b X' g aX' sq
  let : QuasiCompact aX' := MorphismProperty.of_isPullback sq inferInstance
  let : LocallyOfFiniteType aX' := MorphismProperty.of_isPullback sq inferInstance
  let : IsSeparated aX' := MorphismProperty.of_isPullback sq inferInstance
  let : HasInvertibleExponent A (Spec (.of k₀)) := by
    obtain ⟨r, hr⟩ := hA
    refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hr
    · have hell : (ell : k₀) ≠ 0 := fun h ↦
        (Fact.out : ringChar k₀ ≠ ell)
          (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) h)
      have hu : IsUnit ((ell ^ r : ℕ) : k₀) := by
        simpa only [Nat.cast_pow] using hell.isUnit.pow r
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k₀)).inv.hom
  let : HasInvertibleExponent A (Spec (.of k')) := .of_hom b
  let : HasCompactification aX := (NagataCompactification aX).hasCompactification
  let : HasCompactification aX' := (NagataCompactification aX').hasCompactification
  have hb : proAffineEtale b :=
    proAffineEtale_Spec_iff.mpr ((RingHom.IndEtale.algebraMap_iff k₀ k').mpr
      (Algebra.IndEtale.of_isSeparable k₀ k'))
  have hb' : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) b :=
    by
      rcases hb with ⟨J, _, _, D, t, s, hs, hts⟩
      refine ⟨J, inferInstance, inferInstance, D, t, s, hs, ?_⟩
      intro j
      have : IsAffine (D.obj j) := (hts j).1.2.1
      exact ⟨⟨(hts j).1.1, @isAffineHom_of_isAffine (D.obj j) (Spec (.of k₀))
        (t.app j) inferInstance inferInstance⟩, (hts j).2⟩
  have hg : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) g :=
    MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback sq.flip hb'
  have : IsAffineHom g := MorphismProperty.of_isPullback sq.flip inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace aX'
  have : IsNoetherian X' := { __ := LocallyOfFiniteType.isLocallyNoetherian aX' }
  have hU : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A)
      (Spec (.of k₀)) (𝟙_ _) :=
    (DerivedCategory.boundedConstructible _ _).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0)
  have hω := boundedConstructible_rightDerivedUpperShriek A (𝟙 _) aX hU
  have hdual : IsIso (dualizingComplexBaseChangeMap A sq) :=
    (isIso_dualizingComplexBaseChangeMap_iff A sq).2
      (fieldExtensionShriekCore A b hb' aX sq (𝟙_ _) hU)
  have hHom (M : DerivedCategoryModule A X)
      (hM : DerivedCategory.boundedConstructibleFiniteTor A X M) :
      IsIso (fieldExtensionDualComparison A g aX aX' b sq M) := by
    have := fieldExtensionInternalHomCore A g hg M (dualizingComplex A aX) hM hω.1.1
    unfold fieldExtensionDualComparison
    infer_instance
  have hA' : ∃ r : ℕ, 1 ≤ r ∧ (ell ^ r : A) = 0 := by
    obtain ⟨r, hr⟩ := hA
    exact ⟨r + 1, by omega, by rw [pow_succ, hr, zero_mul]⟩
  have hDK := generalFieldFiniteVerdierPreservation ell A hA' aX hK
  refine ⟨?_, ?_, ?_, hdual, hHom K hK, hHom _ hDK, ?_, ?_⟩
  · intro Y _ f _ _ M hM
    exact fieldExtensionDirectImageCore A g hg f M hM
  · intro Z i _ M hM
    exact fieldExtensionExceptionalCore A g hg i (IsPullback.of_hasPullback i g) M hM
  · exact fieldExtensionInternalHomCore A g hg K L hK hL.1.1.1
  · exact fieldExtensionEvaluation_comparison (ModuleCat.{u + 1} A) g
      (ambient_duality_pairing A aX).1 (ambient_duality_pairing A aX').1
      (dualizingComplexBaseChangeMap A sq) K
  · exact fieldExtensionBidualityMap_comparison (ModuleCat.{u + 1} A) g
      (ambient_duality_pairing A aX).1 (ambient_duality_pairing A aX').1
      (dualizingComplexBaseChangeMap A sq) K

end AlgebraicGeometry.Etale
