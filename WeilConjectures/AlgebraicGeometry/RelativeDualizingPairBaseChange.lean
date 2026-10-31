/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeDualizingPair
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCoherence
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion
import WeilConjectures.AlgebraicGeometry.AffineKFlatPullbackChartComparison
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietorisSupplement
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpen
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting

/-! # Arbitrary base change of supplied coherent relative dualizing pairs

Source: Stacks Project, duality.tex, Tag 0E2Y, lemma-base-change-relative-dualizing.
(blueprint: lem-sfb-relative-dualizing-pair-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits

noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The identity comparison normalized by the recorded pullback composition.
Source: Stacks 0D5S (blueprint: lem-sfb-relative-dualizing-pair-base-change). -/
@[irreducible] def relativeDualizingPullbackId (X : Scheme.{u}) :
    derivedPullback (𝟙 X) ≅ 𝟭 (schemeDerivedCategory X) := by
  let a : ∀ {A B : Scheme.{u}} (k : A ⟶ B), (Scheme.Modules.tensorPullback k).Additive :=
    fun k ↦ by
      rw [← recordedPullbackData_E k]
      exact recordedPullbackData_additive k
  exact (Classical.choose (derivedPullbackComposition_coherence a
    (fun k ↦ recordedDerivedPullbackCounit k)
    (fun k ↦ recordedDerivedPullbackCounit_universal k)
    (fun k P hP ↦ recordedDerivedPullbackCounit_kFlat k P hP)
    (fun p q ↦ recordedDerivedPullbackComposition p q) (fun p q ↦ rfl))) X

/-- The map on the two relative self-products induced by a commutative base square.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change). -/
def relativeDualizingProductMap {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (hs : p ≫ f = f' ≫ g) : pullback f' f' ⟶ pullback f f :=
  pullback.map f' f' f f p p g hs.symm hs.symm

/-- The induced product map carries the primed diagonal to the original diagonal.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change).
Proof: compose both sides with the two product projections; both composites are p.
The universal property of the fibre product proves equality. -/
theorem relativeDualizingProductMap_diagonal {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (hs : p ≫ f = f' ≫ g) :
    p ≫ pullback.diagonal f =
      pullback.diagonal f' ≫ relativeDualizingProductMap f f' g p hs := by
  sorry

/-- Ordinary diagonal base change followed by the structure-sheaf pullback map.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change). -/
def relativeDualizingOrdinaryDiagonalMap {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (hs : p ≫ f = f' ≫ g) :
    (Scheme.Modules.tensorPullback (relativeDualizingProductMap f f' g p hs)).obj
        (relativeDualizingDiagonalModule f) ⟶ relativeDualizingDiagonalModule f' :=
  Scheme.Modules.moduleBaseChangeMap (pullback.diagonal f) (pullback.diagonal f')
      (relativeDualizingProductMap f f' g p hs) p
      (relativeDualizingProductMap_diagonal f f' g p hs)
      (SheafOfModules.unit (moduleRings X.toRingedSpace)) ≫
    (Scheme.Modules.pushforward (pullback.diagonal f')).map
      (Scheme.Modules.tensorPullbackObjUnitToUnit p)

/-- The actual derived diagonal augmentation: the left-derived counit, then ordinary
base change. It is defined before asserting invertibility, with no choice of a map.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change). -/
def relativeDualizingDiagonalBaseChangeMap {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (hs : p ≫ f = f' ≫ g) :
    (derivedPullback (relativeDualizingProductMap f f' g p hs)).obj
        (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)) ⟶
      DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') :=
  (recordedDerivedPullbackCounit (relativeDualizingProductMap f f' g p hs)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (relativeDualizingDiagonalComplex f)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback (relativeDualizingProductMap f f' g p hs))
        (.up ℤ) 0).hom.app (relativeDualizingDiagonalModule f))) ≫
    (DerivedCategory.singleFunctor _ 0).map (relativeDualizingOrdinaryDiagonalMap f f' g p hs)

/-- The target comparison, using the actual first-projection equation.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change). -/
def relativeDualizingBaseChangeTarget {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (hs : p ≫ f = f' ≫ g) :
    derivedPullback (pullback.fst f f) ⋙
        derivedPullback (relativeDualizingProductMap f f' g p hs) ≅
      derivedPullback p ⋙ derivedPullback (pullback.fst f' f') :=
  recordedDerivedPullbackComposition
      (relativeDualizingProductMap f f' g p hs) (pullback.fst f f) ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) (pullback.lift_fst _ _ _)) ≪≫
      (recordedDerivedPullbackComposition (pullback.fst f' f') p).symm

/-- The canonical class pulled back along a commutative square whose diagonal
augmentation is invertible: invert that augmentation, pull back ξ, and compare targets.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change). -/
def relativeDualizingBaseChangeClass {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (hs : p ≫ f = f' ≫ g)
    (hd : IsIso (relativeDualizingDiagonalBaseChangeMap f f' g p hs))
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K) :
    DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj ((derivedPullback p).obj K) := by
  letI := hd
  exact inv (relativeDualizingDiagonalBaseChangeMap f f' g p hs) ≫
    (derivedPullback (relativeDualizingProductMap f f' g p hs)).map ξ ≫
      (relativeDualizingBaseChangeTarget f f' g p hs).hom.app K

/-- The canonical diagonal augmentation is invertible for arbitrary base change.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change).
Proof: both X and X ×_S X are flat over S. The common-base Tor-independence lemma
applies to the diagonal square. The diagonal is closed because f is separated.
Tor-independent derived base change on affine charts identifies the displayed
augmentation with the diagonal tensor augmentation; closed direct image is exact.
These comparisons glue by the naturality of the canonical base-change mate. -/
theorem relativeDualizingDiagonalBaseChangeMap_isIso
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f]
    (g : S' ⟶ S) (p : X' ⟶ X) (sq : IsPullback p f' f g) :
    IsIso (relativeDualizingDiagonalBaseChangeMap f f' g p sq.w) := by
  sorry

variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- A supplied coherent relative dualizing pair remains such under any base change.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change).
Proof, step 1: flatness, separatedness and local finite presentation persist under
base change. Relative-perfect base change preserves pseudo-coherence and locally
finite Tor dimension (lem-sfb-scheme-relative-perfect-base-change).
Step 2: the Tor-independent diagonal comparison is the canonical augmentation above.
The target comparison uses pullback composition and the first-projection equation.
Step 3: work on affine charts R → A and R → R'. Write B = A ⊗_R A. Affine
pseudo-coherence and Tor-amplitude criteria give a pseudo-coherent representative
M with finite R-Tor amplitude. Applying relative-perfect base change along f itself
bounds M ⊗_A^L B below; do the same after base change.
Step 4: the flat finite-presentation quotient lemma makes A[0] pseudo-coherent over B.
The affine class-evaluation comparison identifies the supplied sheaf multiplication
map with multiplication by the algebraic diagonal class, including that class itself.
Step 5: its invertibility says the class generates the rank-one degree-zero diagonal
Hom module. The algebraic diagonal-generator base-change lemma preserves this
property. Multiplication by the resulting generator is invertible in degree zero;
all other cohomology vanishes. Thus the primed class map is an isomorphism locally.
Step 6: these affine self-product opens cover a neighbourhood of the diagonal. On
its complement both the diagonal sheaf and its internal Hom vanish. Open restriction
of internal Hom and locality of vanishing of the cone give the global isomorphism. -/
theorem isCoherentRelativeDualizingPair_baseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f]
    (g : S' ⟶ S) (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (h : IsCoherentRelativeDualizingPair f K ξ) :
    IsCoherentRelativeDualizingPair (pullback.snd f g)
      ((derivedPullback (pullback.fst f g)).obj K)
      (relativeDualizingBaseChangeClass f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition
        (relativeDualizingDiagonalBaseChangeMap_isIso f (pullback.snd f g) g
          (pullback.fst f g) (IsPullback.of_hasPullback f g)) K ξ) := by
  sorry

/-- Identity base change preserves the specified class under the canonical object unit.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change).
Proof: the ordinary base-change mate of the identity square is the unit comparison.
The recorded derived counit gives the same comparison after localization. The two
unit laws for the recorded pullback composition identify the target comparison with
the first-projection pullback of the object unit. Substituting in the definition of
the base-changed class and cancelling the diagonal augmentation gives ξ. -/
theorem relativeDualizingBaseChangeClass_id
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f]
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K) :
    relativeDualizingBaseChangeClass f f (𝟙 S) (𝟙 X) (IsPullback.id_horiz f).w
        (relativeDualizingDiagonalBaseChangeMap_isIso f f (𝟙 S) (𝟙 X)
          (IsPullback.id_horiz f)) K ξ ≫
      (derivedPullback (pullback.fst f f)).map ((relativeDualizingPullbackId X).hom.app K) =
        ξ := by
  sorry

/-- Iterated base change preserves the specified class under the canonical object
composition comparison. Invertibility proofs merely permit writing the inverses;
the preceding diagonal theorem supplies them for every base-change square in the node.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-dualizing-pair-base-change).
Proof: horizontal pasting of the canonical diagonal base-change mates identifies
the composite augmentation with the pullback of the first augmentation followed by
the second. Its affine normalization is (a ⊗ r') ⊗ r'' ↦ a ⊗ k(r')r''. The two
target comparisons commute by associativity of recorded derived pullback composition.
Insert these identities in the definition, cancel the invertible augmentations,
and use functoriality on ξ. The displayed equality is the equality of the resulting
classes; recordedDerivedPullbackComposition q p is the corresponding object isomorphism. -/
theorem relativeDualizingBaseChangeClass_comp
    {X S X' S' X'' S'' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (f'' : X'' ⟶ S'')
    (g : S' ⟶ S) (p : X' ⟶ X) (sq : IsPullback p f' f g)
    (k : S'' ⟶ S') (q : X'' ⟶ X') (sq' : IsPullback q f'' f' k)
    (hd : IsIso (relativeDualizingDiagonalBaseChangeMap f f' g p sq.w))
    (hd' : IsIso (relativeDualizingDiagonalBaseChangeMap f' f'' k q sq'.w))
    (hd'' : IsIso (relativeDualizingDiagonalBaseChangeMap f f'' (k ≫ g) (q ≫ p)
      (sq'.paste_horiz sq).w))
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K) :
    relativeDualizingBaseChangeClass f' f'' k q sq'.w hd' ((derivedPullback p).obj K)
        (relativeDualizingBaseChangeClass f f' g p sq.w hd K ξ) ≫
      (derivedPullback (pullback.fst f'' f'')).map
        ((recordedDerivedPullbackComposition q p).hom.app K) =
      relativeDualizingBaseChangeClass f f'' (k ≫ g) (q ≫ p)
        (sq'.paste_horiz sq).w hd'' K ξ := by
  sorry

end AlgebraicGeometry
