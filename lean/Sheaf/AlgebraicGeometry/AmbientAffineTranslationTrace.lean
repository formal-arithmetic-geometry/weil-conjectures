/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.AffineTraceTower
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.LocallyConstant.Basic
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Compactification.Noetherian

/-!
# Translation invariance of the affine-space trace

Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md, Step 1
(blueprint: lem-trf-ambient-affine-translation-trace).

We use the recorded coordinate-tower presentation of affine space and of its
shifted Tate complex. All action maps are constructed from the existing
proper/open exchange and the normalized roots-of-unity pullback comparisons.
No trace, exchange, or coefficient identification is an arbitrary parameter.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Package the existing affine translation and its opposite as an isomorphism.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationIso (B : Scheme.{u}) (b : PUnit.{u + 1} → Γ(B, ⊤)) :
    AffineSpace PUnit.{u + 1} B ≅ AffineSpace PUnit.{u + 1} B where
  hom := AffineSpace.translation b
  inv := AffineSpace.translation (-b)
  hom_inv_id := (AffineSpace.translation_add b (-b)).symm.trans
    (congrArg AffineSpace.translation (add_neg_cancel b) |>.trans AffineSpace.translation_zero)
  inv_hom_id := (AffineSpace.translation_add (-b) b).symm.trans
    (congrArg AffineSpace.translation (neg_add_cancel b) |>.trans AffineSpace.translation_zero)

/-- The translation `z ↦ z-a` in the coordinate-tower model. Restrict the vector
at each step to its first coordinates, translate the last affine line, and apply
functoriality to the previous stages. This uses the upstream translation.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslation (S : Scheme.{u}) :
    (d : ℕ) → (a : Fin d → Γ(S, ⊤)) → (affineTraceTower S d ≅ affineTraceTower S d)
  | 0, _ => Iso.refl S
  | d + 1, a =>
    ambientAffineTranslationIso (affineTraceTower S d)
      (fun _ ↦ -(affineTraceProjection S d).appTop (a (Fin.last d))) ≪≫
      (AffineSpace.functor.obj (Opposite.op PUnit.{u + 1})).mapIso
        (ambientAffineTranslation S d (fun i ↦ a i.castSucc))

/-- The cartesian square of a coordinate projection under translation. It is
cartesian because both horizontal morphisms are the explicit translation
isomorphisms. Its commutativity follows from `translation_over`, `map_over`,
and the recursive definition; these are equalities of the actual scheme maps.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace).
Proof: the last-coordinate translation is over the preceding tower stage;
functoriality of affine space makes the other factor lie over the preceding
translation. Compose these equations and use the isomorphism-square criterion.
-/
theorem ambientAffineTranslation_lineSquare (S : Scheme.{u}) (d : ℕ)
    (a : Fin (d + 1) → Γ(S, ⊤)) :
    IsPullback (ambientAffineTranslation S (d + 1) a).hom
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom := by
  sorry

/-- Expand the recorded affine-line right functor into its ordinary pulled-back
input and its shifted finite Tate line. This is tensor pullback followed by the
canonical inverse-image composition and the normalized finite-line comparison.
Source: Step 1 and sk-prop-an, Step 5(b)
(blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineLineRightExpansion (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (B : Scheme.{u}) (hB : IsUnit (N : Γ(B, ⊤))) (K : DerivedCategoryModule A B) :
    (affineTraceLineRight A N hA B).obj K ≅
      (ordinaryFiniteTwistedPullback A (AffineSpace PUnit.{u + 1} B ↘ B)
        ((ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} B))⟦(2 : ℤ)⟧)).obj K :=
  ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart B)
      ((ordinaryFinitePullback A (ProjectiveLine B ↘ B)).obj K)
      ((ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧) ≪≫
    ordinaryFiniteTensorRightMapIso A (AffineSpace PUnit.{u + 1} B)
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart B)
        (ProjectiveLine B ↘ B) (AffineSpace PUnit.{u + 1} B ↘ B)
        (ProjectiveLine.affineChart_over B).symm).symm.app K)
      (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine.affineChart B)
        (affineTraceProjectiveInvertible N B hB))

/-- The Tate identification for one coordinate square, constructed from tensor
pullback, the actual commutative square, and the normalized finite-line transport.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineLineRightSquare (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {B B' : Scheme.{u}} (f : B' ⟶ B)
    (g : AffineSpace PUnit.{u + 1} B' ⟶ AffineSpace PUnit.{u + 1} B)
    (w : g ≫ (AffineSpace PUnit.{u + 1} B ↘ B) =
      (AffineSpace PUnit.{u + 1} B' ↘ B') ≫ f)
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (K : DerivedCategoryModule A B) :
    (ordinaryFinitePullback A g).obj ((affineTraceLineRight A N hA B).obj K) ≅
      (affineTraceLineRight A N hA B').obj ((ordinaryFinitePullback A f).obj K) :=
  (ordinaryFinitePullback A g).mapIso (ambientAffineLineRightExpansion A N hA t B hB K) ≪≫
    ordinaryFiniteTwistedPullbackComparison A
      (AffineSpace PUnit.{u + 1} B ↘ B) (AffineSpace PUnit.{u + 1} B' ↘ B') f g
      ((ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} B))⟦(2 : ℤ)⟧)
      ((ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} B'))⟦(2 : ℤ)⟧) K
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g
        (AffineSpace PUnit.{u + 1} B ↘ B)).symm.app K ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} B' ↘ B') f _ w).app K)
      (ordinaryFiniteShiftedLinePullback A N hA t g (affineTraceInvertible N B hB 1)) ≪≫
    (ambientAffineLineRightExpansion A N hA t B' hB'
      ((ordinaryFinitePullback A f).obj K)).symm

/-- One explicit pasting step for the normalized Tate identification. The last
argument is the preceding coordinate identification, not independently chosen data.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationTateStep (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (a : Fin (d + 1) → Γ(S, ⊤))
    (e : (ordinaryFinitePullback A
      (ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) :
    (ordinaryFinitePullback A (ambientAffineTranslation S (d + 1) a).hom).obj
        ((affineTraceLineRight A N hA (affineTraceTower S d)).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ≅
      (affineTraceLineRight A N hA (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) :=
  ambientAffineLineRightSquare A N hA t
      (ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom
      (ambientAffineTranslation S (d + 1) a).hom
      (ambientAffineTranslation_lineSquare S d a).w
      (affineTraceInvertible N S hS d) (affineTraceInvertible N S hS d)
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≪≫
    (affineTraceLineRight A N hA (affineTraceTower S d)).mapIso e

/-- The normalized Tate pullback identification on the coordinate-tower complex
`A(d)[2d]`, assembled one shifted Tate line at a time. The zero-dimensional
identification is the constant-sheaf identity comparison.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationTate (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → (a : Fin d → Γ(S, ⊤)) →
    ((ordinaryFinitePullback A (ambientAffineTranslation S d a).hom).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
  := Nat.rec (motive := fun d ↦ (a : Fin d → Γ(S, ⊤)) →
      ((ordinaryFinitePullback A (ambientAffineTranslation S d a).hom).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
        (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)))
    (fun _ ↦ ordinaryFiniteUnitPullback A (𝟙 S))
    (fun d r a ↦ ambientAffineTranslationTateStep A N hA t S hS d a
      (r (fun i ↦ a i.castSucc)))

/-- The canonical line exchange is the recorded proper/open exchange for the
translation square, followed by the recorded compactification comparison back
to the standard affine chart. No arbitrary endomorphism is supplied.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationLineExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) (d : ℕ) (a : Fin (d + 1) → Γ(S, ⊤))
    (M : DerivedCategoryModule A (affineTraceTower S (d + 1))) :
    (ordinaryFinitePullback A
      (ambientAffineTranslation S d (fun i ↦ a i.castSucc)).hom).obj
        ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ⟶
      (affineTraceLineLeft A (affineTraceTower S d)).obj
        ((ordinaryFinitePullback A (ambientAffineTranslation S (d + 1) a).hom).obj M) :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      (ambientAffineTranslation_lineSquare S d a)
      (affineTraceLineCompactification (affineTraceTower S d))).app M ≫
    (rightDerivedLowerShriekOfCompactificationIso A
      ((affineTraceLineCompactification (affineTraceTower S d)).ofIsPullback
        (ambientAffineTranslation_lineSquare S d a))
      (affineTraceLineCompactification (affineTraceTower S d))).hom.app _

/-- The compact-support exchange for translation, pasted along the coordinate
compactifications. At rank zero insert only the canonical identity inverse-image
comparison. The unbounded comparison dependency identifies this pasting with
its compactification-independent exchange, on these bounded-below inputs.
Source: Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTranslationExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) : (d : ℕ) → (a : Fin d → Γ(S, ⊤)) →
    (M : DerivedCategoryModule A (affineTraceTower S d)) →
    (affineTraceLeft A S d).obj M ⟶
      (affineTraceLeft A S d).obj
        ((ordinaryFinitePullback A (ambientAffineTranslation S d a).hom).obj M)
  | 0, _, M =>
    (unboundedEtaleUpperStarIdIso A S).inv.app M ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S)).inv.app M
  | d + 1, a, M =>
    ambientAffineTranslationExchange A S d (fun i ↦ a i.castSucc)
        ((affineTraceLineLeft A (affineTraceTower S d)).obj M) ≫
      (affineTraceLeft A S d).map (ambientAffineTranslationLineExchange A S d a M)

/-- The normalized twist transport supplied by the trace dependency. Its roots
inclusion and pure-tensor normalizations determine its maps uniquely; this is
not a choice of an unnormalized Tate trivialization.
Source: sk-prop-an and Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTraceTransport (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    OrdinaryFiniteTwistTransport A N hA :=
  Classical.choose (exists_affineSpaceTopTrace N hN A hA)

/-- The specified normalized projective-line data used in the coordinate counit.
The Kummer Chern map, decomposition components, and counit normalization determine
this data up to the equality of trace maps used here. No free trace is chosen.
Source: sk-prop-an and Step 1 (blueprint: lem-trf-ambient-affine-translation-trace). -/
def ambientAffineTraceDatum (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA (ambientAffineTraceTransport N hN A hA) T hT :=
  Classical.choose (Classical.choose_spec (exists_affineSpaceTopTrace N hN A hA))

/-- Translation preserves the actual coordinate-tower counit trace.
Source: main-20261015, sk-prop-sp-orientation-vector-bundle.proof.md, Step 1
(blueprint: lem-trf-ambient-affine-translation-trace).
Proof:
1. Form the universal translation over P = affine d-space over S. The coordinate
   tower gives Noetherian stages and preserves invertibility of N. Nagata and
   finite-type Noetherianity give the allowed compactifications.
2. Apply the compact-support action/base-change lemma and the unbounded comparison
   normalization to the shifted Tate sheaf. The trace dependency gives the actual
   counit isomorphism and its base-change equation; Tate transport composes.
3. Conjugate this action by the trace. Degree-zero full faithfulness identifies
   the resulting endomorphism of the constant complex with a module-sheaf map.
   Linearity makes it multiplication by a section b. Its inverse makes b a unit,
   including for A = 0. The constant-sheaf lemma makes b locally constant.
4. Every residue-field affine fibre is a nonempty integral spectrum, hence
   connected, including in rank zero. The identity normalization makes b = 1
   along the zero section. Thus it is one on every fibre and on all of P.
5. Specialize along a. The action and trace base-change equations identify the
   specialization with the displayed concrete exchange and Tate map. Cancel the
   base-change isomorphism to obtain the equality of actual derived morphisms.
   Rank zero uses only identity comparisons; the empty base is also included.
-/
theorem ambientAffineTranslationTrace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (a : Fin d → Γ(S, ⊤)) :
    ambientAffineTranslationExchange A S d a
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
      (affineTraceLeft A S d).map
        (ambientAffineTranslationTate A N hA (ambientAffineTraceTransport N hN A hA)
          S hS d a).hom ≫
      affineTraceCounit A N hA (ambientAffineTraceTransport N hN A hA)
        (ambientAffineTraceDatum N hN A hA) S hS d =
      affineTraceCounit A N hA (ambientAffineTraceTransport N hN A hA)
        (ambientAffineTraceDatum N hN A hA) S hS d := by
  sorry

end AlgebraicGeometry.Etale
