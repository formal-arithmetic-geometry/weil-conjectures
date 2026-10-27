/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect

/-! # Perfect reconstruction over a surjective nil-kernel ring tower

Source: Stacks Project, More on Algebra, Tag 0CQG, lemma-Rlim-perfect-gives-perfect,
all-perfect case (blueprint: lem-sfb-nil-ring-perfect-derived-limit).

Index `n : ℕ` denotes the paper's level `n + 1`. Scalar extension is presented by its
adjunction to exact scalar restriction, as permitted by the node. Any presentation of
these left adjoints may be used: their unit-compatible unique isomorphisms identify
all the maps below. In particular, the associativity isomorphism is constructed from
the composite adjunction, rather than supplied as arbitrary comparison data.
The ring limit is specified by its compatible-tuple universal property; no adic
presentation is chosen. The localization universe `w` is independent of `u`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {R : ℕ → Type u} [∀ n, CommRing (R n)]
  {A : Type u} [CommRing A]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [∀ n, HasDerivedCategory.{w} (ModuleCat.{u} (R n))]
  (v : ∀ n, R (n + 1) →+* R n) (q : ∀ n, A →+* R n)
  (hq : ∀ n, q n = (v n).comp (q (n + 1)))

/-- The canonical identification of direct and successive restrictions of scalars.
Source: Stacks Project, Tags 0CQG and 07A6
(blueprint: lem-sfb-nil-ring-perfect-derived-limit).
It is the exact derived image of the identity-on-elements scalar restriction comparison. -/
def nilRingRestrictionComp (n : ℕ) :
    (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (v n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso
    (ModuleCat.restrictScalarsComp' (q (n + 1)) (v n) (q n) (hq n)) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The given transition, restricted to the limit ring using the canonical compositor.
Source: Stacks Project, Tag 0CQG
(blueprint: lem-sfb-nil-ring-perfect-derived-limit). -/
def nilRingTowerTransition
    (K : ∀ n, DerivedCategory (ModuleCat.{u} (R n)))
    (t : ∀ n, K (n + 1) ⟶ (ModuleCat.restrictScalars (v n)).mapDerivedCategory.obj (K n))
    (n : ℕ) :
    (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.obj (K (n + 1)) ⟶
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K n) :=
  (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
    (nilRingRestrictionComp v q hq n).inv.app (K n)

variable
  (L : ∀ n, DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} (R n)))
  (adj : ∀ n, L n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)

/-- The specified reduction map is the scalar-extension adjunct of the Roos projection.
Source: Stacks Project, Tag 0CQG, canonical reduction morphism
(blueprint: lem-sfb-nil-ring-perfect-derived-limit). -/
def nilRingLimitReduction
    (K : ∀ n, DerivedCategory (ModuleCat.{u} (R n)))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K n))]
    (T : DerivedCategory (ModuleCat.{u} A))
    (p : T ⟶ ∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K n))
    (n : ℕ) : (L n).obj T ⟶ K n :=
  ((adj n).homEquiv T (K n)).symm (p ≫ Pi.π _ n)

/-- Associativity of scalar extension, normalized by the composite scalar adjunction.
Source: Stacks Project, Tags 0CQG and 07A6
(blueprint: lem-sfb-nil-ring-perfect-derived-limit).
This is the unique isomorphism of left adjoints to the same exact restriction. -/
def nilRingExtensionAssoc
    (B : ∀ n, DerivedCategory (ModuleCat.{u} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (R n)))
    (badj : ∀ n, B n ⊣ (ModuleCat.restrictScalars (v n)).mapDerivedCategory)
    (n : ℕ) : L n ≅ L (n + 1) ⋙ B n :=
  Adjunction.leftAdjointUniq (adj n)
    (((adj (n + 1)).comp (badj n)).ofNatIsoRight
      (nilRingRestrictionComp v q hq n).symm)

/-- A compatible perfect tower over surjections with elementwise nilpotent kernels has a
perfect derived limit, with invertible canonical reductions, naturality, and transition
compatibility after the canonical scalar-extension associativity identification.

Source: Stacks Project, More on Algebra, Tag 0CQG, all-perfect case; naturality and
transition compatibility are adjuncts of the limiting projections, using Tag 07A6
(blueprint: lem-sfb-nil-ring-perfect-derived-limit).

Proof:
1. Each bounded finite-projective model is pseudo-coherent by the finite-free model
   criterion (lem-pc-pseudo-coherent-bounded-finite-free-model). Apply
   lem-sfb-nil-ring-pseudocoherent-derived-limit to obtain pseudo-coherence of T and
   invertibility of the actual projection adjuncts, not just abstract isomorphisms.
2. By lem-sfb-nil-ring-tower-limit-henselian, q 0 is surjective and its kernel lies in
   the Jacobson radical. Every maximal residue field therefore factors through R 0.
3. A bounded finite-projective model of K 0 is K-flat by
   lem-pc-module-bounded-flat-kflat and bounds its tensor cohomology uniformly in the
   coefficient module. No nonzero term is required; the zero model is allowed.
4. Choose a bounded-above finite-free model of T. K-flat scalar extension computes its
   reductions termwise (lem-pur-derived-change-of-rings). Tensor associativity and the
   isomorphism to K 0 identify every maximal residue fibre with the corresponding
   fibre of K 0. The uniform interval from step 3 and
   lem-weil-pbc-pseudocoherent-maximal-fibre-perfect give perfectness of T.
5. For naturality, the two sides have adjuncts u followed by the second projection,
   and the first projection followed by the restriction of the level map. These are
   equal by the assumed projection condition; use injectivity of the adjunction
   bijection (lem-pur-sheaf-ring-derived-coefficient-adjunction).
6. The first two Roos arrows compose to zero. Projecting gives p_n = t_n p_(n+1).
   Taking successive adjuncts identifies the right side with scalar extension of
   rho_(n+1) followed by gamma_n. The definition of nilRingExtensionAssoc identifies
   that composite adjunction with the direct one, giving the asserted equation. -/
theorem nilRingPerfectDerivedLimit
    (hsurj : ∀ n, Function.Surjective (v n))
    (hnil : ∀ n (x : R (n + 1)), x ∈ RingHom.ker (v n) → IsNilpotent x)
    (hring : ∀ (x : ∀ n, R n), (∀ n, v n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    (B : ∀ n, DerivedCategory (ModuleCat.{u} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (R n)))
    (badj : ∀ n, B n ⊣ (ModuleCat.restrictScalars (v n)).mapDerivedCategory)
    (K : ∀ n, DerivedCategory (ModuleCat.{u} (R n)))
    (t : ∀ n, K (n + 1) ⟶ (ModuleCat.restrictScalars (v n)).mapDerivedCategory.obj (K n))
    (hperfect : ∀ n, IsPerfectRingComplex (K n))
    (hbase : ∀ n, IsIso (((badj n).homEquiv (K (n + 1)) (K n)).symm (t n)))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K n))]
    (T : DerivedCategory (ModuleCat.{u} A))
    (p : T ⟶ ∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K n)) ⟶
      T⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle (nilRingTowerTransition v q hq K t) T p δ) :
    IsPerfectRingComplex T ∧
    (∀ n, IsIso (nilRingLimitReduction q L adj K T p n)) ∧
    (∀ n, nilRingLimitReduction q L adj K T p n =
      (nilRingExtensionAssoc v q hq L adj B badj n).hom.app T ≫
        (B n).map (nilRingLimitReduction q L adj K T p (n + 1)) ≫
          ((badj n).homEquiv (K (n + 1)) (K n)).symm (t n)) ∧
    ∀ (K' : ∀ n, DerivedCategory (ModuleCat.{u} (R n)))
      (t' : ∀ n, K' (n + 1) ⟶
        (ModuleCat.restrictScalars (v n)).mapDerivedCategory.obj (K' n)),
      (∀ n, IsPerfectRingComplex (K' n)) →
      (∀ n, IsIso (((badj n).homEquiv (K' (n + 1)) (K' n)).symm (t' n))) →
      ∀ [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K' n))]
        (T' : DerivedCategory (ModuleCat.{u} A))
        (p' : T' ⟶ ∏ᶜ fun n ↦
          (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K' n))
        (δ' : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (K' n)) ⟶
          T'⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (nilRingTowerTransition v q hq K' t') T' p' δ' →
        ∀ (φ : ∀ n, K n ⟶ K' n),
          (∀ n, t n ≫ (ModuleCat.restrictScalars (v n)).mapDerivedCategory.map (φ n) =
            φ (n + 1) ≫ t' n) →
          ∀ (f : T ⟶ T'),
            (∀ n, f ≫ p' ≫ Pi.π _ n = p ≫ Pi.π _ n ≫
              (ModuleCat.restrictScalars (q n)).mapDerivedCategory.map (φ n)) →
            ∀ n, (L n).map f ≫ nilRingLimitReduction q L adj K' T' p' n =
              nilRingLimitReduction q L adj K T p n ≫ φ n := by
  sorry

end DerivedCategory
