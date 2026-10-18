/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Sheaf.Paper.SupportedAffineLineHomotopy
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.RingTheory.GeometricallyRegularFieldExtension
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback

/-!
# Completion comparison for constant supported etale cohomology

Source: ILO, Travaux de Gabber, Expose XVII, proof of Lemma 3.6.3, printed p. 279,
formal base change (Fujiwara 1995, Corollary 6.6.4), and Corollary 4.2.3, p. 281
(blueprint: lem-per-completion-supported-constant-comparison).

The target coefficients use the canonical roots-of-unity comparison
`Scheme.etaleFiniteTwistPullback` to identify the inverse image with the signed
Tate sheaf on the completed spectrum. The support is the
scheme-theoretic inverse image of the closed point; for a Noetherian local ring its
residue field is canonically the original residue field. No geometric point is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The spectrum of the canonical maximal-ideal completion map.
Source: ILO XVII, proof of Lemma 3.6.3, completion reduction
(blueprint: lem-per-completion-supported-constant-comparison). -/
def localCompletionSpecMap (A : Type u) [CommRing A] [IsLocalRing A] :
    Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))

/-- The closed point as the spectrum of the quotient by the maximal ideal.
Source: ILO XVII, proof of Lemma 3.6.3, closed support
(blueprint: lem-per-completion-supported-constant-comparison). -/
abbrev localClosedPointImmersion (A : Type u) [CommRing A] [IsLocalRing A] :
    Spec (.of (A ⧸ IsLocalRing.maximalIdeal A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))

/-- The quotient closed point is a closed immersion.
Source: Stacks Tag 01IG; ILO XVII, proof of Lemma 3.6.3
(blueprint: lem-per-completion-supported-constant-comparison). -/
instance localClosedPointImmersion_isClosedImmersion (A : Type u)
    [CommRing A] [IsLocalRing A] : IsClosedImmersion (localClosedPointImmersion A) :=
  IsClosedImmersion.spec_of_quotient_mk (R := .of A) (IsLocalRing.maximalIdeal A)

/-- The normalized signed twist comparison family, extracted before specializing the schemes.
Its root-generator, unit, tensor-power and evaluation equations fix the canonical comparison.
Source: Stacks Tag 03PK; ILO XVII Corollary 4.2.3
(blueprint: lem-per-completion-supported-constant-comparison). -/
def completionTwistPullbackFamily (R : Type (u + 1)) [CommRing R] (N : ℕ)
    (hN : 0 < N) (hR : (N : R) = 0) :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
      IsUnit (N : Γ(X, ⊤)) → IsUnit (N : Γ(Y, ⊤)) → ∀ m : ℤ,
        (upperStar (ModuleCat.{u + 1} R) f).obj
          (Scheme.finiteEtaleTateSheaf R N X hR m) ≅
            Scheme.finiteEtaleTateSheaf R N Y hR m :=
  (Scheme.etaleFiniteTwistPullback R N hN hR).choose_spec.choose

/-- The canonical signed roots-of-unity comparison for completion. The selected family
is the published family fixed by the root generator, the unit, positive tensor powers,
and negative evaluation; thus it has no root-of-unity or basis choice.
Source: Stacks Tag 03PK; ILO XVII, completion reduction
(blueprint: lem-per-completion-supported-constant-comparison). -/
def localCompletionTwistIso (A : Type u) [CommRing A] [IsLocalRing A]
    (l : ℕ) (hl : l.Prime) (hunit : IsUnit (l : A)) (n : ℕ) (m : ℤ) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ n))))
      (localCompletionSpecMap A)).obj
        (Scheme.finiteEtaleTateSheaf (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
          (Spec (.of A)) (CharP.cast_eq_zero _ (l ^ n)) m) ≅
      Scheme.finiteEtaleTateSheaf (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
        (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
        (CharP.cast_eq_zero _ (l ^ n)) m :=
  completionTwistPullbackFamily (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
    (Nat.pow_pos hl.pos) (CharP.cast_eq_zero _ (l ^ n))
      (localCompletionSpecMap A)
      (Eq.mp (congrArg IsUnit (map_natCast (Scheme.ΓSpecIso (.of A)).inv.hom (l ^ n)))
        ((Eq.mp (congrArg IsUnit (Nat.cast_pow l n).symm) (hunit.pow n)).map
          (Scheme.ΓSpecIso (.of A)).inv.hom))
      (Eq.mp (congrArg IsUnit
        (map_natCast (Scheme.ΓSpecIso
          (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv.hom (l ^ n)))
        ((Eq.mp (congrArg IsUnit
          (map_natCast (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
            (l ^ n)))
          ((Eq.mp (congrArg IsUnit (Nat.cast_pow l n).symm) (hunit.pow n)).map
            (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))).map
          (Scheme.ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv.hom)) m


/-- The canonical supported pullback in integer degree, with the intrinsic target twist.
`ULift` only places the finite coefficient ring in the coefficient universe of the small
etale site. The support is the inverse-image closed
point, canonically the closed point of the completion. The kernel and its derived
pullback are the published ordinary etale constructions with their unit normalization.
Source: ILO XVII, Lemma 3.6.3 and Corollary 4.2.3; Stacks Tag 03PK
(blueprint: lem-per-completion-supported-constant-comparison). -/
def localCompletionSupportedPullback (A : Type u) [CommRing A] [IsLocalRing A]
    (l : ℕ) (hl : l.Prime) (hunit : IsUnit (l : A)) (n : ℕ) (q m : ℤ) :=
  (DerivedCategory.Plus.homologyFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ n)))) q).map
      ((affineSupportDerivedMap (ULift.{u + 1} (ZMod (l ^ n)))
        (localClosedPointImmersion A)
        (pullback.snd (localClosedPointImmersion A) (localCompletionSpecMap A))
        (localCompletionSpecMap A)
        (WeilConjectures.PurityFiniteSetting.affineSupportProjectionComplement
          (localClosedPointImmersion A) (localCompletionSpecMap A))).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
            (Spec (.of A)) (CharP.cast_eq_zero _ (l ^ n)) m)) ≫
        (affineSupportKernel (ULift.{u + 1} (ZMod (l ^ n)))
          (pullback.snd (localClosedPointImmersion A)
            (localCompletionSpecMap A))).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusSingleFunctor
            (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ n))))
              (localCompletionSpecMap A)) 0).hom.app
                (Scheme.finiteEtaleTateSheaf (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
                  (Spec (.of A)) (CharP.cast_eq_zero _ (l ^ n)) m) ≫
            (DerivedCategory.Plus.singleFunctor _ 0).map
              (localCompletionTwistIso A l hl hunit n m).hom))

/-- Completion preserves the canonical pullback on ordinary closed-supported etale
cohomology of every signed constant finite Tate twist, in every integer degree.
The inverse-image target twist and inverse-image closed point in the displayed map
are canonically the intrinsic twist and closed point of the completed spectrum.

Source: ILO XVII, proof of Lemma 3.6.3, printed p. 279, citing Fujiwara 1995,
Corollary 6.6.4; regular base change, ILO XVII Corollary 4.2.3, printed p. 281
(blueprint: lem-per-completion-supported-constant-comparison).

Proof plan (the seven steps of the node):
1. Completion is Noetherian by lem-weil-pbc-adic-completion-noetherian, local with
   maximal ideal m times the completion and the same residue field by
   lem-weil-pbc-local-completion-local-ring. The quotient closed immersions and
   affine tensor formula identify the inverse-image closed subscheme with that
   residue-field spectrum. Invertibility of l is preserved by the completion map.
2. Excellence gives the G-ring condition. Localization at m is A itself, so the
   completion map is flat with geometrically regular Noetherian fibres, using
   def-weil-pbc-g-ring and lem-weil-pbc-geometrically-regular-finitely-generated-extensions.
   The affine flatness criterion makes its spectrum a regular morphism.
3. lem-pur-etale-supported-kernel-adjunction identifies the kernel sheaf with
   i_* i!_0 and makes i_* exact and left adjoint to i!_0. Naturality in each scalar
   transports this to module sheaves; the exact faithful forgetful functor detects
   exactness. The Hom extension criterion shows i!_0 takes injectives to injectives.
4. Choose a bounded-below injective representative. Apply
   lem-weil-pbc-right-derived-plus-injective to identify supported derived sections
   with RΓ(s,i!K), with normalization given by inclusion of the supported kernel.
5. lem-per-regular-supported-base-change gives the canonical supported exchange
   isomorphism for the completion morphism and K = Lambda(m)[0].
   lem-asd-etale-finite-twist-pullback identifies its inverse-image coefficient with
   the intrinsic signed twist without choosing a root of unity.
6. On injective representatives the published supported pullback sends supported
   kernels into the pulled-back supported kernels. The derived adjunction of
   lem-trf-bounded-below-derived-adjunction identifies its transpose by the closed
   counit. The counit normalization of regular supported exchange therefore makes
   this map exactly the composite of residue-field pullback and supported exchange.
7. The residue-field morphism is an isomorphism, so both factors of that composite
   are isomorphisms. Apply degree-q homology. Negative degrees are included (both
   groups vanish). No regularity of A or finite-type hypothesis is used. -/
theorem isIso_localCompletionSupportedPullback
    (A : Type u) [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    (_hA : IsExcellent A) (l : ℕ) (hl : l.Prime) (hunit : IsUnit (l : A))
    (n : ℕ) (_hn : 1 ≤ n) (q m : ℤ) :
    IsIso (localCompletionSupportedPullback A l hl hunit n q m) := by
  sorry

end AlgebraicGeometry.Etale
