/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.FlatLocalExtensionGivenResidueField
import Sheaf.RingTheory.PrincipalRegularLocalCompletionDVR
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.RingTheory.RaynaudFaltingsNormalizedReduction
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.RingTheory.DvrNormalGenericReducedSpecial
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Potentially smooth normalization of an affine group model

Source: Prasad--Yu, On quasi-reductive group schemes, Section 3.3, Proposition 3.4,
Appendix Corollary A.4 and Theorem A.6; the local-extension reductions in Section 5
and after Lemma A.9 (blueprint: lem-sfb-group-model-potential-smooth-normalization).

Scalar extension is a pullback. The coordinate algebra is written R tensor_A B,
canonically B tensor_A R; its integral closure is taken in its actual generic algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.PotentialSmoothNormalization

/-- The given affine scheme over its coefficient ring.
Source: Prasad--Yu, Section 3.3
(blueprint: lem-sfb-group-model-potential-smooth-normalization). -/
abbrev affineOver (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Over (Spec (.of A)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- The canonical scalar arrow on spectra.
Source: Prasad--Yu, Appendix A.4
(blueprint: lem-sfb-group-model-potential-smooth-normalization). -/
abbrev scalarArrow (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] :
    Spec (.of R) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A R))

/-- The scalar-extended coordinate ring, with the new scalars on the left.
Source: Prasad--Yu, Appendix A.4
(blueprint: lem-sfb-group-model-potential-smooth-normalization). -/
abbrev coordinateBase (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] := R ⊗[A] B

/-- The generic coordinate ring of the extended model.
Source: Prasad--Yu, Appendix A.4
(blueprint: lem-sfb-group-model-potential-smooth-normalization). -/
abbrev coordinateGeneric (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [IsDomain R] [Algebra A B] [Algebra A R] :=
  (coordinateBase A B R) ⊗[R] (FractionRing R)

/-- The prescribed integral closure: elements of the generic ring integral over B_R.
Source: Prasad--Yu, Appendix A.4
(blueprint: lem-sfb-group-model-potential-smooth-normalization). -/
abbrev coordinateClosure (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [IsDomain R] [Algebra A B] [Algebra A R] :=
  integralClosure (coordinateBase A B R) (coordinateGeneric A B R)

/-- The spectrum of the actual integral closure, over the extended base.
Source: Prasad--Yu, Appendix A.4
(blueprint: lem-sfb-group-model-potential-smooth-normalization). -/
abbrev normalizedModel (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [IsDomain R] [Algebra A B] [Algebra A R] : Over (Spec (.of R)) :=
  affineOver R (coordinateClosure A B R)

/-- The normalization arrow, induced by B -> B_R -> C and the structure map to R.
Source: Prasad--Yu, Appendix A.4
(blueprint: lem-sfb-group-model-potential-smooth-normalization). -/
def normalizationArrow (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
    [IsDomain R] [Algebra A B] [Algebra A R] :
    normalizedModel A B R ⟶ (Over.pullback (scalarArrow A R)).obj (affineOver A B) :=
  Over.homMk (pullback.lift
    (Spec.map (CommRingCat.ofHom
      ((algebraMap (coordinateBase A B R) (coordinateClosure A B R)).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] coordinateBase A B R).toRingHom)))
    (normalizedModel A B R).hom (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      apply congrArg (fun f : CommRingCat.of A ⟶
        CommRingCat.of (coordinateClosure A B R) => Spec.map f)
      ext a
      simp [coordinateBase]))
    (by exact pullback.lift_snd _ _ _)

/-- After an injective local extension to a henselian DVR with the specified algebraically
closed residue field, the prescribed finite normalization is a smooth group model.

Source: Prasad--Yu, Section 3.3, Proposition 3.4, Appendix Corollary A.4 and Theorem A.6;
local-extension reductions in Section 5 and after Lemma A.9
(blueprint: lem-sfb-group-model-potential-smooth-normalization).

Proof plan:
1. Apply flat-local-extension-given-residue-field with the specified algebraic closure.
   A uniformizer remains regular by flatness. Principal-regular-local-completion-dvr
   gives a complete DVR D with that residue field and an injective local map from A.
2. Base change B to D. Smooth-geometrically-normal makes its generic fibre normal;
   raynaud-faltings-normalized-reduction gives a finite fraction-field extension L
   and the finite, flat integral closure C with geometrically reduced special fibre.
3. Complete-local-nagata makes the integral closure R of D in L finite. By
   finite-over-complete-local-product it is complete local; finite-normalization-local-dvr
   identifies it as a DVR with fraction field L, without separability. The residue extension
   of the specified algebraically closed field is finite, hence trivial. Complete-pair-
   henselian gives henselianity. This constructs the required compatible local injection.
4. The tensor square of C is flat, with normal generic fibre by smooth-geometrically-normal
   and reduced special fibre by flat-geometrically-reduced-pullback. Finite-type-algebra-
   noetherian and dvr-normal-generic-reduced-special give normality of C and its tensor square.
5. Apply generic comultiplication and inversion to monic equations for elements of C.
   Their values are integral, hence lie in the tensor square and C respectively.
   The generic counit lands in R by pid-noetherian-normal. Restrict these actual maps.
6. All group diagrams hold after localization and descend through the injective localization
   maps of the flat tensor powers. Compatibility on B_R makes normalization a homomorphism;
   its generic fibre is the canonical isomorphism of step 2.
7. Geometrically-reduced-group-smooth makes the special fibre smooth. Finite-type-noetherian-
   finite-presentation and smooth-criterion then give smoothness over R. Affineness and finite
   type come from the coordinate construction.
8. Integral-injective-lying-over gives surjectivity. Primes over special-fibre primes contain
   the extended maximal ideal, giving special-fibre surjectivity without quotient injectivity.
   Finite module generators reduce to finite generators on the special fibre. No excellence
   assumption on A was used.
-/
theorem exists_potential_smooth_normalization
    (A B : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] [Module.Flat A B]
    [GrpObj (affineOver A B)]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (Ω : Type u) [Field Ω] [Algebra (IsLocalRing.ResidueField A) Ω]
    [IsAlgClosure (IsLocalRing.ResidueField A) Ω]
    (hsm : Smooth ((Over.pullback (scalarArrow A K)).obj
      (affineOver A B)).hom)
    (hconn : GeometricallyConnected ((Over.pullback (scalarArrow A K)).obj
      (affineOver A B)).hom) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : HenselianLocalRing R) (_ : Algebra A R) (_ : IsLocalHom (algebraMap A R)),
      Function.Injective (algebraMap A R) ∧
      ∃ e : IsLocalRing.ResidueField R ≃+* Ω,
        e.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap A R)) =
          algebraMap (IsLocalRing.ResidueField A) Ω ∧
        Module.Finite (coordinateBase A B R) (coordinateClosure A B R) ∧
        ∃ (_ : GrpObj (normalizedModel A B R)),
          IsMonHom (normalizationArrow A B R) ∧
          Smooth (normalizedModel A B R).hom ∧
          IsAffine (normalizedModel A B R).left ∧
          LocallyOfFiniteType (normalizedModel A B R).hom ∧
          QuasiCompact (normalizedModel A B R).hom ∧
          IsIso ((Over.pullback (scalarArrow R (FractionRing R))).map
            (normalizationArrow A B R)) ∧
          IsFinite (normalizationArrow A B R).left ∧
          Surjective (normalizationArrow A B R).left ∧
          Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom
            (e.toRingHom.comp (IsLocalRing.residue R))))).obj
              (normalizedModel A B R)).hom ∧
          IsAffine ((Over.pullback (Spec.map (CommRingCat.ofHom
            (e.toRingHom.comp (IsLocalRing.residue R))))).obj
              (normalizedModel A B R)).left ∧
          LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom
            (e.toRingHom.comp (IsLocalRing.residue R))))).obj
              (normalizedModel A B R)).hom ∧
          QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
            (e.toRingHom.comp (IsLocalRing.residue R))))).obj
              (normalizedModel A B R)).hom ∧
          IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom
            (e.toRingHom.comp (IsLocalRing.residue R))))).map
              (normalizationArrow A B R)).left ∧
          Surjective ((Over.pullback (Spec.map (CommRingCat.ofHom
            (e.toRingHom.comp (IsLocalRing.residue R))))).map
              (normalizationArrow A B R)).left := by
  sorry

end AlgebraicGeometry.PotentialSmoothNormalization
