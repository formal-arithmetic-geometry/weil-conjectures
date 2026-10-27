/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.SixFunctors.ListedCoefficientMaps
public import Sheaf.SixFunctors.ScalarDirectImageMateCoherence
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstantModelTorAmplitude

/-! # The elementary coefficient cases of ordinary direct-image comparison

Source: blueprint latest, scalar-six direct-image proof, finite rings,
finite-free and finitely presented extensions, localization, and algebraic closure.
(blueprint: lem-sfb-scalar-direct-image-elementary-cases).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarSixChange
attribute [local irreducible] scalarDirectImageMate


/-- Invertibility of the normalized mate for the six elementary coefficient maps
and the algebraic-closure identity. Composite maps are not asserted here.

Source: blueprint latest, `det-prop-scalar-six-direct-image.proof.md`,
Finite rings; Finite free and finitely presented coefficient extensions;
localization; algebraic closure; Formal properties for the identity.
(blueprint: lem-sfb-scalar-direct-image-elementary-cases).

Proof: Finite type and separatedness of f follow by cancellation of the structure
maps over k, hence f is qcqs. In the finite-ring case transport internal modules
to fixed module sheaves using the finite-discrete coefficient comparison, and
transport the actual mate using the pullback and adjunction normalizations.
Apply finiteRingRelativeScalarComparison, using p = ringChar k, the positive
ell-power annihilators (increase the exponents if necessary), and the transported
boundedness, constructibility and Tor amplitude. Reflect invertibility through
the target equivalence. This proof uses the relative torsion cohomological bound,
not an absolute cohomological bound on k, and permits nonflat maps and zero rings.
For integral and field finite extensions use the finite-free isomorphisms of
cartesianCoefficients and finiteFreeDirectImageCoherence; transport its counit mate
through the internal/sectionwise module equivalence. The normalizations on a
identify the coefficient square and its inverse pullback comparison with the
ones defining scalarDirectImageMate. For an integral-to-finite map use the
continuous map witnessing IsIntegralFiniteScalarMap and its two-term finite-free
model from integralFiniteScalarPerfectModel. Its normalized projection is this
mate, and scalar restriction is conservative, so the mate is invertible.
For localization and algebraic closure use the bounded-below comparisons
localizedDirectImageComparison_isIso and
isIso_derivedPushHom_padicAlgCl_of_boundedBelow. Bounded constructible inputs
are bounded below; the defining pullback normalizations identify their adjuncts
with the scalar extension of this geometric counit, so uniqueness of adjuncts
identifies the maps, after the canonical functor comparisons. Finally the scalar
unit comparison identifies the identity-coefficient mate with the identity by
the two geometric triangle identities. All transports are along the specified
coefficient and derived-functor comparisons, so they prove invertibility of the
specified map, rather than existence of an unrelated isomorphism. -/
theorem scalarDirectImageElementaryCases
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    (∀ (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
      (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
      (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
      (φ : A →+* B)
      (a : (⟨cartesianFinitePointRing A⟩ : ScalarSixRing.{u}) ⟶
        ⟨cartesianFinitePointRing B⟩)
      (ha : ∀ (P : Profinite.{u}) (s : (cartesianFinitePointRing A).obj.obj (op P)) (x : P),
        ((a.hom.hom.hom.app (op P)) s).down x = φ (s.down x)),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (cartesianFinitePointRing A) X.left),
      (constantModelBoundedConstructible (cartesianFinitePointRing A) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicIntegersRingObj ell F.1⟩)
      (ha : a.hom.hom = finiteCoefficientIntegersPointMap ell h),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.padicIntegersRingObj ell E.1) X.left),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj F.1⟩)
      (ha : a.hom.hom = Profinite.padicSubfieldRingObjMap ell h),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.continuousMapRingObj E.1) X.left),
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj E.1⟩)
      (ha : a.hom.hom = (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E.1)),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.padicIntegersRingObj ell E.1) X.left),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicAlgClRingObj ell⟩)
      (ha : a.hom.hom = Profinite.padicSubfieldRingObjToPadicAlgCl ell E),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.continuousMapRingObj E.1) X.left),
      (constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (A : Type u) [CommRing A] [Finite A]
      (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨cartesianFinitePointRing A⟩)
      (ha : IsIntegralFiniteScalarMap ell E A a),
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules
          (Profinite.padicIntegersRingObj ell E.1) X.left),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E.1) X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((scalarDirectImageMate a f.left).app K)) ∧
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules
        (Profinite.padicAlgClRingObj ell) X.left),
      IsIso ((scalarDirectImageMate
        (𝟙 (⟨Profinite.padicAlgClRingObj ell⟩ : ScalarSixRing.{u})) f.left).app K)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
