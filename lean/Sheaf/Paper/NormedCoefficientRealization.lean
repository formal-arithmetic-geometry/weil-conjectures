/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.CartesianCoefficients
import Sheaf.SixFunctors.ResolvingDerivedAdjunction

/-!
# Realization of finite normed coefficient fields

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.8.1 and
Remark 6.8.15; the node's algebraic embedding and scalar transport expansion
(blueprint: lem-sfb-normed-coefficient-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormedCoefficientRealization

/-- Postcomposition by a continuous ring map, in the existing universe-sized continuous
coefficient construction. Source: Bhatt--Scholze, Definition 6.8.1, and the continuous-map
formula of sk-def-sfb-condensed-ring (blueprint: lem-sfb-normed-coefficient-realization). -/
def condenseMap {T T' : Type u} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
    (φ : T →+* T') (hφ : Continuous φ) :
    Mon.mk (Profinite.continuousCoefficientRingObj T) ⟶
      Mon.mk (Profinite.continuousCoefficientRingObj T') :=
  Mon.Hom.mk ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ⟨{ app := fun _ ↦ RingCat.ofHom
           (ULift.ringEquiv.symm.toRingHom.comp
             ((φ.compLeftContinuous _ hφ).comp ULift.ringEquiv.toRingHom))
         naturality := fun _ _ _ ↦ rfl }⟩)

/-- The actual termwise inverse scalar restriction for the point-induced coefficient
isomorphism. Source: the node's proof step 4; Stacks 03CZ
(blueprint: lem-sfb-normed-coefficient-realization). -/
abbrev transport {Λ Λ' : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (a : Λ ≅ Λ') (Z : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ.X Z)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ'.X Z)) :=
  (Mod.comap (coefficientMap a.inv.hom Z) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ'.X Z)).mapDerivedCategory

/-- The canonical inverse-image comparison from the coefficient square induced from the
point. Source: the node's proof steps 7 and 9; Stacks 03CZ
(blueprint: lem-sfb-normed-coefficient-realization). -/
def pullComparison {Λ Λ' : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (a : Λ ≅ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPullback Λ.X f ⋙ transport a X ≅
      transport a Y ⋙ CondensedRing.moduleObjectDerivedPullback Λ'.X f :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X f) (transport a X) ≪≫
    CondensedRing.derivedComapUpperStarIso a.inv.hom f ≪≫
    Functor.isoWhiskerLeft (transport a Y)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).symm

/-- All the categorical conclusions for one of the two coefficient isomorphisms. The
comparison is constrained by the actual derived module-adjunction counits and the
point-induced inverse-image comparison, rather than by a freely chosen adjunction.
Source: Bhatt--Scholze, Remark 6.8.15; the node's proof steps 4--10; Stacks 03CZ, 010N,
015F, 09T5 (blueprint: lem-sfb-normed-coefficient-realization). -/
def IsCoefficientTransport {Λ Λ' : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (a : Λ ≅ Λ') : Prop :=
  (∀ Z : Scheme.{u},
    Nonempty ((Mod.extendScalars (coefficientMap a.hom.hom Z)).leftDerivedFunctor ≅
      transport a Z) ∧
    (transport a Z).IsEquivalence ∧ (transport a Z).IsTriangulated ∧
    (transport a.symm Z).IsEquivalence ∧ (transport a.symm Z).IsTriangulated ∧
    (∀ K n, (DerivedCategory.IsLE ((transport a Z).obj K) n ↔
        DerivedCategory.IsLE K n) ∧
      (DerivedCategory.IsGE ((transport a Z).obj K) n ↔ DerivedCategory.IsGE K n)) ∧
    (∀ K n, (DerivedCategory.IsLE ((transport a.symm Z).obj K) n ↔
        DerivedCategory.IsLE K n) ∧
      (DerivedCategory.IsGE ((transport a.symm Z).obj K) n ↔ DerivedCategory.IsGE K n)) ∧
    (∀ K, boundedConstructible (condensedRingObj Λ'.X Z) ((transport a Z).obj K) ↔
      boundedConstructible (condensedRingObj Λ.X Z) K) ∧
    (∀ K, boundedConstructible (condensedRingObj Λ.X Z) ((transport a.symm Z).obj K) ↔
      boundedConstructible (condensedRingObj Λ'.X Z) K)) ∧
  (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    ∃ γ : CondensedRing.moduleObjectDerivedPushforward Λ.X f ⋙ transport a Y ≅
        transport a X ⋙ CondensedRing.moduleObjectDerivedPushforward Λ'.X f,
      ∀ K,
        (CondensedRing.moduleObjectDerivedPullback Λ'.X f).map (γ.inv.app K) ≫
          (pullComparison a f).inv.app
            ((CondensedRing.moduleObjectDerivedPushforward Λ.X f).obj K) ≫
          (transport a X).map
            ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ.X f).counit.app K) =
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ'.X f).counit.app
          ((transport a X).obj K))

/-- A finite normed extension is realized isometrically in the fixed algebraic closure;
its unit ball and both condensed coefficient presentations induce the specified exact
unbounded derived equivalences, preserving bounds and stratified local finite presentation.

Source: Bhatt--Scholze, Definition 6.8.1 and Remark 6.8.15; agent expansion recorded in
the DAG (blueprint: lem-sfb-normed-coefficient-realization).

Proof:
1. Finite dimension makes E algebraic. Apply the algebraic-closure embedding theorem
(lem-weil-pbc-algebraic-extension-embeds-algebraically-closed, Stacks 09GU), corestrict
its algebra homomorphism to its image, and transport a basis to show the image is finite.
2. Pull back the closure absolute value. Its restriction is the normalized p-adic norm,
so lem-weil-l-adic-extension-absolute-value identifies it with the supplied norm. This
makes the algebra isomorphism isometric and identifies the two closed unit balls.
3. Postcomposition gives the condensed ring isomorphisms. The integer-ring square
commutes because its map is the restriction of the field map. Pull back from the point.
4. For the pulled-back isomorphism c, Ext_c is inverse scalar restriction Res_(c^-1)
(sk-def-sfb-change-of-scalars, Stacks 03CZ), by s tensor m mapping to c^-1(s)m, with
inverse m mapping to 1 tensor m. These are exact inverse equivalences. The exact-functor
derived comparison identifies L(Ext_c) with termwise restriction; it is triangulated
(lem-sf-exact-functor-derived-triangulated).
5. Exact scalar restriction commutes with cohomology
(lem-weil-pbc-exact-functor-complex-cohomology, Stacks 010N), so preserves each bound.
6. Scalar transport commutes with the pullback to every stratum and every covering map.
It takes regular modules to regular modules, and finite cokernel presentations to finite
cokernel presentations (def-sfb-finitely-presented-module). The same local covers
(def-sfb-locally-finitely-presented) and finite stratification work in both directions
(def-sfb-constructible-module), giving sk-def-sfb-bounded-constructible in both directions.
7. Naturality of alpha from point pullback, and of its adjoint eta, makes the identity
of the underlying abelian direct image linear after inverse scalar restriction
(sk-def-sfb-coefficient-morphisms, sk-def-sfb-module-pushforward-pullback).
8. Restriction preserves K-injectives (lem-sfb-comap-preserves-k-injectives). Both total
right derived direct images can be computed on the same transported K-injective
resolution. The ordinary comparison is natural there; lem-sc-kinjective-quasi-iso-comparison
and resolution existence descend it to all unbounded derived objects.
9. The ordinary inverse-image comparison sends b tensor m to c(b) tensor m; its inverse
uses c^-1. The coefficient square supplies balancing. These formulas preserve 1 tensor m
and scalar multiplication, hence the ordinary units and counits (Stacks 03CZ).
10. The embedded coefficients have exact pullback (sk-prop-sfb-cartesian-coefficients),
as do the transported coefficients. Exact-functor derivation and
lem-sfb-resolving-derived-adjunction-normalization identify the derived transposes on
K-injective targets with the localized ordinary transposes (Stacks 015F, 09T5).
Step 9 therefore gives the displayed derived counit equation. The localization universal
property (lem-weil-pbc-localization-universal-property) extends it to every object.
-/
theorem normed_coefficient_realization (ℓ : ℕ) [Fact ℓ.Prime]
    (E Ω : Type u) [NormedField E] [NormedField Ω]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    [Algebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (hE : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] E x‖ = ‖x‖)
    (hΩ : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] Ω x‖ = ‖x‖) :
    ∃ (E' : IntermediateField ℚ_[ℓ] Ω) (_ : FiniteDimensional ℚ_[ℓ] E')
      (σ : E ≃ₐ[ℚ_[ℓ]] E') (_hσ : Continuous σ) (_hσi : Continuous σ.symm)
      (τ : Padic.coefficientExtensionIntegers ℓ E ≃+*
        Padic.coefficientExtensionIntegers ℓ E')
      (_hτ : Continuous τ) (_hτi : Continuous τ.symm)
      (sE : Mon.mk (Profinite.continuousCoefficientRingObj E) ≅
        Mon.mk (Profinite.continuousCoefficientRingObj E'))
      (sA : Mon.mk (Profinite.continuousCoefficientRingObj
          (Padic.coefficientExtensionIntegers ℓ E)) ≅
        Mon.mk (Profinite.continuousCoefficientRingObj
          (Padic.coefficientExtensionIntegers ℓ E'))),
      Isometry σ ∧ Isometry τ ∧
      (∀ x : E, x ∈ Padic.coefficientExtensionIntegers ℓ E ↔ ‖x‖ ≤ 1) ∧
      (∀ x : E', x ∈ Padic.coefficientExtensionIntegers ℓ E' ↔ ‖x‖ ≤ 1) ∧
      (∀ x, (τ x : E') = σ (x : E)) ∧
      sE.hom = condenseMap σ.toRingHom _hσ ∧
      sA.hom = condenseMap τ.toRingHom _hτ ∧
      condenseMap (Padic.coefficientExtensionIntegers ℓ E).subtype
          continuous_subtype_val ≫ sE.hom =
        sA.hom ≫ condenseMap (Padic.coefficientExtensionIntegers ℓ E').subtype
          continuous_subtype_val ∧
      IsCoefficientTransport sE ∧ IsCoefficientTransport sA := by
  sorry

end AlgebraicGeometry.ProEtale.NormedCoefficientRealization
