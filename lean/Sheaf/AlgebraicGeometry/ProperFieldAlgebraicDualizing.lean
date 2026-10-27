/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom

import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Sheaf.RingTheory.RegularLocalBoundedInjectiveResolution
import Sheaf.Algebra.Homology.DerivedHomProjectiveResolution
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import WeilConjectures.RingTheory.RegularLocalFiniteGlobalDimension
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Homology.FiniteMapDualizingTransfer

/-! # Algebraic dualizing complexes for proper schemes over fields

Source: Stacks Project, duality.tex, Tag 0AA3 (lemma-shriek-dualizing),
Tag 0AWI (example-proper-over-local), and example-equidimensional-over-field.
(blueprint: lem-sfb-proper-field-algebraic-dualizing).

The direct image includes the canonical affine transport to ordinary k-modules.
Stalks apply the recorded module stalk functor to a localization representative.
The scalar map is the transpose of the identity under derived tensor-Hom adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The right adjoint of proper direct image sends k[0] to a complex with bounded
coherent cohomology and algebraic dualizing stalks over Noetherian local rings.
No dimension, connectedness, reducedness or field-perfection condition is imposed.
The two localization objects in the stalk clauses are the same stalk complex.
`MonoidalClosed.curry' (𝟙 K_x)` is the scalar map from the unit O_{X,x}[0].

Source: Stacks Project, duality.tex, Tag 0AA3; Tag 0AWI and
example-equidimensional-over-field.
(blueprint: lem-sfb-proper-field-algebraic-dualizing).

Proof:
1. Properness gives finite type and a finite affine cover Spec(B_i). A field is
   Noetherian; finite-type algebras are Noetherian and finitely presented
   (lem-weil-pbc-finite-type-algebra-noetherian,
   lem-weil-pbc-finite-type-noetherian-finite-presentation). Thus X is locally
   Noetherian and f is finitely presented and flat (lem-pc-flat-field,
   lem-pc-separated-quasi-separated).
2. Apply lem-sfb-proper-flat-dualizing-polynomial-model. The affine derived
   equivalence (lem-pc-affine-qcoh-derived-equivalence) and uniqueness of right
   adjoints (det-sp-unique-right-adjoint) identify its complex with a(k[0]).
   On a chart B = P/I, P = k[t_1,...,t_n], its model is RHom_P(B,Omega^n)[n]
   with the coinduced B-action.
3. Every prime localization A of P is regular local
   (lem-weil-pbc-polynomial-ring-field-regular-ring), and A[0] has a bounded
   injective model (lem-trf-regular-local-bounded-injective-resolution).
   Its cohomology is finite, and evaluation at 1 identifies RHom_A(A,A) with A[0]
   and its scalar map with the identity (lem-sc-derived-hom-projective-resolution).
4. The polynomial differential basis (lem-weil-pbc-polynomial-ring-kahler-basis)
   trivializes Omega^n by its ordered volume form and the determinant; for n=0
   use the zeroth exterior power. Thus the model is M_B[n], M_B = RHom_P(B,P).
5. Shifts preserve finite cohomology, bounded injective representatives and scalar
   isomorphisms: shifting both Hom arguments cancels and preserves scalar identities.
6. Resolve B by degreewise finite free P-modules
   (lem-weil-pbc-finite-free-resolution-noetherian). Derived Hom is the dual
   complex (lem-sc-derived-hom-projective-resolution); its cycles and hence
   cohomology are finite (lem-weil-pbc-noetherian-submodule-finite). The same
   generators work over B. Cohomology in negative degrees vanishes.
7. Localize at every maximal ideal of P, using flatness and coherent RHom base
   change (lem-weil-pbc-localization-flat,
   lem-trf-flat-coherent-homothety-base-change). The local ring has dimension n
   (lem-weil-pbc-polynomial-ring-maximal-localization-dimension) and global
   dimension at most n (lem-weil-pbc-regular-local-finite-gl-dim), so cohomology
   above n vanishes. A module zero at all maximal localizations is zero.
8. The tilde homology comparison (new-affine-derived-tilde-homology-comparison)
   and the finite-type and coherence criteria
   (lem-weil-pbc-quasi-coherent-finite-type-affine, pqf-lem-coherent-ft-locnoeth)
   give coherent cohomology on every chart, hence globally. Take minimum and
   maximum of the finite collection of chart bounds. For the empty scheme all
   objects are zero and bounds [0,0] work.
9. Exact stalks and the affine ring and tilde stalk formulas
   (lem-weil-pbc-module-stalk-exact, lem-weil-pbc-affine-open-stalk-localization,
   lem-weil-pbc-spec-tilde-stalk-localization) identify the stalk with the localized
   chart model. For p in B and its inverse image q in P, put A=P_q and D=B_p.
   Surjectivity gives B tensor_P A = D. Flat coherent RHom base change identifies
   the stalk with RHom_A(D,A)[n], D-linearly: localization respects the coinduced
   action (b phi)(y)=phi(by). Forgetting scalars detects quasi-isomorphisms.
10. The quotient A to D is finite and both rings are Noetherian. Apply
   lem-trf-finite-map-dualizing-transfer to A[0], whose three conditions were
   verified in step 3. Shift as in step 5 and use step 9 to obtain the bounded
   injective stalk representative and the canonical scalar isomorphism. -/
theorem proper_field_algebraic_dualizing
    (k : Type u) [Field k] (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings (Spec (.of k)).toRingedSpace))]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (a : DerivedCategory (ModuleCat.{u} k) ⥤ schemeDerivedQCohCategory X)
    (_adj : ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f ⋙
      (RingedSpace.globalSectionsFunctor (Spec (.of k)).toRingedSpace ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).rightDerivedFunctor) ⊣ a) :
    (∀ j : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj
          (a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
            (ModuleCat.of k k))).obj)) ∧
    (∃ p q : ℤ, ∀ j : ℤ, j < p ∨ q < j →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj
          (a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
            (ModuleCat.of k k))).obj)) ∧
    (∀ x : X, IsNoetherianRing (X.presheaf.stalk x) ∧
      (∃ I : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ,
        (∃ p q : ℤ, ∀ j : ℤ, j < p ∨ q < j → IsZero (I.X j)) ∧
        (∀ j : ℤ, Injective (I.X j)) ∧
        Nonempty (DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj
          (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
            (.up ℤ)).obj (DerivedCategory.Q.objPreimage
              (a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
                (ModuleCat.of k k))).obj)))) ∧
      IsIso (MonoidalClosed.curry' (𝟙 (DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (.up ℤ)).obj (DerivedCategory.Q.objPreimage
            (a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
              (ModuleCat.of k k))).obj)))))) := by
  sorry

end AlgebraicGeometry
