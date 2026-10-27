module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.CondensedOpenClosedRecollement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.Paper.CanonicalPointScalarComparison
public import Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData
public import Sheaf.AlgebraicGeometry.FieldActionTransportData
public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent
public import Sheaf.Paper.SupportedLatticeNormProjection
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible
import Sheaf.SixFunctors.IntegralModelsGenerators
import Sheaf.Paper.DerivedScalarMateThickLocus
import Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Geometric norm projection by finite supported-lattice devissage

Source: current blueprint, six-functors direct-images proof, paragraph (3), and
integral-models generators, clause (1); the agent refinement of the ordinary
all-continuous norm coefficient projection.
(blueprint: lem-sfb-geometric-generator-projection-devissage).

The projection is the existing normalized point projection, not an unspecified
isomorphism. Its natural transformation is specified componentwise, so the shift
and triangle clauses concern that same canonical map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
open CondensedGalois FieldActionTransport

namespace GeometricNormProjection

/-- Finite type on the actual second projection of geometric base change.
Source: Mathlib finite-type base-change instance, direct-images proof (3)
(blueprint: lem-sfb-geometric-generator-projection-devissage). -/
instance baseChangeLocallyOfFiniteType (k ks : Type u) [Field k] [Field ks]
    [Algebra k ks] (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] :
    LocallyOfFiniteType
      (Over.mk (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap k ks))))).hom :=
  MorphismProperty.pullback_snd a
    (Spec.map (CommRingCat.ofHom (algebraMap k ks))) (inferInstance : LocallyOfFiniteType a)

/-- Quasi-compactness on the same second base-change projection.
Source: Mathlib quasi-compact base-change instance, direct-images proof (3)
(blueprint: lem-sfb-geometric-generator-projection-devissage). -/
instance baseChangeQuasiCompact (k ks : Type u) [Field k] [Field ks]
    [Algebra k ks] (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) [QuasiCompact a] :
    QuasiCompact
      (Over.mk (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap k ks))))).hom :=
  MorphismProperty.pullback_snd a
    (Spec.map (CommRingCat.ofHom (algebraMap k ks))) (inferInstance : QuasiCompact a)

/-- The source of the specified coefficient projection, using ordinary K-flat extension.
Source: direct-images proof (3), B tensor_A^L Rp_{T*,A}
(blueprint: lem-sfb-geometric-generator-projection-devissage). -/
abbrev source {R R' : Coefficients.{u}} (φ : R ⟶ R') (T : Scheme.{u}) :=
  (pointModules R.toMon T).rightDerivedFunctor ⋙ condensedDerivedExtend φ

/-- The target of the specified projection, using the actual derived point direct image.
Source: direct-images proof (3), Rp_{T*,B}(B_T tensor_{A_T}^L -)
(blueprint: lem-sfb-geometric-generator-projection-devissage). -/
abbrev target {R R' : Coefficients.{u}} (φ : R ⟶ R') (T : Scheme.{u}) :=
  derivedExtend φ T ⋙ (pointModules R'.toMon T).rightDerivedFunctor

/-- Canonical shifts on condensed scalar extension are adjoint to exact restriction's shifts.
Source: direct-images proof (3), canonical coefficient shifts
(blueprint: lem-sfb-geometric-generator-projection-devissage). -/
instance condensedExtensionCommShift {R R' : Coefficients.{u}} (φ : R ⟶ R') :
    (condensedDerivedExtend φ).CommShift ℤ :=
  (condensedScalarAdjunction φ).leftAdjointCommShift ℤ

end GeometricNormProjection

/-- Geometric pullback is bounded constructible, is finitely generated by the displayed
supported lattices, and satisfies the specified ordinary norm coefficient projection.
Naturality, all integer shifts and the connecting arrows of distinguished triangles
refer to the same componentwise fixed projection.
Source: current blueprint, six-functors direct-images proof (3), agent-extracted finite
lattice argument; integral-models generators clause (1).
(blueprint: lem-sfb-geometric-generator-projection-devissage).

Proof plan:
1. Base change of the finite-type separated structure map makes T finite type and
separated over ks (lem-pod-separated-finite-type-base-change). X and T are qcqs by
lem-weil-pbc-qcqs-over-affine; ks is separably closed of characteristic p, distinct from ell.
No finite-type assumption on the projection to X is needed.
2. Exact module pullback (det-prop-sfb-module-pullback-exact-main) identifies its derived
cohomology with pullback of each cohomology sheaf, by
lem-weil-pbc-exact-functor-derived-factorization. Pull back the same finite scalar models
using lem-sfb-pullback-constant-model-constructible. The original finite cohomological
interval is retained, proving the first clause.
3. Clause (1) of det-lem-integral-models-generators gives a finite cone-and-shift expression
in supported rationalized integral lisse lattices. Finite type over a field makes T
Noetherian (lem-weil-pbc-finite-type-over-noetherian); its closed subsets satisfy the
minimal condition (lem-weil-pbc-noetherian-scheme-closed-subsets-minimal), and all subsets
are quasi-compact (lem-sfb-noetherian-space-compact-subsets). Thus the locally closed
supports are constructible. Extension is open extension followed by closed pushforward,
as in lem-weil-pbc-condensed-open-closed-recollement; variable rank and zero are allowed.
4. Apply lem-sfb-derived-scalar-mate-thick-locus to T over Spec ks. The trivial-Galois case
of lem-sfb-field-action-derived-section-transport identifies the counit mate with the
point projection, preserving scalar units, exact restriction, input maps and shifts.
Its exact derived equivalences preserve distinguished triangles and connecting arrows.
Hence the specified projections are natural, commute with canonical shifts and give
morphisms of distinguished triangles; their isomorphism locus contains zero and is
closed under isomorphisms, shifts and cones. This uses ordinary K-flat tensor, not
flatness of the coefficient inclusion.
5. Every supported rationalized lattice lies in this locus by
lem-sfb-supported-lattice-norm-projection: its normalization is exactly the existing
pointProjection, the transpose of insertion of one and canonical exact restriction.
6. Induct on the finite expression from step 3. At each cone use
lem-sf-triangle-morphism-iso on the triangle morphism of step 4. Zero, isomorphisms and
shifts stay in the locus, so the geometric pullback does too. Empty X and V = 0 give zero
objects and their unique comparison isomorphism. No completion or replacement of all
continuous functions by finite-subextension-valued functions occurs.
-/
theorem geometric_generator_projection_devissage
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks] [CharP k p]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (V : DerivedCategory.{u + 2} (Modules (normCoefficients E).toMon X))
    (_hV : constantModelBoundedConstructible (normCoefficients E).X X V) :
    constantModelBoundedConstructible (normCoefficients E).X (geometricScheme k ks X a)
      ((CondensedRing.moduleObjectDerivedPullback (normCoefficients E).X
        (geometricProjection k ks X a)).obj V) ∧
    (∀ P : ObjectProperty
        (DerivedCategory.{u + 2} (Modules (normCoefficients E).toMon
          (geometricScheme k ks X a))),
      P.IsTriangulated → P.IsClosedUnderIsomorphisms →
      (∀ (S : Scheme.{u}) (i : S ⟶ geometricScheme k ks X a) (hi : IsImmersion i),
        Topology.IsConstructible (Set.range i) →
        ∀ L₀ : Modules (supportedLatticeIntegralRing ℓ E).toMon S,
          IsLisseCoefficientModule (supportedLatticeIntegralRing ℓ E).X L₀ →
          P (supportedRationalizedLattice ℓ E
            (Over.mk (pullback.snd a
              (Spec.map (CommRingCat.ofHom (algebraMap k ks))))) i hi L₀)) →
      P ((CondensedRing.moduleObjectDerivedPullback (normCoefficients E).X
        (geometricProjection k ks X a)).obj V)) ∧
    IsIso (pointProjection (supportedLatticeNormInclusion ℓ E) (geometricScheme k ks X a)
      (canonicalPointScalar (supportedLatticeNormInclusion ℓ E) (geometricScheme k ks X a))
      ((CondensedRing.moduleObjectDerivedPullback (normCoefficients E).X
        (geometricProjection k ks X a)).obj V)) ∧
    ∃ π : GeometricNormProjection.source (supportedLatticeNormInclusion ℓ E)
        (geometricScheme k ks X a) ⟶
      GeometricNormProjection.target (supportedLatticeNormInclusion ℓ E)
        (geometricScheme k ks X a),
      (∀ N : DerivedCategory.{u + 2} (Modules (normCoefficients E).toMon
          (geometricScheme k ks X a)),
        π.app N = pointProjection (supportedLatticeNormInclusion ℓ E)
          (geometricScheme k ks X a)
          (canonicalPointScalar (supportedLatticeNormInclusion ℓ E)
            (geometricScheme k ks X a)) N) ∧
      NatTrans.CommShift π ℤ ∧
      ∀ Δ : Triangle (DerivedCategory.{u + 2} (Modules (normCoefficients E).toMon
          (geometricScheme k ks X a))),
        Δ ∈ distTriang _ →
        (GeometricNormProjection.source (supportedLatticeNormInclusion ℓ E)
          (geometricScheme k ks X a)).mapTriangle.obj Δ ∈ distTriang _ ∧
        (GeometricNormProjection.target (supportedLatticeNormInclusion ℓ E)
          (geometricScheme k ks X a)).mapTriangle.obj Δ ∈ distTriang _ ∧
        ∃ m : (GeometricNormProjection.source (supportedLatticeNormInclusion ℓ E)
              (geometricScheme k ks X a)).mapTriangle.obj Δ ⟶
            (GeometricNormProjection.target (supportedLatticeNormInclusion ℓ E)
              (geometricScheme k ks X a)).mapTriangle.obj Δ,
          m.hom₁ = π.app Δ.obj₁ ∧ m.hom₂ = π.app Δ.obj₂ ∧ m.hom₃ = π.app Δ.obj₃ := by
  sorry

end AlgebraicGeometry.ProEtale
