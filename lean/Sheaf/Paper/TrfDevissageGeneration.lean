/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.FlatModel
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Triangulated.Generators
import Sheaf.AlgebraicGeometry.ConstructibleSheafDevissage
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.SixFunctors.FlatModelGeneration
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Triangulated.AmbientThickClosureEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.CategoryTheory.Triangulated.GeneratingClassDetermination
import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.RepresentationTheory.LAdic
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.FieldDiscreteModules
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.FieldTheory.EtaleFieldGaloisClassification

/-!
# Constructible devissage and the need for lisse coefficients

Source: Weil conjectures blueprint, `sec-six-functors/sk-lem-sf-ctf-generation/`
`lem-trf-devissage-generation.md`, statement and Steps 0--3
(blueprint: lem-trf-devissage-generation).

The lisse-flat generator family is the published `sfProEtaleClosureGenerators`.
Closed direct image is exact, so its sheaf-level formula in degree zero represents
`Rg_*j_!L`. The second clause of the statement is an existential obstruction to replacing
all such L by the constant rank-one coefficient sheaf; it is not a claim for every X.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The constant-coefficient subfamily in the final sentence of the statement.
The actual stratum immersion factors through its scheme-theoretic closure, and the
coefficient sheaf is the sheafification of the constant regular module A. The canonical
intrinsic realization retains its scalar action. Closed direct image is exact, so this
sheaf in degree zero is also `Rg_*j_!A_U`.
Source: blueprint `lem-trf-devissage-generation`, statement and Step 3
(blueprint: lem-trf-devissage-generation). -/
def trfConstantClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : LocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((constantSheaf (ProEt.topology (str.domain i))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))))

/-- Bounded constructible complexes of finite Tor amplitude are exactly the ambient thick
closure of the lisse flat locally closed extension generators. `T` supplies the coefficient
conventions; X is any separated finite-type scheme over its algebraic closure k.
Source: blueprint `lem-trf-devissage-generation`, statement and Steps 0--2
(blueprint: lem-trf-devissage-generation).

Proof plan, following the node's numbered steps:
1. Finite type over k makes X and its locally closed subschemes Noetherian by
lem-weil-pbc-finite-type-over-noetherian; the empty scheme has zero sheaf category.
2. Over the finite ring, finite flat modules are finitely presented and projective by
lem-weil-pbc-finitely-presented-flat-module-projective; projectives are flat by
lem-weil-pbc-projective-module-flat. This identifies the allowed local models.
3. Factor every stratum immersion through its closure. By lem-fin-constructible-devissage,
lem-fin-extension-by-zero, lem-fin-closed-immersion and det-sf-flat-model-generation (3),
the generators lie in the finite-Tor constructible category and that category is thick.
4. For an etale finite-Tor complex choose a bounded flat constructible model using
lem-sf-etale-flat-constructible, with its chosen Tor interval.
5. Apply det-sf-flat-model-generation (1)--(2) to each term: its finite extension filtration
has lisse finite-projective stratum factors. Use lem-weil-pbc-complex-ses-triangle to put
each term in the thick closure. This does not truncate by the cohomology sheaves.
6. The degreewise split sequences of stupid tails from def-kun-truncations give triangles
with third vertex P^q[-q]. Descend from the zero tail above the bound to obtain P, hence K.
7. lem-sf-proetale-constructible-origin and lem-sf-comparison-tor-amplitude give the exact
ctf comparison equivalence. Exactness and inverse exactness use
lem-sf-comparison-pullback-exact, lem-sf-exact-functor-derived-triangulated and
lem-trf-exact-equivalence-inverse, with their shift comparisons.
8. A closed immersion is qcqs: it is affine and a monomorphism.
9. prop-weil-pbc-comparison-direct-image followed by
lem-cbc-proetale-extension-zero-comparison identifies the actual immersion generators.
10. lem-sf-proetale-locally-constant-origin and lem-cbc-proetale-comparison-stalk identify
all lisse flat generators in both directions; constant coefficients also correspond.
11. lem-trf-ambient-thick-closure-equivalence transports the ambient thick closure equality.
12. The node's determination consequence then follows from
lem-sf-triangle-two-out-of-three and lem-sf-generating-class-determination, with the
specified shift compatibility; no additional determination assertion is included here. -/
theorem trf_devissage_generation (T : WeilConjectures.TraceFormulaCoefficientConventions.{u})
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of T.datum.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    WeilConjectures.finiteTorConstructible T.coefficients.l T.coefficientField T.level
      T.level_pos X =
    (@sfProEtaleClosureGenerators X T.coefficientRing inferInstance
      (Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
        T.level T.level_pos)).triangEnvelope := by
  sorry

/-- Constant rank-one coefficients do not generate in general: there is a separated
finite-type X with admissible coefficients and a ctf complex outside their thick closure.
Source: blueprint `lem-trf-devissage-generation`, final sentence and Step 3
(blueprint: lem-trf-devissage-generation).

Proof plan, node steps 13--15 (with the comparison of steps 7--11):
13. Take k = algebraic closure of F_5, X = G_m and A = F_3, realized at l = 3,
E = Q_3, n = 1 in the coefficient conventions. The cover t = u^2 is finite etale of
rank two: its derivative 2u is invertible by
lem-weil-pbc-standard-etale-monic-derivative. thm-galois-fundamental and
cor-galois-lisse-representations construct its rank-one sign local system L, which is
free locally and hence an allowed flat generator.
14. Pull back exactly to Spec k(t) by prop-weil-pbc-inverse-image-modules-exact and
lem-sf-exact-functor-derived-triangulated, retaining the discrete Galois action via
lem-exc-field-discrete-modules. Complexes whose bounded cohomology has a finite
filtration with trivial one-dimensional quotients form a thick subcategory. Intersect
filtrations with submodules, pass to their images for quotients, and concatenate for
extensions. The long exact sequence of lem-sf-derived-homology-long-exact gives triangle
closure; shifts and retracts preserve these conditions.
15. Every constant generator has generic restriction either zero or trivial, by
lemma-weil-pbc-finite-stalk-formula, lem-weil-pbc-closed-immersion-finite,
lem-weil-pbc-extension-by-zero-stalks and lem-fin-closed-immersion. The sign local system
has nontrivial generic action: coprime polynomials cannot satisfy f(t)^2 = t g(t)^2,
so u^2 - t defines a separable quadratic field extension; transitivity follows from
lem-exc-etale-field-galois-classification and agrees with the cover action by
thm-galois-fundamental. Its nontrivial rank-one representation has no filtration by
trivial quotients. Thus L is outside the constant-generated closure. The exact comparison
and generator identifications of steps 7--11 transport both the constants and this
obstruction to the pro-etale site. -/
theorem exists_trf_constant_coefficients_not_generating :
    ∃ (T : WeilConjectures.TraceFormulaCoefficientConventions.{u})
      (X : Scheme.{u}) (aX : X ⟶ Spec (.of T.datum.k)),
      LocallyOfFiniteType aX ∧ QuasiCompact aX ∧ IsSeparated aX ∧
      ∃ K : proEtaleDerivedCategory X T.coefficientRing,
        WeilConjectures.finiteTorConstructible T.coefficients.l T.coefficientField
          T.level T.level_pos X K ∧
        ¬ (@trfConstantClosureGenerators X T.coefficientRing inferInstance
          (Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField
            T.level T.level_pos)).triangEnvelope K := by
  sorry

end AlgebraicGeometry
