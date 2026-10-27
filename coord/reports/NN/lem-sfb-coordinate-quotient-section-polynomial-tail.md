## Worker report

The module Sheaf.AlgebraicGeometry.CoordinateQuotientSectionPolynomialTail states
AlgebraicGeometry.coordinateQuotient_section_polynomial_tail, with its proof `sorry`.
Three real helper definitions name the pulled-back twist, its module of global sections
with canonical k-scalars, and its pulled-back coordinate frame. These are expressions
in the existing pullback and twist constructions, not new independent notions or
choices of unspecified objects. The node changes only in `lean`.

Hypothesis and clause correspondence:

- A field k is `{k : Type u} [Field k]`; arbitrary `N : ℕ` includes N = 0.
  The polynomial variables are `ULift.{u} (Fin (N + 1))`, as in the dependency's
  quotient grading. The lift is a bijective relabelling and keeps the ring in Type u.
- The homogeneous ideal is `J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule
  (ULift.{u} (Fin (N + 1))) k)`. This is a bundled ideal with precisely the homogeneous
  condition, with no properness or saturation assumption.
- The ring A is the actual `MvPolynomial ... k ⧸ J.toIdeal`; the degree-m subspace
  is the recorded `coordinateQuotientPiece J m`. The instance
  `coordinateQuotientGrading` is used throughout. The u_j are explicitly
  `Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j)`.
- Z is `Proj (coordinateQuotientPiece J)`. The existing `coordinateQuotientImmersion J`
  is literally `Proj.map` of the quotient graded homomorphism, with surjectivity
  supplied by `Ideal.Quotient.mk_surjective`; its target is definitionally Proj B.
  This uses the specified quotient morphism, rather than assuming an arbitrary
  closed embedding. Its closed-immersion property is the standard surjective Proj
  result (Stacks 01N1).
- L_m is `coordinateQuotientSectionTwist J m`, the actual
  `(tensorPullback (coordinateQuotientImmersion J)).obj (Proj.twist ... m)`.
- The first existential family `θ` consists of isomorphisms
  `Proj.twist (coordinateQuotientPiece J) m ≅ coordinateQuotientSectionTwist J m`.
  Its first conjunct sends `twistPowSection m` for u_j to
  `coordinateQuotientSectionFrame J m j`, which is exactly
  `tensorPullbackSection` of the z_j^m frame. Degree-one membership is obtained
  from the recorded quotient graded map and `MvPolynomial.isHomogeneous_X`.
  These normalized frames on a covering determine theta, so the comparison is canonical.
- The second conjunct quantifies over both coordinates and every open W in their
  intersection. It states `res e_i = res (awayToSection (Away.mk ... 1 u_i ...)) ^ m
  • res e_j`. The fraction is u_i/u_j in the degree-zero homogeneous localization;
  restricting it to W gives precisely the transition `(u_i/u_j)^m` on overlaps.
- The second existential family `σ` has type
  `∀ m : ℕ, coordinateQuotientPiece J m →ₗ[k] coordinateQuotientTwistSections J m`.
  Thus k-linearity is part of its type, in every degree. Its restriction conjunct
  is exactly `res (σ m h) = awayToSection (Away.mk ... m h ...) • e_j`.
  Here `Away.mk` uses numerator degree m and denominator u_j^m, so this is
  `(h/u_j^m)e_j`. Every coordinate chart is quantified, including empty charts.
  The charts cover Z, so these restrictions determine the maps canonically.
- H^0 is written as global sections: `RingedSpace.globalSectionsFunctor ...` is
  the evaluation of the module sheaf at top. This is the degree-zero cohomology
  in the node, without changing to another cohomology construction. To obtain
  the k-module, `ModuleCat.restrictScalars` uses the actual ring map induced by
  `coordinateQuotientImmersion J ≫ projectiveSpaceOverAffineToSpec ... k`, preceded
  by `Scheme.ΓSpecIso.inv`. No arbitrary scalar action is assumed or chosen.
- `∀ m : ℕ, Module.Finite k (coordinateQuotientPiece J m)` is finite-dimensionality
  of every A_m. `∃ (a : ℕ) (P : Polynomial ℚ)` supplies a nonnegative bound and
  rational polynomial. For every m ≥ a, `Function.Bijective (σ m)` makes the linear
  map an isomorphism, and the two `P.eval` equalities are the two required dimensions.
  All finranks use exactly the displayed k-module structures.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Sheaf.RingTheory.CoordinateQuotientGrading: `coordinateQuotientPiece`,
  `coordinateQuotientGradingCompatible`, `existsUnique_coordinateQuotientGrading`,
  and the actual `coordinateQuotientGrading` instance.
- Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme/Basic: `AlgebraicGeometry.Proj`,
  `Proj.basicOpen`, `Proj.awayToSection`; homogeneous localization `Away.mk`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`, read to
  check the meaning of the stipulated canonical quotient immersion.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`, and the normalized adjunction.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules/UnitToTwist/TensorObj:
  `Proj.twist`, `unitToTwist`, `twistPowSection` (with its full section type and formula).
- WeilConjectures.AlgebraicGeometry.PQFCohomology:
  `sheafCohomologyAndHigherDirectImages`; its recorded cohomology is
  `RingedSpace.moduleCohomology`. Its `globalSectionsFunctor` supplies H^0 here.
- Proof imports: Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison
  (`Proj.gradedQuotientTwistComparison`),
  Sheaf.AlgebraicGeometry.FiniteGradedModuleSectionTail
  (`Proj.finite_graded_module_section_tail`),
  Sheaf.RingTheory.StandardGradedHilbertFunction
  (`GradedAlgebra.IsStandard.exists_eventually_eq_polynomial`), and the standard
  graded algebra dependency transitively (`GradedAlgebra.IsStandard`).

Existing helper ownership/import detail: `coordinateQuotientGradedMap` and
`coordinateQuotientImmersion` already belong to
Sheaf.AlgebraicGeometry.ProjectiveCoordinateRingEulerPolynomial, so this delivery imports
that module rather than duplicating either definition. That node lists the present item
as a proof dependency. The reverse proof import must therefore be omitted by the
standard import-cycle exception in stages/2-statements.md §3(7); adding that reverse
import would create an actual module cycle. No DAG dependency is added towards this
consumer, and the present theorem does not use its Euler-polynomial theorem as a premise.
The definitions themselves contain only the quotient ring map and Proj.map.

Edge cases checked before writing: N = 0 is a single homogeneous variable; m = 0 has
h/u_j^0 = h, e_j the unit frame, and transition exponent zero. For J = B the quotient
is zero, Proj is empty, all section spaces and graded pieces are zero; theta is the
unique isomorphism and sigma the bijection of zero spaces, with a = 0 and P = 0.
A coordinate in J gives an empty chart, where the formula is equality in the zero
module. An irrelevant-primary proper ideal may have empty Proj but nonzero low
pieces: bijectivity is asserted only eventually. Unsaturated ideals and nilpotents
are retained in the actual quotient and are not excluded. Arbitrary characteristics
and arbitrary field universe u are permitted.

Searches for existing statements:

- `msearch.py ... leanfinder` query: "Canonical homogeneous coordinate quotient map to
  global sections of projective twists is eventually an isomorphism with Hilbert polynomial".
  Eight hits, including Proj.isIso_toSpec, fromOfGlobalSections, projIsoSpecTopComponent,
  awayι and toBasicOpenOfGlobalSections. These are chart/Proj construction APIs,
  not this coordinate quotient section and polynomial theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Proj, Module.finrank"`: zero hits.
- `msearch.py ... grep "section.*twist|twist.*section|hilbertPoly" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch` query: "Homogeneous coordinate quotient graded pieces
  canonically map to sections of pulled back projective twists, eventually isomorphically
  with polynomial dimensions". Eight hits: GradedRing.proj, Proj.basicOpenToSpec_app_top,
  Proj.awayToSection, Proj.awayMap_awayToSection, ProjectiveSpectrum.Proj.awayToSection,
  Proj.basicOpenIsoAway, Proj.basicOpenIsoAway_hom, ProjectiveSpectrum.Proj.awayToΓ.
  These give projections and localized chart sections, not the sought theorem.
- `rg` in lean/WeilConjectures and lean/Sheaf for `coordinateQuotient`, coordinate
  sections, quotient sections, and section polynomial: found the actual quotient
  grading and the existing quotient map/immersion helpers, reused above. The Euler
  theorem only states eventual dimensions/Euler values, not the section isomorphisms,
  all-degree canonical maps, or overlap formulas. No exact existing match.
- Search for the node id in lean/WeilConjectures returned no declaration.

Source text read: coherent.tex lemma-recover-tail-graded-module (0AG7),
constructions.tex lemma-apply-modules (01MT) and
lemma-surjective-graded-rings-generated-degree-1-map-proj (01N1),
algebra.tex lemma-graded-module-fg (00K0) and proposition-graded-hilbert-polynomial (00K1).
No statement correction, dispute, new independent notion, or unusable dependency was found.

Validation: scompile.py compiled both the sandbox and final module name, without errors
or non-sorry warnings. The initial compile diagnosed the polynomial grading instance;
using the existing MvPolynomial.gradedAlgebra attribute, as in its owning dependency,
resolved it. No Lean library or launcher file was edited.

## Second reading by NN

A separate agent was not started, as the dispatcher brief explicitly prohibits it.
On a second pass through the node and file, I checked each quantified m, coordinate,
open restriction and scalar action against the formulas above. The direction of theta
is the inverse of the imported comparison, as required. The overlap coefficient has
numerator u_i and denominator u_j and exponent m; the section coefficient instead has
numerator h and denominator u_j^m. The section maps are linear in every degree,
whereas bijectivity and both finrank equalities share one eventual bound. The actual
quotient and its grading are reused unchanged. The scalar restriction was checked
against the structure map, rather than using an unrelated or arbitrary Module instance.
The J = B and empty chart cases require no nonzero quotient instance and remain typed.
No mismatch was found. The only elaboration repair was enabling the already defined
polynomial grading in this file, matching its existing owner and project convention.
