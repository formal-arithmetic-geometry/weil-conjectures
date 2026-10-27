## Worker report

The module Sheaf.AlgebraicGeometry.RelativeDiagonalProjectiveBoundary states
`AlgebraicGeometry.RelativeDiagonalProjectiveBoundary.relative_diagonal_projective_boundary`.
It has one postponed theorem, whose entire proof is `sorry`. All helper definitions contain
real data or predicates; none uses the theorem. There is no statement correction and no new
node or dependency module. The single added stmt_dep is the already landed
`def-sfb-ring-diagonalizable-group`, whose arbitrary-ring Hopf-spectrum construction is used
rather than a private generalization of the field-only StandardGroupSchemes interface.

Hypotheses and objects, read against the whole node:

* `A : Type u`, `[CommRing A]`, `[IsNoetherianRing A]` give exactly the commutative
  Noetherian base, with `Spec (.of A)` as S. There is no reducedness, domain, nontriviality,
  field or characteristic assumption on A.
* `r n : ℕ` includes both zero cases. The polynomial variable type is
  `ULift.{u} (Fin (n + 1))`, which is the same n+1 coordinates in the scheme universe.
  `projective A n` is the existing `Proj.projectiveSpaceOverAffineToSpec` in `Over S`,
  hence precisely Proj of the total-degree graded polynomial ring, not an arbitrary
  projective embedding or the projective space of a different module.
* `torus A r` is `ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))`.
  The existing group-algebra Hopf structure has basis `AddMonoidAlgebra.single m 1`,
  multiplication by adding characters, coproduct e_m tensor e_m, counit 1 and antipode
  e_(-m). Thus it is exactly the Laurent Hopf torus specified explicitly in the node,
  including r=0. The lift changes only the encoding of the free character lattice.
* `w` chooses each coordinate weight. `a : ModObj ...` contains the action morphism,
  identity law and associativity law in `Over S`. `ha : IsDiagonal ... w a` specifies
  exactly its homogeneous-coordinate coaction by localization: each standard chart is
  preserved scheme-theoretically and each z_j/z_i pulls back to
  t^(w_j-w_i) z_j/z_i. These formulas determine the given action on the standard affine
  cover. The over-category already forces the coefficients A to be fixed. In particular
  this is a coordinate characterization of the action named in the node, not an extra
  hypothesis about a previously arbitrary action or a field-point invariance test.
* `W : Over S`, `[IsReduced W.left]`, `j : W ⟶ projective A n`, `[IsImmersion j.left]`
  give precisely a reduced locally closed subscheme. Mathlib's `IsImmersion` is the
  recorded closed-then-open notion of def-weil-closed-immersion, not merely a topological
  immersion. `aW` and `hj` assert the actual restricted action and equivariant inclusion,
  with the same torus and base. No normality, separatedness or surjectivity is added.

Conclusions and definitions, clause by clause:

* `closureSet A n j` is `Closeds.closure (Set.range j.left)`. `reducedClosed` uses
  `Scheme.IdealSheafData.vanishingIdeal C` and its existing `subscheme`, `subschemeι`.
  Thus Z is the actual reduced induced scheme on the closure, with its canonical map
  to P and S; it is not an existentially unconstrained reduced scheme.
* The existential closed set `B` has underlying set exactly
  `closure (Set.range j.left) \ Set.range j.left`. This states closedness of the boundary
  without requiring an added proof as a hypothesis. `reducedClosed A n B` is its exact
  reduced induced structure, and `inclusion A n B` is its canonical closed immersion.
* `jW`, `IsOpenImmersion jW.left`, its factorization into `j`, and
  `Set.range jW.left = (Set.range jB.left)ᶜ` identify W with exactly Z minus B as an
  open subscheme. `jB`, its closed-immersion property and its factorization into the
  canonical inclusion identify B inside Z.
* `aZ` and `aB` are restricted group-scheme actions. The following four displayed
  equivariance equalities give Z→P, B→P, W→Z and B→Z, respectively; W→P was given by hj.
  The inclusions into P are already the actual canonical reduced closed immersions.
* `Vanishes A n B d f` requires `f.IsHomogeneous d` and vanishing on every B∩D_+(z_i).
  More precisely, `HomogeneousLocalization.Away.mk` constructs f/z_i^d in the degree-zero
  localization, `Proj.awayToSection` is the actual regular chart section, and
  `(inclusion A n B).left.app` restricts it to that precise inverse-image open of B.
  This is zero as a section, not merely at geometric points. The existential `hf` is
  only the proof that constructs this fraction; it is not unspecified mathematical data.
* For every degree d, polynomial f satisfying this predicate, and weight m,
  the conclusion gives `Vanishes ... (MvPolynomial.weightedHomogeneousComponent w m f)`.
  This existing Mathlib map groups monomials by the weight sum of exponents times w_i.
  Its finite-support and finite-sum reconstruction are the existing
  `weightedHomogeneousComponent_finsupp` and `sum_weightedHomogeneousComponent`;
  the finite decomposition is not redefined.
* `coaction` is the concrete algebra homomorphism `MvPolynomial.aeval`, sending z_i
  to `AddMonoidAlgebra.single (ULift.up (w i)) (MvPolynomial.X i)` and fixing A.
  Its codomain R[Z^r] is the standard Laurent-polynomial presentation of
  A[Z^r] tensor_A R. The last equality says exactly that the weight-m component maps
  to t^m times itself, as one coefficient in that group algebra. It is a polynomial
  coaction equation, not just a scalar-action assertion on points.
* There is no finite-freeness assertion about I(B)_d. `Vanishes` is membership in that
  degree piece, which is all the theorem needs, without constructing a redundant
  submodule structure or imposing freeness to access an API.

Dependency declarations used and read:

* Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
* Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
* Sheaf.AlgebraicGeometry.StandardGroupSchemes: `StandardGroupSchemes.multiplicative`
  and its `multiplicativeGroup` (field-only historical Gm dependency). Its entire
  multiplicative signature and docstring were read; the node supplies the Laurent
  torus over A explicitly, so the actual ring construction uses the additional
  recorded `ringDiagonalizableGroup` from Sheaf.AlgebraicGeometry.RingDiagonalizableGroup.
* Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, its projections
  and induced map; the equivalent existing Cartesian monoidal `Over` product encodes
  the fibre products used by the group actions, tensoring inclusions and projections.
* Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic and Scheme: `Proj`, `basicOpen`,
  `awayToSection`. The recorded upstream Proj chart theorem was read in
  WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic.
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace supplies the actual total-degree
  Proj over Spec A; it is used directly, not the separate relative-Proj sheaf construction.
* Mathlib.Algebra.MvPolynomial.Basic and Eval: `MvPolynomial`, `aeval`, `algHom_ext`;
  Mathlib.RingTheory.MvPolynomial.Homogeneous: `IsHomogeneous`, `gradedAlgebra`;
  WeightedHomogeneous: `weightedHomogeneousComponent` and its coefficient formula.
  WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous supplies `awayXRatio`
  and `X_mem_homogeneousSubmodule_one`, whose signatures and docstrings were read.
* Mathlib.AlgebraicGeometry.OpenImmersion, Morphisms.ClosedImmersion and
  Morphisms.Immersion: `IsOpenImmersion`, `IsClosedImmersion`, `IsImmersion`.
* Mathlib.AlgebraicGeometry.Properties: `IsReduced` (the sectionwise definition).
* WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, read in full with the
  evaluation criterion, affine radical ideals, reduced subscheme, image and uniqueness.
  Its existing `vanishingIdeal`, `subscheme` and `subschemeι` are used directly.

Proof imports follow the accepted seven-step plan: finite type and Noetherian schemes,
`LocallyOfFiniteType.isLocallyNoetherian`; affine fibre products (`pullbackSpecIso`) and
commutative tensor products and their universal property; affine-space smoothness
(`AffineSpace.smoothOfRelativeDimension_over`) and smooth restriction; closed-immersion
base change; and the recorded upstream
`IsClosedImmersion.existsUnique_fac_of_range_subset_range`. Their source signatures
were read. `lem-trf-smooth-reduced-dense-pullback` currently has no recorded module,
so there is no import for it, as permitted for an unstated proof-only dependency.
The full natural-language proof is retained in the theorem docstring.

Edge checks: W empty gives Z=B empty and every homogeneous polynomial vanishes;
B empty gives the same vanishing predicate. At d=0, every term is a constant of
weight zero (including a nilpotent constant over nonreduced A), and the fraction
construction permits the zeroth denominator power. At r=0 the character lattice is
singleton and the torus and weight decomposition are trivial. At n=0 there is exactly
one standard chart, with no extra coordinate ratio conditions needed. The zero ring
has empty Proj and is allowed. For A=Z/4 no reducedness of A is inferred or assumed;
B and Z are reduced by the existing radical-ideal construction. Repeated weights are
handled by the existing grouping projection, rather than by separating individual
monomials incorrectly. Nonreduced test schemes are retained by scheme morphisms and
section equations, not replaced by geometric points.

Searches actually run through the prescribed msearch wrapper:

* leanfinder: “A diagonal split torus action on projective space over a Noetherian ring
  preserves the reduced closure and boundary and the character components of homogeneous
  vanishing polynomials”: eight hits, general Proj and projective vanishing-ideal
  closure/topology declarations, no equivariant scheme theorem.
* loogle: “MvPolynomial, weightedHomogeneousComponent”: no hits; unknown identifier in
  that query. Retried “MvPolynomial.weightedHomogeneousComponent”: twelve hits including
  the projection, coefficient formula, finite support and reconstruction. Used the
  existing projection rather than writing it again.
* leansearch: “MvPolynomial weighted homogeneous component projection character weight
  grading”: eight hits including the actual component definition and explicit monomial
  sum. This is a reusable algebraic ingredient, not the boundary theorem.
* grep: `invariant.*(boundary|ideal)|diagonal.*action|splitTorus`, subdirectory
  AlgebraicGeometry: no Mathlib hits for that case-sensitive expression.
* Direct rg searches in both lean/WeilConjectures and lean/Sheaf for the item id,
  torus, weightComponent, diagonal action, invariant boundary/closure/ideal,
  projective action, and coaction found the existing RingDiagonalizableGroup and
  group-object action APIs, but no complete theorem. The field-only
  lem-sfb-projective-invariant-boundary-ideals has no Lean declaration and would not
  supply the arbitrary-ring statement. dag/lean_names_upstream.json has no item match.

Read source places: descent.tex lemma-reduced-local-smooth (034E), morphisms.tex
lemma-smooth-open (056G), schemes.tex lemma-reduced-closed-subscheme,
definition-reduced-induced-scheme (01J4), remark-reduced-induced-locally-closed (0F2L),
and lemma-map-into-reduction (0356). These support the actual reduced scheme argument,
with the node's explicit Laurent coefficient calculation completing the relative claim.
No source or statement fault was found.

## Second reading by Q65

This is the author's separate second pass; independent review belongs to the maintainer,
as specified in the dispatcher brief. I reread the complete node and the actual file.
The Noetherian base has no hidden reducedness hypothesis; r,n,d are unrestricted naturals.
The coordinate type has n+1 elements and all schemes have the same unrestricted universe u.
The torus is the previously constructed group-algebra Hopf spectrum, not a variable
unspecified group. The action is specified by its standard chart maps on sections,
including scheme-theoretic chart inverse images; over S fixes the remaining coefficients.
The restricted action on W is required by the exact tensor-product equivariance equation.
The reduced-closure definition uses precisely the closure of j's range, and the boundary
is existential only as a closed subset with a forced underlying set. Both scheme
structures are fixed by the existing reduced-induced construction. W's open immersion
and complementary range prove exactly the asserted identification, while the four
compatibility equations cover every claimed equivariant inclusion. I checked the
fraction denominator exponent d and the shifted chart weight w_j-w_i; the theorem's
polynomial coaction uses w_i, so there is no accidental switch to the contragredient
action of the separate field lemma. The weight component is Mathlib's existing map,
and its vanishing conclusion includes total-degree homogeneity through `Vanishes`.
The final single group-algebra coefficient is exactly t^m f_m. No clause forces
finite freeness or excludes an empty scheme or a nonreduced base.

During compilation I corrected only elaboration: the grading instance needs a reducible
`letI` inside definitions to match the existing Proj, and monoid-algebra coefficients
use `AddMonoidAlgebra.single`, not the distinct bare Finsupp encoding. The final theorem
signature contains no `let`, `show`, auto-bound variables or file-local instances.
All helpers have source and blueprint docstrings and are listed in lean.declarations.
