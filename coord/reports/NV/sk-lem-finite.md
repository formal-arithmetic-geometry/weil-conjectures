## Worker report

The module `Sheaf.Paper.PoincarePointFiniteness` states `sk-lem-finite` in four
coefficient-specific theorems. Every theorem has exactly `by sorry` as its proof.
There are no new mathematical definitions or nodes, no dependency-node changes,
and no statement correction or disputed assertion. The node copy changes only `lean`.
The main record names the finite theorem; `lean.declarations` lists all four
statements and the five instance aliases used to elaborate them.

Source checked: main-20261015 `sec-poincare-duality/sk-lem-finite/_section.md`,
its complete proof, and the current DAG statement and proof. The DAG expands the
unit's fixed-setting shorthand and spells out the four point complexes. The Lean
follows that expansion without imposing properness, exceptional-adjoint
admissibility, a Weil structure, or a cohomological-degree-zero restriction on K.

Hypothesis-by-hypothesis correspondence:

- The primes p, l, exponent r>=1, q=p^r, finite base field and specified algebraic
  closure are `D : FiniteFieldDatum.{u}`, `l : ℕ`, `[Fact l.Prime]`, and
  `hl : l ≠ D.p`. The fields `D.prime`, `D.exponent_pos`, `D.cardinality_eq`,
  `D.card_base`, and `D.isAlgClosure` provide exactly the fixed finite-field data.
- A finite extension E/Q_l is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]`. Its integers, chosen uniformizer and positive
  quotients are the existing `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer` and `Padic.coefficientExtensionRing`.
  An abstract finite extension gives the same finite coefficient stage as a
  chosen embedded copy; at the Qbar stage the actual embedded field is retained
  by the recorded common-stage category. `Ω` is an arbitrary specified algebraic
  closure of `Padic l`, not a selected replacement closure.
- Nonnegative relative dimension is `d : ℕ`. All geometric hypotheses are the
  recorded `S : AlgebraicGeometry.PoincareDualitySetting D.k₀ d`: its model map
  is separated, quasi-compact, smooth of relative dimension d, and geometrically
  connected. Smoothness supplies local finite type. The coefficient and closure
  data omitted by this upstream geometric bundle are supplied explicitly by D,
  l, E and, in the algebraically closed case, Ω.
- X is literally `(D.geometricFiber (Over.mk S.modelStructureMorphism)).left`.
  Its recorded `Over` structure map is a_X to `Spec D.k`. This is the same
  pullback as `S.geometricFiber D.k` and `S.structureMorphism D.k`.
- `c : Compactification (X ↘ Spec (.of D.k))` supplies the existing compact-support
  construction's presentation data. It is arbitrary, not an additional geometric
  property: the separated finite-type structure map admits compactification.
  The recorded constructions are independent of this presentation. Ordinary
  cohomology is also included; properness is never imposed to identify the two.
- Finite K is `finiteTorConstructibleCategory l E n hn X`, with `n : ℕ` and
  `hn : 1 ≤ n`. Integral K is `finiteTorConstructibleIntegralCategory l E X`.
  Its `.property.1` supplies exactly the existing constructible object accepted
  by integral sections, while its common finite-reduction Tor condition remains
  part of the hypothesis. Rational and Qbar inputs use
  `finiteTorFieldCoefficientCategory` applied to the recorded rationalized and
  general common-stage algebraically closed constructible categories. This is
  the dependency's identity alias, imposing no extra field-stage condition.

Clause-by-clause correspondence:

- In each theorem the first set contains exactly the recorded ordinary and
  compact section complexes. The second set `{C, (ihom C).obj (𝟙_ _)}` contains
  that complex and its point RHom into the coefficient ring. Thus the two nested
  universal quantifiers assert the conclusion for C, C_c, C^vee and C_c^vee;
  they do not use a sheaf dual or add an arbitrary point-complex input.
- At every stage `CategoryTheory.IsDualizable B` is perfectness in the recorded
  `sk-def-perfect` sense, for the ordinary module derived tensor product.
- `poincarePointFiniteness_finite` additionally asserts
  `DerivedCategory.TStructure.t.bounded B`, `Finite` of every cohomology module's
  underlying set, and `DerivedCategory.finiteTorAmplitude (ModuleCat ...) B`.
  This is finite, not merely finitely generated, cohomology.
- `poincarePointFiniteness_integral` additionally asserts boundedness and
  `Module.Finite` over the lifted O_E for every cohomology module. The statement
  `∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ...` asserts perfectness and Tor amplitude [a,b]
  for each actual derived quotient
  `(pointReductionModuleTensor l E n).obj B`. This functor means exponent n+1,
  so every positive reduction is present and the interval does not depend on n.
  Each of the four B has such an interval. Equivalently one can choose a single
  interval for all four by taking the minimum of their lower bounds and maximum
  of their upper bounds; the finite choice of four does not affect uniformity.
- `poincarePointFiniteness_rational` uses the actual E-module sections and asserts
  `pointFiniteDimensional E B`, whose definition is finite cohomological support
  and finite-dimensional cohomology in every integer degree.
- `poincarePointFiniteness_qbar` uses `pointFdQbarRealization l Ω` on the actual
  common-stage ordinary and compact section objects, then the point dual in
  D(Ω). It asserts `pointFiniteDimensional Ω B`. The realization is the recorded
  canonical scalar extension from the input's finite coefficient field, so no
  field of definition or common-stage descent is discarded.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.PoincareDualitySetting`:
  `AlgebraicGeometry.PoincareDualitySetting`, including its full structure and
  geometric-fibre/structure-morphism definitions (`sk-def-set`, upstream closed).
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructibleCategory`,
  `finiteTorConstructibleIntegralCategory`, and `finiteTorFieldCoefficientCategory`.
  The finite and integral predicates and every component of their definitions
  were read, rather than substituting the older etale categories.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`, through its public imports
  `OrdinaryCompactWeilCohomology` and `OrdinaryCompactCohomology`: the
  `finiteOrdinarySections`, `finiteCompactSections`, `integralOrdinarySections`,
  `integralCompactSections`, `rationalOrdinarySections`, `rationalCompactSections`,
  `qbarOrdinarySections` and `qbarCompactSections` signatures and definitions.
  This lemma needs the retained coefficient-complex interface, not its later
  Frobenius-retaining sheaf specialization.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`:
  `CategoryTheory.IsDualizable` (`sk-def-perfect`, upstream closed).
- Supporting recorded constructions: `FiniteFieldDatum.geometricFiber` from
  `Sheaf.Paper.FiniteFieldFiber`, `DerivedCategory.pointFiniteDimensional` from
  `PointFdComplexes`, `DerivedCategory.pointFdQbarRealization` from
  `PointFdQbarCategory`, and `pointReductionModuleTensor` from
  `PointSectionsDerivedReduction`. The latter is the genuine left-derived
  tensor with the quotient module in degree zero, not an exact underived tensor.
- Existing ordinary module tensor/Hom/Tor APIs come from upstream
  `WeilConjectures.CategoryTheory.DerivedCategory.Perfect` and its public imports.
  The stated dimension-bound proof prerequisite is imported privately from
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
  `thm-pod-point-perfectness` has no published declaration in the node read for
  this delivery, so no fictitious proof import or duplicate statement is added.

The five helper instances contain only existing constructions. Three expose the
model's finite-type, quasi-compact and separated structures through `Over.mk`;
one is the standard separated pullback instance. `poincarePointModuleDerived`
explicitly uses `HasDerivedCategory.ofIsGrothendieckAbelian` for ordinary
coefficient modules. The broad recorded dependency imports a larger-Hom standard
module localization, which otherwise prevents inference of the native closed
monoidal API. This alias selects the existing small-Hom construction; it chooses
no new tensor, dual, coefficient ring, or equivalence. The reduction Tor predicate
also has explicit universes, with no new site/coefficient universe equality.

Edge cases checked against the source: n=1 occurs directly at finite level and
as n=0 in the integral reduction index; no exponent-zero coefficient quotient is
used. The zero complex and all integer shifts are covered, including the point
with K=Λ[-1], whose cohomology need not lie in [0,2d]. Dimension zero and the point
are allowed. Nonproper smooth examples such as affine space are allowed. No
nonzero-object condition or extra connectedness condition on a point complex is
introduced. The empty scheme is excluded only insofar as the original geometric
connectedness setting excludes it. The integral interval is attached to the
single K and remains uniform through all positive reductions. Field inputs need
not be specified by an arbitrary adic-sheaf model.

Searches for an existing exact statement (2026-10-18):

- `msearch.py ... leanfinder`: "global sections and compact support cohomology of
  constructible finite Tor complexes are perfect at all coefficient stages".
  Eight hits concerned derived t-structure bounds and unrelated K-projectivity;
  none stated this result.
- `msearch.py ... leansearch`: "perfect point complexes ordinary compact support
  cohomology finite integral rational algebraically closed coefficients".
  Eight hits concerned topological perfect spaces and perfect fields; no match.
- `msearch.py ... loogle`: "DerivedCategory.IsPerfect,
  AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections".
  No hits; the service does not index the project's IsPerfect declaration.
- `msearch.py ... grep 'IsPerfect|PointPerfect' CategoryTheory`: no Mathlib hits.
- `rg` in Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` checked the proposed names; no collisions.
  Concept searches and `grep -rn 'sk-lem-finite'` located upstream
  `EtaleCohomology/PoincareDuality/PointPerfect.lean`, read in full for its
  finite, integral, rational and adic signatures. Its finite/integral theorems
  use etale sheaf complexes, its rational clause treats scalar extensions of
  integral representatives, and its Qbar clause uses the older AdicSheaf
  category. It supplies related perfectness clauses but not the complete
  current intrinsic/common-stage statement with its explicit uniform reduction
  clause. It is therefore not an exact existing binding for this node.

Validation: `scompile.py NV sk-lem-finite` compiled the delivered module cleanly
as both a sandbox file and its actual library module, with server confirmation.
Only the expected theorem `sorry` warnings are permitted. Exploratory probe files
were removed before delivery. The prescribed dry run and push are performed next.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
