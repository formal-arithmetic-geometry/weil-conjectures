## Worker report

The item module is `Sheaf.AlgebraicGeometry.SingularPointJetWeightBounds`, with theorem
`AlgebraicGeometry.ProjectiveCurveJets.singular_point_jet_weight_bounds`. Its only proof is
`sorry`. The companion definition module supplies real constructions and predicates; it
contains no postponed theorem or data chosen from an unproved existence assertion.

The source was read at https://arxiv.org/html/0810.2340, Section 3.2 Theorem 8 steps (3)--(6)
and its subsequent cusp and tangent-line calculations. The latest blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
was read: this is a supporting alteration-route input, not the blueprint unit's own statement.
The node's coefficient is half Morrison's e_F. Its expanded seven-step proof is retained in
the theorem docstring, including the exceptional tangent-line coefficient.

Hypotheses and objects, one by one:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Ambient projective space: `Ambient k (n + 2)`, definitionally the same coordinates
  as `HilbertPlucker.Coordinates n`. This covers every possible one-dimensional closed
  projective subscheme: fewer than two coordinates cannot have dimension one.
- Connected closed subscheme: `X`, `[ConnectedSpace X]`, `i`, `[IsClosedImmersion i]`.
- Dimension one: `hdim : topologicalKrullDim X = 1`.
- Generically reduced: `hgeneric` says every generic-point local ring is reduced, using
  `genericPoints X`, without requiring X itself reduced.
- Reduced support: `Reduction X` is the existing nilradical subscheme, and `reductionMap X`
  its canonical immersion. No arbitrary reduction or comparison map is supplied.
- Nondegenerate reduced support: `hspan` says a homogeneous linear form vanishing at all
  its points is zero. Pointwise vanishing detects the restricted section on the reduced D.
- Every reduced component of degree at most three is rational normal: `hlow` quantifies over
  the actual `irreducibleComponents (Reduction X)`, uses the canonical reduced component
  immersion, and `componentDegree` on its canonical normalization. `IsRationalNormal`
  requires a k-isomorphism with P¹ and surjectivity of actual ambient linear-form restriction
  onto hyperplane sections. On this closed embedded curve this is precisely completeness
  of the degree-e linear system in its own span; it is not merely rationality of normalization.
- Weighted flags and a_F: `ρX`, `ρD` are existentially supplied with `IsRestriction`, which
  fixes their values chart by chart to dehomogenization times the twist generator, exactly
  as in the recorded bounded-weight theorem. `HasCoefficient` uses that theorem's actual
  `weight` and eventual monomial bases and quadratic O(m) estimate. No assumption on a_F
  or arbitrary map replaces the needed canonical objects.

Conclusions, clause by clause:

1. The first conjunct quantifies over p,t with `HasMultiplicity (Reduction X) p t` and
   `3 ≤ t`. It supplies b,w,a with `IsPointFlag`, sum weights = 1, `HasCoefficient ρX b w a`
   and `(t : ℚ) / 2 ≤ a`. `IsPointFlag` fixes exactly the zero/one flag of the point ideal.
2. The second conjunct quantifies over p and the actual labelled branch q. Ramification is
   `tangentImage ... = {0}`; this is the same as zero normalization tangent map because
   a closed immersion induces an injective tangent map. Its conclusion is degree ≥4 and
   a flag with `IsRamifiedFlag`, sum ≤7, `HasCoefficient` and a≥8. Natural weights express
   nonnegativity; the predicate imposes weights ≤4 and precisely order thresholds 4,3,2
   at weights 0,1,2. Equality of thresholds 3 and 2 rules out a weight-3 piece.
3. The third conjunct is conditional on every normalization branch tangent image nonzero
   and every singular local ring having multiplicity two. Singularity uses
   `¬ IsRegularLocalRing`; over this algebraically closed perfect field this is the usual
   singularity of a finite-type curve. For a multiplicity-two point without
   `HasSplitNodeCompletion`, it supplies a branch q, its common tangent-line equations
   (equal for every branch), and b,w,a. `IsTangentFlag` fixes weights 0,1,2 on tangent
   equations, additional point equations and their complement. Sum ≤3 and a≥7/2 follow.
   The final implication gives a≥4 when every branch's component degree differs from one;
   on an integral embedded curve degree one is exactly a line component. This quantifies
   over labelled branches, so includes two branches lying on the same component.
4. The final conjunct says `HasCoefficient ρX b w a ↔ HasCoefficient ρD b w a` for EVERY
   basis, integral nonnegative weight vector and rational a. This is coefficient invariance
   under the finite-length nilradical, including every displayed flag. Generic reducedness
   on this projective one-dimensional scheme already makes the nilradical have finite
   support and finite length, so no additional finite-length assumption is introduced.
5. The ordinary-node condition is the imported `HasSplitNodeCompletion`: the isomorphism
   of the completed local ring with `MvPowerSeries (Fin 2) k / (uv)` explicitly preserves
   the given structural k-map. There is no semistability hypothesis anywhere.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and
  its `Hom`; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`,
  `twistGenerator`, `twistOneSection`; `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.moduleCohomology` (inside `sections`) and `globalSectionsFunctor`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.Modules.degree`, used
  by imported `componentDegree` on the normalization and its structural k-map.
- `Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials`:
  `BoundedHilbertWeight.exists_uniform_bounded_hilbert_weights`; its public dependency
  `WeightedMonomialBasisWeight` supplies `LinearForms`, `sections`, `flag`, `weight`,
  `IsMonomialBasis`. The same types and chart formulas are used, rather than a new weight.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`; the generic clause uses the root
  ring predicate. `ConnectedSpace` is the nonempty connectedness definition of its node.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization`,
  `fromNormalization`; `Sheaf.AlgebraicGeometry.StablePointedCurve`:
  `Scheme.normalizedComponentMap`; these are used through the branch interface.
- `Mathlib.RingTheory.Length`: `Module.length`; `Mathlib.RingTheory.AdicCompletion.Basic`
  and `.Algebra`: `AdicCompletion`; `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace`,
  `schemeTangentMap`; all appear inside the reused branch interface.
- `Sheaf.AlgebraicGeometry.DivisorModule`: divisor valuation/order convention; orders here
  are explicitly maximal-ideal powers in the normalized branch local rings.
- `Sheaf.AlgebraicGeometry.BranchMultiplicityTangentCriterion`: `Branch`, `Component`,
  `localMap`, `componentDegree`, `HasMultiplicity`, `tangentImage`, `linearGerm`,
  `lineEquations`, `HasSplitNodeCompletion`. The twelve definitions are now attached to
  `def-sfb-projective-curve-branch-data`, cited in stmt_deps. The theorem node stays only
  in proof_deps; no definition selects data from its theorem.
- `def-weil-pbc-scheme-reduction` is added to stmt_deps for the existing nilradical
  construction. The abbreviations `Reduction` and `reductionMap` simply expose that
  construction and do not replace its definition. Its declaration signature was read.
- Plain proof imports are `NormalizationJetCodimension`, `CoherentFiniteSupportSkyscrapers`,
  and Mathlib's Noetherian and quasi-compactness files, as required by the proof DAG.
  The branch and bounded-weight proof imports are already public statement dependencies.

Edge cases checked: n=0 (ambient P¹) is admitted, without a false r≥4 restriction; empty X
is excluded exactly by connectedness/dimension. A smooth point has multiplicity one and does
not trigger the multiple-point or double-point conclusions. Branches retain component labels
and distinct points on one normalization. Characteristic two and positive characteristic are
admitted. Zero forms and forms identically zero on a branch satisfy every order condition.
Empty jet graded pieces are allowed. A line tangent to a nonlinear branch retains 7/2 instead
of 4. Natural weight zero everywhere is allowed by coefficient invariance. All low degrees m,
including m=0, are excluded only from eventual asymptotics; the restriction arrows themselves
are defined in every degree. Generic points are not silently declared closed: the statement
quantifies over all p; its ramified and multiplicity hypotheses exclude generic points on a
reduced curve. No finite-set nonemptiness or universe equality has been added.

Searches: msearch LeanFinder on Hilbert weight lower bounds for singular-point jet
filtrations returned only multivariate power-series weighted-order lemmas. Loogle
`MvPowerSeries, Module.length` returned zero hits. msearch grep
`jet.*weight|singular.*Hilbert|rationalNormal` in AlgebraicGeometry returned zero hits.
The new node records fresh LeanSearch, LeanFinder and grep outputs verbatim. The local
`rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` found the branch interface,
actual weights and an ordinary-node predicate, all inspected. The exact item-id grep in
`lean/WeilConjectures` found no existing theorem. DAG searches found the unstated
integral-curve span/degree theorem and projection bounds mentioning rational normal curves,
but no separate declaration. `tools/blueprint_refs.py search 'rational normal'` found no unit.
No statement correction or STATEMENT-DISPUTED issue is needed.

Validation: scompile.py compiled both delivered modules separately in dependency order,
including their library-mode checks, with no errors or warnings. All universes and variables
are explicitly bound and both files disable autoImplicit and relaxedAutoImplicit.

## New nodes

`def-sfb-projective-curve-jet-weight-data` defines the specialized predicates for the three
geometric jet flags, canonical restriction characterization and its actual quadratic weight
coefficient, and rational normality as the complete hyperplane system on P¹. Its module also
exposes the existing reduction, linear coefficient vectors, point and branch vanishing, and
the actual linear-section map needed for that predicate. Source: Morrison §2.2 and §3.2,
Theorem 8(3)--(6). It reuses every existing normalization/tangent/length/completion/weight
notion; the searches listed in its mathlib_searches record found no declaration of these
specialized flags or rational normality. This is a definition node, with empty proof fields,
real data throughout, and it is cited by the item. Its blueprint ancestor is null, as the
prescribed ancestor tool reports; the complete inherited via route is retained.

`def-sfb-projective-curve-branch-data` attaches the twelve existing plain definitions
`Ambient`, `Component`, `Branch`, `localMap`, `branchIdeal`, `componentDegree`,
`HasMultiplicity`, `tangentImage`, `linearGerm`, `lineEquations`, `HasOrderAtLeastTwo`,
and `HasSplitNodeCompletion` in `Sheaf.AlgebraicGeometry.BranchMultiplicityTangentCriterion`.
It is `existing: true` and supplies no new Lean module. The statement describes each
definition, without asserting the branch-multiplicity theorem. Source: Morrison §3.2,
Theorem 8(4)--(6), and the Stacks places in the existing docstrings. Fresh LeanSearch,
LeanFinder and Mathlib grep outputs are recorded verbatim; local source and DAG searches
found the exact twelve declarations but no separate definition node for them. This
attachment is the correction explicitly requested by immutable-head review 21038f6b457d.

## Second reading by Q66

Author self-check for direct delivery; independent review belongs to the maintainer.
I reopened the original node, both Lean files and all signature predicates. I checked that
point weights are 0/1 and sum exactly 1, cusp weights are precisely 0/1/2/4 with missing
pieces permitted and sum at most 7, and tangent weights are 0/1/2 and sum at most 3. The
rational lower bounds are typed as ℚ, including 7/2 rather than natural division. The
stronger tangent conclusion uses the degrees of ALL branches, including repeated component
labels. I checked the node's finite-nilradical clause against the final iff on actual minimum
weights, not an arbitrary coefficient function. I removed initially explicit closed-point
premises so the Lean quantifies exactly as the node does; the local hypotheses automatically
force the relevant points to be closed on the reduced finite-type pure curve. I fixed the
linear-section construction to use the existing `tensorPullbackTopSection`, which restricts
the unit to the top open before applying its canonical scalar action. No definition uses
sorry, no geometric object is replaced by a freely chosen object, and the only sorry belongs
to the named item theorem carrying the complete source-based proof plan.

## Returned delivery repair (H2+H12)

The immutable-head review of 21038f6b457d found a definition/theorem dependency error:
the item and its new jet-data definition node cited the branch-multiplicity theorem in
stmt_deps even though their signatures only use its module's plain definitions.
I added `def-sfb-projective-curve-branch-data` with `lean.existing: true`, the existing
module and all twelve definitions, including `branchIdeal` and `HasOrderAtLeastTwo`.
Both statement dependency lists now cite this definition node instead of the theorem;
the jet-data node's textual citation is updated as well. The original theorem remains
in the item's proof_deps. No Lean file or mathematical assertion changed.

I compared the restored sandbox with current main: before the repair, the item's only
changed fields were lean and stmt_deps. The delivery wrapper refreshes its base and
builds a new commit against current main. I reopened the existing twelve definitions
and checked their full bodies: none chooses data from the branch-multiplicity theorem.
The new record's main signature is verbatim `def Branch (D : Scheme.{u}) (p : D) : Type u`;
its declarations list names all twelve. The new node has empty proof/proof_deps, no
module copy, and only definition-node statement dependencies. Both unchanged delivered
Lean modules are compiled again with scompile.py before the dry run and repaired push.
