## Worker report

The module `Sheaf.TraceFormula.GeometricNodeFittingDepth` states
`AlgebraicGeometry.geometricNode_fitting_depth`, with one whole-proof `sorry` and
no new definitions. The node changes only in `lean`. The five-step proof docstring
follows the node's proof, including coefficient-field rectification of the initially
nonlinear completion isomorphism, completed differentials, faithful-flat contraction,
and the depth formula.

Hypothesis and clause correspondence:

- An algebraically closed field K is `(K : Type u) [Field K] [IsAlgClosed K]`.
- A finitely generated K-algebra R is `(R : Type v) [CommRing R] [Algebra K R]
  [Algebra.FiniteType K R]`. This is exactly the algebra-instance version of the
  recorded `RingHom.FiniteType (algebraMap K R)`, by `RingHom.finiteType_algebraMap`.
- The maximal ideal is `(q : Ideal R) [q.IsMaximal]`; Mathlib supplies primality.
- Rationality through the structure map is precisely
  `hrational : Function.Bijective (algebraMap K (R ⧸ q))`. This does not substitute
  an abstract ring equivalence for the required structure-map identification.
- B is the recorded `Localization.AtPrime q`. The ideal n=qB is
  `Ideal.map (algebraMap R (Localization.AtPrime q)) q`.
  `IsLocalization.AtPrime.map_eq_maximalIdeal` identifies it with
  `IsLocalRing.maximalIdeal (Localization.AtPrime q)`.
- The completion is `AdicCompletion (IsLocalRing.maximalIdeal B) B`, written out
  with B's full expression. Thus it is exactly the n-adic completion.
- The hypothesis `hnode : Nonempty (completion ≃+* (MvPowerSeries (Fin 2) K ⧸ ...))`
  is existence of a ring isomorphism. The relation ideal is the singleton span of
  `MvPowerSeries.X 0 * MvPowerSeries.X 1`. Neither K-linearity nor a chosen
  topology-compatible presentation is assumed.
- The first conclusion quantifies over every finite free surjection
  `π : (Fin n → R) →ₗ[R] KaehlerDifferential K R`. Its index-one ideal is the
  recorded `π.presentationFittingIdeal 1`; `Ideal.map` extends it to B, and the
  equality is exactly J_B=n. Finite type implies that differentials are finitely
  generated, so such presentations exist. This universal presentation formulation
  is the presentation-independent Fitting assertion, not an additional hypothesis.
- The second conclusion is `IsLocalRing.depth (R := B) B = 1`.
- The third is `Ideal.depth (Ideal.map (algebraMap B completion) (maximalIdeal B))
  completion = 1`. Since B is Noetherian local, its completion is local and
  `AdicCompletion.maximalIdeal_eq_map` identifies this very ideal with its maximal
  ideal. Consequently this is exactly depth of the completed local ring, using
  the recorded definition `Ideal.depth` underlying `IsLocalRing.depth`. The two
  depth equalities express the node's chain depth B = depth completion = 1.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, `RingHom.FiniteType`,
  and `RingHom.finiteType_algebraMap`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `IsLocalization.AtPrime.map_eq_maximalIdeal`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`
  with its commutative ring and canonical algebra structures.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth`, `IsLocalRing.depth`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its universal
  derivation `KaehlerDifferential.D`, and `linearMapEquivDerivation`.
- `Sheaf.RingTheory.PresentationFittingIdeal`: `LinearMap.presentationFittingIdeal`
  and `LinearMap.presentationFittingIdeal_independence_baseChange`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed
  field clause of `def-weil-algebraic-closure`'s mathlib match.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and `MvPowerSeries.X`.

All recorded statement dependencies have usable declarations, so no dependency
repair or new node is needed. The stated proof dependencies are imported privately:
`Algebra.separable_closed_point_formal_presentation`,
`KaehlerDifferential.isLocalizedModule_map`,
`AlgebraicGeometry.completedJacobianDifferentials`, the Mathlib completion-flatness
and faithfully-flat contraction APIs, regular sequences, and
`IsLocalRing.depth_eq_add_of_flat_local`. The fitting and depth dependencies are
already public statement imports. The two proof nodes
`lem-trf-rational-nodal-completion-algebra` and
`lem-trf-binary-quadratic-model-depth` have no recorded Lean declaration in this
snapshot, so they have no corresponding import; neither is required to type the
statement.

Source checked: `literature/stacks-project/curves.tex`, lemma-nodal-algebraic
(Tag 0C49), lemma-fitting-ideal (0C4C), and lemma-nodal (0C4D), including the
algebraically closed proof's Jacobian presentation. The latest blueprint ancestor
`lem-trf-local-term-locality` now concerns contracting correspondences; this node
is the retained local-algebra auxiliary described in its existing split report.
No unit statement or source claim is changed.

Edge cases: u and v are independent and explicitly bound. The zero ring R has no
maximal ideal, so it supplies no case. The rationality map is the prescribed
structure map, including twisted abstract field identifications. A completion
isomorphism need not preserve that structure map. Characteristic 2 is included:
the gradient of uv is (v,u) without any division by 2. All finite presentation
sizes, including 0 and 1, remain quantified; in the nodal situation those small
surjections do not exist, and the separate depth clauses do not depend on them.
No finiteness of R as a K-module or dimension hypothesis on all of Spec R is added.
No statement fault or dispute was found.

Searches for existing statements (2026-10-24):

- msearch LeanFinder: "A rational ordinary node has first Fitting ideal of
  differentials equal to its maximal ideal and local depth one" returned smooth,
  unramified, etale, and cotangent-space criteria, none this assertion.
- msearch Loogle: `KaehlerDifferential, IsLocalRing` returned three formally smooth
  cotangent-complex criteria, not the nodal Fitting/depth statement.
- msearch grep: `nodal|Fitting|fittingIdeal` in `RingTheory` returned two unrelated
  Artinian Fitting-decomposition comments.
- msearch LeanSearch: "The first Fitting ideal of differentials at a rational
  ordinary node is its maximal ideal and the local ring has depth one" returned
  height and cotangent-space criteria, not this assertion.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for geometric-node and
  nodal-Fitting/depth names found related nodal-family modules, no exact statement;
  `grep -rn` for this node id in `lean/WeilConjectures` found nothing.
  `rg` for `geometricNode_fitting_depth` in those trees and
  `dag/lean_names_upstream.json` found no collision.

Validation: scompile.py compiled the file in both sandbox and library module
modes, each in 2.0 seconds, with no errors or warnings reported.

## Second reading by Q57

A separate self-review pass reopened the node and the completed file. It checked
that `hrational` names the actual algebraMap, `hnode` uses a ring equivalence,
the Fitting index is 1, both depth conclusions occur, the relation is uv, and
the universes impose no size identification. The use of maximalIdeal in the
completion and extended maximal ideal in its depth is justified by the two
canonical ideal equalities described above. No mismatch or change was found.
This is the worker's rereading; the dispatch brief reserves independent delivery
review for the maintainer and explicitly forbids starting another agent.
