## Worker report

Wrote `lean/Sheaf/AlgebraicTopology/CompleteSegalWalkingIsomorphism.lean`, with the sole
statement `SSet.BisimplicialDivision.complete_segal_walking_isomorphism` and a `sorry`
proof. No definitions, auxiliary theorems, new nodes, or dependency repairs are needed.
The module and declaration docstrings cite Joyal–Tierney Lemma 4.2 and Rezk Theorem 6.2 /
Proposition 6.4. The theorem docstring gives all six proof steps, including the strict/path
Segal-product comparison and the identification of the two homotopy-category conventions.

Clause-by-clause correspondence:

- A bisimplicial set is `X : BisimplicialDivision.BSet.{u}`. This is the dependency's
  product-index functor, with arbitrary explicitly bound universe `u`.
- Vertical Reedy fibrancy is `hReedy : verticalFibrations (terminal.from X)`, the
  dependency's boundary-division Kan-fibration test for the terminal morphism.
- The homotopy Segal hypothesis is exactly
  `hSegal : HomotopySegal.IsHomotopySegalSpace (Functor.curry.obj X)`.
  Currying retains both simplicial coordinates and all operators.
- The ordinary groupoid with objects 0 and 1 and unique arrows is Mathlib's
  `CategoryTheory.WalkingIso`, the codiscrete category on `ULift Bool`. Its ordinary
  nerve is `SSet.coherentIso.{u}`; this is not a freely chosen interval or an
  arbitrary categorical-equivalence object.
- The chosen endpoint is `coherentIso.x₀`, the vertex `WalkingIso.zero`.
  `SSet.yonedaEquiv.symm coherentIso.x₀` is therefore the specified
  `u₀ : Δ[0] ⟶ coherentIso`, in every degree selecting the all-zero simplex.
- The actual restriction `u₀ backslash X` is
  `leftMap (SSet.yonedaEquiv.symm coherentIso.x₀) (𝟙 X)`.
  Its source is `leftDivision coherentIso X` and its target is
  `leftDivision Δ[0] X`, exactly the two division objects in the statement.
  Evaluation on the outer identity simplex canonically identifies the target with
  `X₀`; it is sufficient to retain the displayed division target rather than add
  a second endpoint/evaluation construction.
- Completeness is the existing `CategoryTheory.SegalSpace.IsComplete X`.
  Unfolding it gives `IsSegal X` and the existence of a factor of the actual `s₀`
  through `equivalenceArrows X`, with its composite with the inclusion equal to
  the actual outer degeneracy, and that factor a realization weak equivalence.
  Its factor is unique because the inclusion is mono: this is the specified
  degeneracy, not an arbitrary equivalence from the same source to the same target.
- `equivalenceArrows X` is the existing union of components in `X₁` containing
  equivalence arrows. `IsEquivalenceArrow` uses a reverse edge and both identity
  equations in strict mapping-fibre components, represented by triangles. Under
  `hReedy` the endpoint-pair map is a Kan fibration; the constant-path comparison
  to the recorded homotopy fibres is a weak equivalence and preserves identities
  and triangle composition. Thus these are exactly the isomorphisms in the node's
  `hX`. This identification is spelled out in proof step 2, not assumed as an
  additional hypothesis. The `IsSegal` conjunct follows from `hReedy` and `hSegal`
  by proof step 1 and adds no restriction to the class of spaces quantified here.
- The equivalence is the outer `↔`. The right side is `Fibration p ∧
  Enhanced.IsWeakHomotopyEquivalence p` for precisely that restriction `p`.
  These are the recorded Kan horn-lifting property and realization weak equivalence;
  their conjunction is exactly trivial Kan fibration in the stated Kan model
  structure. This retains boundary lifting in dimension zero as well.

Dependencies used, with their recorded modules read in full at the needed signatures:

- `Sheaf.AlgebraicTopology.BisimplicialReedyDivisionCalculus`:
  `SSet.BisimplicialDivision.BSet`, `leftDivision`, `leftMap`, `verticalFibrations`,
  `bisimplicial_reedy_division_calculus`.
- `Sheaf.CategoryTheory.SegalDKDiagonalEquivalence`:
  `SSet.segal_dk_diagonal_equivalence`, whose public
  `Sheaf.CategoryTheory.HomotopySegalSpace` import supplies
  `SSet.HomotopySegal.IsHomotopySegalSpace` and its path-model component conventions.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, with the fixed Mathlib Kan-fibration
  structure and the realization-based weak equivalences (not an arbitrary model witness).
- `Sheaf.CategoryTheory.SegalSpace`: `CategoryTheory.SegalSpace.IsComplete`,
  `IsSegal`, `equivalenceArrows`, `IsEquivalenceArrow`, and `SameMappingComponent`.
  Added the already landed `def-coef-segal-space` to `stmt_deps`, as authorized by
  brief-stage2 §5, because it owns the exact completeness predicate used here.
- `Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso`: `SSet.coherentIso`,
  `SSet.coherentIso.x₀`, and the underlying `CategoryTheory.WalkingIso`.
- Proof imports: `Sheaf.AlgebraicTopology.KanPullbackPathComparison`
  (`SSet.Enhanced.kan_pullback_path_comparison`),
  `Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`
  (`SSet.Enhanced.kan_homotopy_pullback_invariance`),
  `Sheaf.CategoryTheory.ReedyModelStructure`
  (`HomotopicalAlgebra.Reedy.model_structure`), and
  `Sheaf.AlgebraicTopology.SegalEquivalenceClassifier`
  (`SSet.SegalSpace.segal_equivalence_classifier`). All recorded proof dependencies
  have their modules imported; no import is omitted for a cycle.

Edge cases checked before writing:

- Empty simplicial space: both division objects and the object space are empty;
  the empty identity is a trivial fibration, and the degeneracy equivalence holds.
- Terminal space: both conditions hold.
- A category nerve made discrete in the inner direction is Reedy fibrant and
  homotopy Segal. Both conditions hold exactly when each object has exactly one
  outgoing isomorphism, namely its identity: a nonidentity isomorphism between
  distinct objects also makes completeness fail, even if all automorphism groups
  are trivial. For a one-object nontrivial group both conditions fail; endpoint
  restriction is a Kan fibration but not a weak equivalence. Thus the weak
  equivalence condition was not inadvertently replaced by fibrancy alone.
- The boundary inclusion in dimension zero is retained by the Kan model's notion
  of trivial fibration. No nonempty-object or chosen-basepoint hypothesis is added.
- The theorem uses one arbitrary simplicial-set universe, as the division-calculus
  node requires. Both objects of the walking groupoid are lifted to that universe;
  there is no extra equality between independent universes.

Searches for an existing theorem (2026-10-17):

- `msearch.py ... leanfinder` with query “A Reedy fibrant homotopy Segal space is
  complete if and only if evaluation from its walking isomorphism space at the
  initial endpoint is a trivial Kan fibration”: 8 hits, strict Segal predicates
  and general fibrant-object results; no completeness criterion.
- `msearch.py ... leansearch` with query “A Segal space is complete if and only if
  restriction from the walking isomorphism to an endpoint is a trivial fibration”:
  8 hits; strict Segal results and `HomotopicalAlgebra.trivialFibrations`, whose
  signature confirms it is the intersection of fibrations and weak equivalences.
  No theorem with this criterion.
- `msearch.py ... loogle 'SSet.coherentIso, SSet.StrictSegal'`: 0 hits.
  An earlier query including `CategoryTheory.SegalSpace.IsComplete` gave 0 hits
  with an unknown-identifier note, since that is a project declaration; inspected
  its actual source directly rather than treating that search as absence evidence.
- `msearch.py ... grep 'walking.*isomorphism|complete.*Segal|Segal.*complete'
  AlgebraicTopology`: 3 hits, all in Mathlib's `CoherentIso.lean`. Read its full
  nerve, endpoint and codiscrete-groupoid definitions and reused them.
- Direct `rg` of `lean/Sheaf/AlgebraicTopology`, `lean/Sheaf/CategoryTheory` and
  `WeilConjectures` for `IsComplete|complete_segal_walking|walking_isomorphism|
  complete.*walking|walking.*complete` found the existing Segal completeness
  definition, classifier helpers and completion theorem, but no endpoint criterion.
- `grep -rn 'lem-coef-complete-segal-walking-isomorphism' WeilConjectures` and
  `rg` of `dag/lean_names_upstream.json` for the proposed declaration: no match.

Sources opened online: [Joyal–Tierney, Lemma 4.2](https://arxiv.org/html/math/0607820)
and [Rezk, Theorem 6.2 and Proposition 6.4](https://arxiv.org/html/math/9811037).
The first states the division endpoint criterion; the second compares the degeneracy
and collapse forms of completeness. Archival copies remain WANTED as the node records;
no literature or coordinator file was edited.

Validation: `scompile.py Q73 lem-coef-complete-segal-walking-isomorphism
lean/Sheaf/AlgebraicTopology/CompleteSegalWalkingIsomorphism.lean` compiled the module
cleanly, including its side-only division and classifier imports. All variables and
universes are explicitly bound (`autoImplicit false`). The only postponed proof is
the item's theorem. No statement dispute, statement correction, or dependency fault.

## Second reading by Q73

I reread the item node, its source (Joyal--Tierney, Lemma 4.2, and Rezk, Theorem 6.2
and Proposition 6.4), the dependency records, and the Lean declaration
`SSet.BisimplicialDivision.complete_segal_walking_isomorphism`.

The node's objects and hypotheses match as follows. The ordinary groupoid
`mathcal J` with two objects and one morphism in every ordered hom-set is rendered by
Mathlib's `CategoryTheory.WalkingIso`, and its nerve `J` by `SSet.coherentIso`. The
chosen endpoint `u_0 : Delta[0] -> J` is rendered by
`SSet.yonedaEquiv.symm coherentIso.x₀`; this selects the zero vertex in every degree.
The bisimplicial set `X` is `X : BSet.{u}` from the division-calculus dependency.
Vertical Reedy fibrancy is exactly
`hReedy : verticalFibrations (terminal.from X)`. The homotopy-Segal hypothesis is
exactly `hSegal : HomotopySegal.IsHomotopySegalSpace (Functor.curry.obj X)`; it retains
all outer and inner operators and uses the dependency's path-model convention.
The completeness predicate is `CategoryTheory.SegalSpace.IsComplete X`, from the
landed `def-coef-segal-space` declaration cited in `stmt_deps`; its factor is the
actual outer degeneracy through the union of equivalence-arrow components. The
node's $X_{\mathrm{eq}}$ is therefore the same subcomplex, since the strict mapping
fibres and the homotopy mapping fibres have the same components under these
hypotheses.

The conclusion has the same quantifier order and both clauses. The Lean map
`leftMap (SSet.yonedaEquiv.symm coherentIso.x₀) (𝟙 X)` has source
`leftDivision coherentIso X` and target `leftDivision Delta[0] X`, exactly
`u_0 backslash X -> Delta[0] backslash X`; the latter is the canonical division
presentation of `X_0`. The right side writes the node's trivial Kan fibration as
`Fibration p ∧ Enhanced.IsWeakHomotopyEquivalence p`, the Kan--Quillen dependency's
equivalent recorded characterization, including the degree-zero boundary condition.
No hypothesis is added or strengthened, and no conclusion is weakened.

Edge cases checked again: empty `X` (both sides are vacuous in the corresponding
empty division objects), terminal `X`, `n = 0` boundary lifting, a discrete nerve,
a nontrivial one-object group, and a category nerve with a nonidentity isomorphism.
The empty index and empty object cases introduce no nonemptiness or chosen-basepoint
hypothesis; the single universe `u` is used consistently for `X`, `J`, and all
division objects.

The existing-definition searches were checked against Mathlib's coherent-iso nerve,
the project `SegalSpace` and `HomotopySegalSpace` declarations, `WeilConjectures/`,
and the DAG name index. LeanFinder/LeanSearch/Loogle searches for the completeness
criterion and direct `rg` searches for walking-isomorphism completeness found no
duplicate theorem. The exact `WalkingIso` and completeness predicates were reused.

No mismatch was found. The worker's added `def-coef-segal-space` statement dependency
is necessary and present in the sandbox node; the Lean file and node `lean.statement`
remain verbatim aligned. No Lean, node, or dependency repair was made in this second
reading. The prescribed `scompile.py` check passed with only the postponed theorem
proof.
