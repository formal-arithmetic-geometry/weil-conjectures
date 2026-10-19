## Worker report

The module `lean/Sheaf/AlgebraicTopology/RealizationWeakEquivalence.lean` states
`SSet.Enhanced.realization_weak_equivalence_iff_kan_targets`.  It gives the exact
biconditional in the node.  The binders `P Q : SSet.{u}` and `v : P ⟶ Q` are the
simplicial sets and simplicial map in the node, with one fixed universe and no Kan,
nonemptiness, or injectivity hypothesis on `P`, `Q`, or `v`.

The left side, `IsWeakHomotopyEquivalence v`, is the dependency declaration
`SSet.Enhanced.IsWeakHomotopyEquivalence` from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; its definition is the realization
component bijection and all based homotopy-group bijections specified by
`def-cbc-enhanced-diagrams-cones`.  On the right, `W : SSet.{u}` is an arbitrary
Kan complex through the typeclass binder `[KanComplex W]`.  The internal functor
simplicial set is represented by Mathlib's `MonoidalClosed.pre v`, and
`(MonoidalClosed.pre v).app W` is exactly precomposition
`Fun(Q,W) -> Fun(P,W)`.  `SSet.mapπ₀` is Mathlib's map on edge-generated
components (`SSet.π₀`), and `Function.Bijective` renders the required bijection.

The proof is intentionally `sorry`, as required for stage 2.  Its source route is
Kerodon Corollary the project server (03X7), using Definition the project server (00UA): realization
weak equivalence is equivalent to a homotopy equivalence, and the realization--singular
adjunction identifies mapping components into Kan targets with topological homotopy
classes.  The converse tests against singular complexes of the realizations.  Empty
simplicial sets and empty Kan targets remain covered, since all quantifiers are
unrestricted and no `Nonempty` binder was added.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.IsWeakHomotopyEquivalence` (the node's `def-cbc-enhanced-diagrams-cones`).
- `Mathlib.AlgebraicTopology.SimplicialSet.PiZero`, `SSet.mapπ₀` and `SSet.π₀`.
- `Mathlib.CategoryTheory.Monoidal.Closed.Basic`, `MonoidalClosed.pre`.
- `Mathlib.AlgebraicTopology.SimplicialSet.KanComplex`, `SSet.KanComplex` (imported by
  the enhanced-diagrams module).

Searches for an existing declaration were made before writing.  `msearch.py` LeanFinder
for “A simplicial map realizes to a weak homotopy equivalence if and only if
precomposition induces bijections on edge components of mapping simplicial sets into
every Kan complex” returned only abstract model-category homotopy-class lemmas;
none has the realization/edge-component biconditional.  LeanSearch for the analogous
homotopy-class query returned `RightHomotopyClass.precomp_bijective_of_weakEquivalence`,
`SSet.toTop`, and `sSetTopAdj`, but no exact statement.  Loogle for
`HomotopicalAlgebra.RightHomotopyClass.precomp_bijective_of_weakEquivalence` found only
that forward abstract theorem.  Grep of Mathlib AlgebraicTopology for
`weakEquivalence.*(toTop|realiz)|((toTop|realiz).*[Ww]eak)|precomp_bijective_of_weakEquivalence`
found only the same model-category theorem.  Grep of the project found no declaration
for this node.  The complete query records are in `searches.jsonl`.

Edge cases checked: `P` and `Q` may be empty; `W` may be empty (the universal Kan
quantifier handles this); `v` need not be injective; neither source simplicial set is
assumed Kan; and all objects use the same explicit universe `u`.

Additional proof imports preserve the available DAG proof route:
`Sheaf.AlgebraicTopology.RealizationCWSubcomplex` (`SSet.realization_cw_subcomplex`),
`Sheaf.AlgebraicTopology.RealizationFiniteLimits` (`SSet.realization_finite_limits`),
`Sheaf.CategoryTheory.HomotopyEquivalenceWeak`
(`SSet.Enhanced.homotopy_equivalence_weak`), and `Mathlib.Topology.CompactOpen`
(`ContinuousMap.curry` / `ContinuousMap.uncurry`).  The two remaining proof-only nodes,
`lem-cbc-whitehead-cw-homotopy-inverse` and `lem-cbc-kan-realization-mapping-classes`,
have no recorded Lean module and supply no notion needed to type this statement;
no import can yet be added for them.  Their use is explicit in the six-step docstring.

The source pages https://kerodon.net/tag/03X7 and https://kerodon.net/tag/00UA
were read online.  The abstract Mathlib candidate's full signature was read at
`Mathlib/AlgebraicTopology/ModelCategory/Homotopy.lean:200`; it requires an abstract
model-category weak equivalence and states only one implication.  Local source and
side-project searches found no exact theorem.  `SSet.π₀.mk_eq_mk_iff` explicitly
identifies its quotient equality with `Relation.EqvGen` of the edge relation, so
using Mathlib components does not impose Kan conditions on the mapping spaces.

No statement correction, new node, dependency module, or disputed statement is needed.
The previous failure concerned a stage-1-reviewed node being reprocessed; the current
node has no `lean` record or `reviewed_lean`, and this delivery changes only `lean`.
No accepted split or mathematical statement is replaced.

## Second reading by Q73

I independently read the node, its sole statement dependency
`def-cbc-enhanced-diagrams-cones`, the delivered module, and the actual dependency
definitions. I read [Kerodon 03X7](https://kerodon.net/tag/03X7), Corollary the project server,
and [Kerodon 00UA](https://kerodon.net/tag/00UA), Definition the project server. These are the
node's actual source places, rather than Stacks tags or a Stacks .tex source.
03X7 applies to any simplicial map and equates its realization condition (2) with
00UA's Kan-target condition (1). Neither source imposes Kan conditions on the
source or target, injectivity, connectedness, or nonemptiness.

My object/hypothesis/conclusion checklist, matched against the Lean:

1. A fixed universe of simplicial sets: `universe u` and `P Q : SSet.{u}`.
   Verdict: exact; arbitrary `u`, with no universe equality or size instance added.
2. An arbitrary simplicial map from P to Q: `(v : P ⟶ Q)`.
   Verdict: exact; neither P nor Q is assumed Kan, and v has no property binder.
3. Geometric realization and its path-component bijection:
   `IsWeakHomotopyEquivalence v` unfolds to a conjunction whose first member is
   `Function.Bijective (componentsMap (SSet.toTop.map v).hom)`.
   I opened EnhancedDiagramsCones.lean: `componentsMap` uses `ZerothHomotopy`
   and sends a path class to the class of its image. `SSet.toTop` is Mathlib's
   realization, defined as the left Kan extension of topological standard
   simplices; SingularSet.lean documents the realization--singular adjunction.
   Verdict: the same realization and path components as the dependency node.
4. Every based homotopy group: the second member of the same predicate is
   `∀ (r : ℕ), 1 ≤ r → ∀ (x : SSet.toTop.obj P),
   Function.Bijective (homotopyGroupMap (SSet.toTop.map v).hom r x)`.
   The opened `homotopyGroupMap` postcomposes continuous cubical maps and their
   homotopies relative to the whole boundary. For r >= 1 postcomposition preserves
   concatenation; bijectivity expresses the required group isomorphism. Its
   basepoint is v(x), as required. Verdict: every positive degree and every source
   basepoint, with path components separately covering degree zero.
5. Equivalence of the two conditions: `↔`, rather than only an implication.
   Verdict: exact, in the same order as the node.
6. Every Kan test object in the fixed universe:
   `∀ (W : SSet.{u}) [KanComplex W]`. I read KanComplex.lean and
   CategoryWithFibrations.lean: the fibrancy abbreviation uses all positive
   dimensional horns, including outer horns, without a dimension-zero filler.
   Verdict: exactly all Kan targets, including the empty one.
7. The internal functor simplicial sets and precomposition:
   `(MonoidalClosed.pre v).app W` has domain `(ihom Q).obj W` and codomain
   `(ihom P).obj W`. I read Monoidal/Closed/Basic.lean, especially `pre` and
   `curry_pre_app`, and Closed/FunctorToTypes.lean. The internal hom is the
   presheaf exponential for the degreewise cartesian product, so its n-simplices
   are maps `Q × Δ[n] → W`, and this arrow restricts them along v in that factor.
   Verdict: the dependency's Fun(Q,W) -> Fun(P,W), with correct variance.
8. Vertices modulo the equivalence relation generated by edge endpoints:
   `SSet.mapπ₀` on that arrow. I read PiZero.lean: `π₀Rel` is existence of an
   edge, `π₀` is its `Quot`, `π₀.mk_eq_mk_iff` identifies equality with
   `Relation.EqvGen`, and `mapπ₀_mk` computes the induced map on vertices.
   Verdict: exactly the node's edge-generated components; no Kan assumption on
   the mapping objects is needed to define them.
9. Bijectivity of that map: `Function.Bijective` applies to the entire induced
   quotient map inside the universal Kan-target quantifier.
   Verdict: exact, with no choice of inverse or stronger mapping-space conclusion.

Edge cases: both P and Q empty are allowed. If P is empty and Q is nonempty,
testing against empty Kan W gives a map from an empty component set to a singleton,
which fails bijectivity as it should. A map to empty Q forces empty P. Empty W is
not excluded by KanComplex's positive-dimensional horn convention. A one-point
target gives singleton mapping-component sets without imposing inhabitedness on
P or Q. Positive degrees r >= 1 are all included; r = 0 is handled by path
components, not incorrectly by a group condition. There is no index-set,
scheme, characteristic, ring, or zero-object parameter to restrict. The single
arbitrary universe is intentional in the node: both realization and singular
test objects remain in it, as the signatures of `SSet.toTop.{u}` and
`TopCat.toSSet.{u}` confirm.

Independent searches used different wording from the first worker. LeanFinder
for “Geometric realization of a simplicial map is a weak homotopy equivalence
precisely when the maps on connected components of internal homs into Kan
complexes are bijective” returned abstract model-category homotopy-class results.
LeanSearch for “Precomposition into all Kan simplicial sets detects weak homotopy
equivalences after geometric realization” returned the abstract forward theorem,
`SSet.toTop`, and unrelated Dold--Kan material. Loogle for `SSet.mapπ₀` returned
the induced map and its elementary computation laws, not this biconditional.
I independently searched Mathlib AlgebraicTopology, upstream WeilConjectures, and
the project's lean/Sheaf with `realization_weak`, `weak.*realization`,
`realization.*weak`, `mapπ₀`, and `precomp_bijective`. The project's
`kan_mapping_homotopy_invariance` is a downstream forward consequence with a
weak-equivalence hypothesis, not this equivalence. I opened its full signature.
I also opened Mathlib's `RightHomotopyClass.precomp_bijective_of_weakEquivalence`:
it assumes an abstract weak equivalence and gives only one implication on abstract
right-homotopy classes. Neither candidate supplies this exact statement.
No duplicate declaration was found. Search service records are in searches.jsonl.

There are no new definition nodes or dependency modules in this delivery.
The sole statement dependency's recorded predicates and the standard Mathlib
constructions are usable without repair. I checked the available proof-dependency
signatures in RealizationCWSubcomplex.lean, RealizationFiniteLimits.lean and
HomotopyEquivalenceWeak.lean against their node records. Their imports are present;
CompactOpen supplies the recorded Mathlib currying match. The two proof-only
nodes without Lean records remain documented in the worker report, and are not
needed to type this statement. There is no statement_change or citer audit to
verify because the mathematical statement is unchanged.

No H3--H6 mathematical mismatch was found, and I left the Lean module unchanged.
Its only theorem has proof `by sorry`; there is no definition, hidden hypothesis,
file-local notation, private construction, or unbound variable. The module and
theorem docstrings name the sources and blueprint; the theorem's six proof steps
follow the node's six steps in order. All Lean lines fit 100 characters.
I changed only the node's lean.statement formatting to preserve the exact multiline
signature from the module, and appended this independent reading. The required
`scompile.py Q73 lem-cbc-realization-weak-equivalence` check compiled the module
cleanly in both sandbox and library forms, with no warnings or errors.
