## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyFiniteTypeLimitClosedFp` states
`AlgebraicGeometry.exists_locallyFiniteType_limit_closed_finitePresentation`.
Its only proof is `sorry`; it introduces no definition. The node copy changes only `lean`.
The source was read in `literature/stacks-project/limits.tex`, Tag 09ZQ,
`lemma-finite-type-is-limit-finite-presentation` (lines 2271–2297).

Hypothesis and clause correspondence:

- Schemes and the specified morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The base is quasi-separated: `[QuasiSeparatedSpace S]`. No compactness of S is assumed.
- The morphism is locally of finite type: `[LocallyOfFiniteType f]`.
- X is quasi-compact and quasi-separated: `[CompactSpace X] [QuasiSeparatedSpace X]`.
- A nonempty directed set is `∃ (I : Type u) (_ : Preorder I),
  Nonempty I ∧ IsDirected I (· ≤ ·) ∧ ...`, the project's directed-set convention.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. For j ≥ i, the opposite of
  `homOfLE` gives the transition from the j-th model to the i-th model.
- The models are S-schemes via `p : D ⟶ (Functor.const Iᵒᵖ).obj S`.
  Naturality of p says that every transition is over S.
- Every model is of finite presentation over S: for every i,
  `LocallyOfFinitePresentation (p.app i) ∧ QuasiCompact (p.app i) ∧
  QuasiSeparated (p.app i)`, exactly the convention node's three conditions.
- Every model is qcqs: `∀ i, CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i)`.
- All transitions are closed immersions:
  `∀ (i j : Iᵒᵖ) (g : i ⟶ j), IsClosedImmersion (D.map g)`.
- The compatible maps from X form `π : (Functor.const Iᵒᵖ).obj X ⟶ D`.
  Naturality supplies compatibility with every transition; `∀ i, π.app i ≫ p.app i = f`
  supplies compatibility over the given S.
- X, with precisely those maps, is the limit in schemes:
  `Nonempty (IsLimit (Cone.mk X π))`. No arbitrary isomorphic cone vertex is substituted.
- Every map from X to a model is a closed immersion:
  `∀ i, IsClosedImmersion (π.app i)`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and its quasi-compactness dependency
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (the dependency's Mathlib match).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-scheme-conventions` has a convention-only record, deliberately no module
  or declaration. Its finite-presentation convention is rendered by the conjunction above.
  Scheme quasi-separatedness uses Mathlib `QuasiSeparatedSpace`, whose signature and
  docstring were read in `Mathlib.Topology.QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition` was read in full; it uses the same
  opposite-preorder diagram and `Cone`/`IsLimit` notion used here. This statement dependency
  is publicly imported. It does not itself assert finite presentation approximation.
- The already stated proof dependencies are imported through
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`. In particular, the
  signatures/docstrings of `Scheme.Hom.FinitePresentationApproximation`,
  `Scheme.Hom.exists_isClosedImmersion_locallyOfFinitePresentation`,
  `Scheme.Hom.nonempty_finitePresentationApproximation`, `Scheme.IdealSheafData.FGSub`,
  `fgSubDiagram` and `fgSubCone` were read. The existing approximation theorem assumes
  `[CompactSpace S]` and gives a general cofiltered category, so it is not this node's exact
  statement. It supplies the construction after the qcqs open-base reduction in the node's
  proof. No substitute approximation structure is defined here. The other proof dependencies
  (qcqs and proper/finite-presentation permanence) are Mathlib matches.

Edge cases checked: X may be empty, with a nonempty singleton system of empty models;
S may be empty (then X is empty). No point, nonemptiness, separatedness or Noetherian
assumption on schemes is imposed. S may be non-quasi-compact: the proof docstring includes
restriction to a finite union of affine opens containing f(X), and subsequent composition
with its finite-presentation inclusion. Singleton indices and identity transitions are allowed.
`I : Type u` matches `Scheme.{u}` and the upstream finite type ideal index, with arbitrary
explicit universe u. No independent smaller index universe or linear-order restriction is used.

Searches made (all before writing):

- `msearch.py ... leanfinder`: “locally finite type morphism quasi compact quasi separated
  scheme inverse limit finite presentation closed immersions”. Eight hits, including
  `LocallyOfFiniteType`, `LocallyOfFinitePresentation` and finite-type factorization through a
  given limit; none is the requested existence theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.LocallyOfFinitePresentation,
  CategoryTheory.Limits.IsLimit`. One hit,
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, a factorization through an
  already given limit, not the existence of the model system.
- `msearch.py ... grep`: `finitePresentationApproximation|finite.type.*limit|limit.*finite.presentation`
  in Mathlib/AlgebraicGeometry. One docstring hit in AffineTransitionLimit; no exact match.
- `msearch.py ... leansearch`: “A locally finite type quasi compact quasi separated scheme
  over a quasi separated scheme is an inverse limit of finite presentation schemes with
  closed immersion transition maps”. Service unavailable: Internal Server Error.
- `rg` with the approximation/finite-type-limit patterns in `WeilConjectures` and
  `lean/Sheaf` found the upstream approximation structure and theorem read above, plus
  unrelated ring-limit and integral-morphism approximation modules. None has this exact
  statement for merely quasi-separated S and a directed preorder index.
- The exact node-id search in `WeilConjectures` found no attachment. The new declaration
  name was searched in Mathlib, `WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` with no collision.

No statement correction, new node, dependency module or disputed statement is needed.
Server verification: the delivered module compiled cleanly with `scompile.py`, 1.4 seconds,
nice 19, two threads, 60 seconds per file. No local compilation was run.


## Second reading by NN

I independently read the node, its source in limits.tex (Tag 09ZQ,
lemma-finite-type-is-limit-finite-presentation, including the preceding closed-subscheme
limit lemma), and the delivered Lean side by side. The source lemma lists all three
hypotheses explicitly; no ambient field, Noetherian assumption, or compact base hypothesis
is in force. The following is my object/hypothesis/conclusion checklist, with verdicts.

1. Objects: schemes X and S and the specified morphism f are `{X S : Scheme.{u}}`
   and `(f : X ⟶ S)`. These use Mathlib's locally ringed spaces locally isomorphic to
   affine spectra and their morphisms. Verdict: exact.
2. Base hypothesis: S is quasi-separated, `[QuasiSeparatedSpace S]`. In Mathlib this
   says intersections of compact opens are compact, equivalent to scheme
   quasi-separatedness. No `[CompactSpace S]` occurs. Verdict: exact.
3. Morphism hypothesis: f is locally of finite type, `[LocallyOfFiniteType f]`.
   The dependency's affine-local ring finite-type predicate was read in
   Morphisms/FiniteType.lean. It does not require f to be of finite presentation.
   Verdict: exact, no extra hypothesis.
4. Domain hypotheses: X is quasi-compact and quasi-separated, `[CompactSpace X]`
   and `[QuasiSeparatedSpace X]`. CompactSpace is topological quasi-compactness and
   carries no Hausdorff condition. Verdict: exact.
5. Index: a nonempty directed set is the existential `(I : Type u) (_ : Preorder I)`
   followed by `Nonempty I ∧ IsDirected I (· ≤ ·)`. A preorder is the project convention
   for Stacks directed sets. Verdict: exact.
6. Inverse system of S-schemes: `D : Iᵒᵖ ⥤ Scheme.{u}` and
   `p : D ⟶ (Functor.const Iᵒᵖ).obj S`. Naturality of p states that all transitions
   commute with the structure maps to S. Morphisms in the opposite preorder have the
   j-to-i direction when i ≤ j. Verdict: exact.
7. Each structure map is of finite presentation: the three predicates
   `LocallyOfFinitePresentation (p.app i)`, `QuasiCompact (p.app i)`, and
   `QuasiSeparated (p.app i)` are conjoined for every i. I read their definitions
   in Morphisms/FinitePresentation.lean, QuasiCompact.lean and QuasiSeparated.lean;
   this is precisely the convention dependency's Stacks 01TP meaning. Verdict: exact.
8. Each model is qcqs: `∀ i, CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i)`.
   Verdict: both clauses present and no stronger condition.
9. Closed transitions: `∀ (i j : Iᵒᵖ) (g : i ⟶ j), IsClosedImmersion (D.map g)`.
   The dependency's IsClosedImmersion is a closed embedding with surjective stalk
   maps, not merely a topological embedding. Including identity transitions adds no
   mathematical requirement. Verdict: exact.
10. Compatible maps from the original X: `π : (Functor.const Iᵒᵖ).obj X ⟶ D`.
    Naturality is diagram compatibility, and `∀ i, π.app i ≫ p.app i = f` makes every
    projection a morphism over the specified S. Verdict: exact.
11. Limit in schemes with those projections: `Nonempty (IsLimit (Cone.mk X π))`.
    The vertex is exactly X and the cone uses the same π. I opened the dependency
    exists_limit_affine_transition in LimitAffineTransition.lean and checked that
    this is its category-of-schemes Cone/IsLimit notion. Verdict: exact.
12. Closed projections: `∀ i, IsClosedImmersion (π.app i)`. Verdict: every projection
    is covered, as explicitly stated by both the node and the parenthetical source clause.

Edge cases: the existential index is required to be nonempty, as the node demands,
but it may be a singleton; no nonemptiness is imposed on X or S. Empty X can use empty
models over S, and empty S forces X empty. Identity transitions are allowed. Neither
separatedness, integrality, a field, nor a characteristic is imposed, so zero rings and
all characteristics are included. No numerical n occurs. The explicit universe u is
arbitrary and shared by Scheme and the index; the upstream finite-type ideal index
FGSub is itself Type u. There is no independent small universe making a test family
vacuous, and no unbound variable or universe in the signature.

Independent H4 searches used words and patterns beyond the first reader's queries:

- LeanFinder via msearch.py: "quasi separated base scheme locally finite type qcqs
  closed immersion finite presentation approximation inverse system". Eight results
  concerned factorization through an already given limit or eventual properties of
  stages; none asserted this approximation existence statement.
- Loogle via msearch.py: `AlgebraicGeometry.LocallyOfFiniteType,
  AlgebraicGeometry.IsClosedImmersion`. Its sole result was
  instLocallyOfFiniteTypeOfIsClosedImmersion, not this statement.
- Direct rg across Mathlib/AlgebraicGeometry, WeilConjectures, and lean/Sheaf:
  `09ZQ|finite.type.is.limit|exists.*limit.*closed|finitePresentationApproximation|
  limit.*finite.presentation`. I read the resulting upstream
  Scheme.Hom.FinitePresentationApproximation structure and
  Scheme.Hom.nonempty_finitePresentationApproximation theorem in full, as well as
  exists_isClosedImmersion_locallyOfFinitePresentation and the FGSub construction.
  The theorem requires CompactSpace S and QuasiCompact f and packages an arbitrary
  cofiltered category; it is not the present theorem over merely quasi-separated S.
  Its actual construction uses the opposite of the directed FGSub poset, which
  supports the proof plan after reducing to a qcqs open base. The integral-morphism
  approximation results are special cases with different conclusions. No exact
  declaration was found. The proposed full declaration name also has no hit in
  Mathlib, upstream, lean/Sheaf, or dag/lean_names_upstream.json.

The statement dependencies' node records and actual declarations were opened:
Scheme/Hom, LocallyOfFiniteType/QuasiCompact, LocallyOfFinitePresentation,
IsClosedImmersion, and exists_limit_affine_transition. The convention node explicitly
introduces no new notion and has no module to import. The upstream approximation
module is a proof-only import, not a private replacement definition. There are no new
nodes or dependency modules in this delivery, and no statement_change to audit.

No mismatch was found; no Lean or node field was changed. The theorem's only proof is
sorry, there are no data definitions or local notation/instances, and both source and
blueprint tags are present. Its proof docstring follows all three node proof steps:
qcqs open-base reduction (also for empty X), finite-type subideal directed system with
closed models and limit, and composition with the finite-presentation open inclusion.
The recorded lean.statement was compared byte-for-byte with the declaration signature
and matches. Server-only scompile.py verification is recorded below.

Independent server compile: clean, 1.4 seconds; nice 19, two threads, 60 seconds per file.
