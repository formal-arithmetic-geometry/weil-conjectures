## Worker report

The module `Sheaf.CategoryTheory.DirectedEnrichedAmalgamation` states
`CategoryTheory.DirectedEnrichedAmalgamation.directed_enriched_amalgamation`.
Its conclusion is `Nonempty (Statement M)` for the recorded Bergner model data `M`.
The structure packages the uniquely specified derived composition comparison and
all its mapping-space, naturality and enriched endpoint-action assertions.
Both theorem proofs are `sorry`; all definitions have explicit data.

The module's helper structures and constructions belong to this directed-gluing
notion. They introduce no independent replacement, coend, model structure or
homotopy-pushout notion. `outgoingAction_laws` names precisely the unit and
associativity proofs required for the outgoing restricted Hom module. Its data
are the actual Hom simplicial sets and curried precomposition, not chosen modules.

Hypotheses and conclusions, matched with the node:

- All data small in a fixed universe: `universe u`; `SCat.{u}`, `SSet.{u}`,
  `L : Type u`, `R : Type u`. The middle set `O` is the object type of `T`.
  No relative universe equality between unrelated mathematical data is imposed.
- Disjoint blocks and the two specified object sets: `Span.objectsA : L ⊕ T ≃ A`
  and `objectsB : T ⊕ R ≃ B`. Tagged sums implement disjoint union even when the
  input sets have overlapping presentations. No nonemptiness is imposed.
- Enriched functors from T inducing the middle inclusion on objects: `i`, `j`
  with `i_objects`, `j_objects`. Their mapping weak equivalences are `i_weak`
  and `j_weak`, using the dependency's realization-based weak equivalence.
- Forbidden mappings `A(o,l)` and `B(r,o)`: `reverseA`, `reverseB` assert
  `IsEmpty` in every degree. This is exactly the empty simplicial set condition.
- Z with its cocone maps: `Cocone.Z`, `a`, `b`, `condition`. The pushout hypothesis
  in `Statement.mapping_equivalences` is the existing
  `CofibrantSimplicialInversion.IsBergnerHomotopyPushout M i j a b`.
  Its definition quantifies a cofibrant replacement span, an ordinary colimit,
  objectwise weak equivalences to the original span, and the canonical weak
  equivalence from that colimit to the displayed cocone. Thus the cocone is
  retained, rather than merely an assertion about an unpointed apex.
- The statement allows Z to be presented on `L ⊕ O ⊕ R`; the formalization permits
  arbitrary presentations of Z and evaluates at the corresponding cocone objects.
  It does not demand that every DK-equivalent representative have literally that
  object type. This follows the node's proof step 6, which says explicitly
  "at the corresponding cocone objects".
- The old mapping spaces: the first two conjuncts of `mapping_equivalences`
  quantify every pair in A and in B and assert the weak equivalence of the
  actual maps `C.a.map` and `C.b.map`.
- The reverse new mapping space: the third conjunct asserts every degree of
  `Z(C.b(r), C.a(l))` is empty. Being weakly equivalent to the empty simplicial
  set is equivalent to being empty: a simplex has vertices, and a nonempty
  realization cannot be weakly equivalent to the empty space. Thus this does
  not add a fibrancy requirement or strengthen the claimed homotopy type.
- The chronological derived coend: `incoming S l` is the existing
  `coherentHomDiagram S.i l`, with objects `A(l,i(o))`. `outgoing S r` has
  objects `B(j(o),r)` and precomposition action. The source of `comparison` is
  the dependency's `DerivedSpaceModule.bar (incoming S l) (outgoing S r)`.
  Its words have the exact factors `A(l,o₀) × T(o₀,o₁) × ... × B(oₙ,r)`.
  The recorded `derived_space_module_coyoneda` statement identifies this
  diagonal bar with the derived enriched coend without a local Kan assumption.
  The fourth conjunct of `mapping_equivalences` says the comparison is weak.
- The comparison is specifically the derived composition pairing:
  `normalization` fixes `comparison.app n` on *every* bar word to
  `compositionWord`. This first applies the two cocone maps and the image of
  the middle composite, transports across the cocone equality, then composes.
  All faces/actions and degeneracies are already those of the dependency's bar.
  The formula determines the simplicial comparison uniquely.
- Naturality for arbitrary block-preserving span maps: `SpanMap` includes the
  three enriched functors, both middle triangles, arbitrary `left`/`right`
  functions and their endpoint equations. The middle object function is that
  of `t`. There is no injectivity or identity restriction. `mapWord` maps
  the chain and both endpoint factors by precisely these functors.
  `CoconeMap` retains a compatible map of the given apices. `targetMap` is its
  actual mapping-space map with the forced endpoint identifications.
  `Statement.naturality` gives the comparison square on every simplex.
  Applying this equation to homotopy-pushout cocones is the asserted naturality;
  the same canonical construction also makes sense for any cocone.
- Retained `A|L` opposite and `B|R` enriched variables: `endpointWord` acts
  on the first and last factors by arbitrary *n-simplices* of the original A
  and B mapping spaces. `endpoint_actions` says the comparison intertwines
  those actions with composition in Z in every degree. This is the enriched
  bimodule equation, including higher mapping simplices, not merely ordinary
  naturality on vertices or on the homotopy category.
- Empty blocks and empty mapping sets: there is no `Nonempty` binder anywhere.
  If O is empty, a `Word` would have a chain with at least one middle object,
  so each bar degree is empty. If L or R is empty the corresponding new-pair
  assertions and actions have no instances. An empty endpoint or internal
  factor removes that word. No `IsLocallyKan`, `KanComplex` or fibrancy
  hypothesis occurs.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.BergnerModelData`, including its full model axioms and
  weak-equivalence, fibration and cofibration characterizations. The theorem
  `CategoryTheory.coherent_nerve_comparison` supplies this data. The underlying
  `CoherentNerve.SCat`, `hom`, `underlying` come from its infrastructure import.
- `Sheaf.CategoryTheory.DerivedSpaceModuleCoyoneda`:
  `DerivedSpaceModule.Left`, `Right`, `Word`, `bar`, and the full
  `derived_space_module_coyoneda : Statement` signature/docstring. Read the
  actual operator, action, augmentation and retained-variable constructions.
  Incoming Homs reuse `CoherentNerve.coherentHomDiagram`, also read with its
  `coherentHomAction` and unit/composition laws.
- `Sheaf.CategoryTheory.CofibrantSimplicialInversion`:
  `CofibrantSimplicialInversion.IsBergnerHomotopyPushout` and its cofibrant
  predicate. This already-landed node is added to `stmt_deps` solely to cite
  the canonical predicate's owning node. No definition is copied or repaired.
  Read the node and its module. A read-only graph traversal of both dependency
  kinds found no path from that node back to the item (559 nodes visited).
- `SimplicialHammockDegree` and `simplicialHammockDegreeFunctor` from
  `Sheaf.CategoryTheory.SimplicialHammockPair` (available through the bar module)
  map the actual chain in every degree.
- All eight already-stated proof dependencies have imports, including the two
  statement dependencies. `lem-coef-simplicial-derived-pushout-mapping` and
  `lem-coef-triangular-cofibrant-resolution` have no recorded Lean module in
  the shared DAG at this writing, so no fictional import is added. Their
  complete roles remain in the theorem's seven-step proof docstring. Neither
  is needed to type the statement.

Sources checked: the node's complete statement and seven-step auxiliary proof;
the current blueprint file
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`.
As its provenance says, the current blueprint uses a coefficient-limit
adjunction argument; this item is an inherited auxiliary branch, not a quoted
assertion in that proof. Opened HTT at
`https://www.math.ias.edu/~lurie/papers/HTT.pdf`, checked Appendices A.3.2 and
A.3.3 (in particular the projective/injective structures and enriched
restriction/extension of scalars, A.3.3.2 and A.3.3.7--8). These provide the
background recorded in the node; no archival source for the auxiliary assertion
was invented.

Searches for an existing declaration:

- `msearch.py`, LeanFinder: "Mapping spaces in a directed homotopy pushout of
  simplicial categories are derived coends". Eight hits: Čech conerve maps and
  small-object attachments. Read the returned signatures; these do not state
  the enriched directed gluing result.
- `msearch.py`, Loogle: `"EnrichedFunctor", "pushout"`. No hits.
- `msearch.py`, Mathlib grep: `amalgama|derived.*coend|homotopy.*pushout`,
  CategoryTheory. Twenty-five displayed hits, all ordinary sheaf amalgamation;
  none gives the mapping-space computation. Read ordinary coends in
  `Mathlib/CategoryTheory/Limits/Shapes/End.lean` and simplicial Homs in
  `Mathlib/AlgebraicTopology/SimplicialCategory/Basic.lean`: these supply basic
  notions, not this derived theorem.
- `msearch.py`, LeanSearch: "The mapping spaces of directed gluing of simplicial
  categories are computed by a two sided enriched bar". Eight hits: enriched
  Homs, ordinary glue data, simplicial nerve. Read the returned types; no match.
- `rg` in the full upstream `WeilConjectures` tree for
  `Bergner|Directed.*[Aa]malg|directed.*[Aa]malg|derivedSpaceModule|DerivedSpaceModule`,
  and separately for the exact item id, returned no matching theorem.
- `rg` in `lean/Sheaf` found the bar dependency and the already-landed
  cofibrant-span homotopy-pushout definition, which are both reused. Searching
  `DirectedEnriched|directed_enriched|HomotopyPushout` found no directed-gluing
  statement. Searching proposed helper names in Mathlib's enrichment files,
  upstream and the shared statement library found no existing implementation.
  Mathlib's ordinary `eHomFunctor` is not an enriched functor into simplicial
  sets, so it does not replace `outgoing` with its enriched mapping action.

Edge-case and interface reading found no statement fault. No source correction,
new DAG node, or dependency repair is needed. The sole dependency-list addition
names the existing homotopy-pushout predicate; the original statement and proof
are unchanged.

Validation: compiled the delivered file with the prescribed `scompile.py NN
lem-coef-directed-enriched-amalgamation` wrapper. Both its isolated sandbox
and library checks passed cleanly (about 3 seconds each), with no diagnostics.
All variables and universes are explicit (`autoImplicit false`), and all Lean
lines have at most 100 characters. No global build or direct git command was run.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
