## Worker report

Stage 2, group Q54, item `lem-sfb-boolean-coatom-excision-derived`.
The delivery adds `Sheaf.AlgebraicTopology.BooleanCoatomExcisionDerived` and changes
only the item's `lean` field. The accepted Q105 stage-1 split, statement, statement
dependencies and proof are preserved. The current node has no Lean record; the
stage-handoff paragraph in `coord/brief-stage2.md` explicitly authorizes this
stage-2 work despite the inherited stage-1 unchanged-item BLOCKED ending.
There is no released repair note for this item in the read repository.

The main declaration is
`AlgebraicTopology.AugmentedPosetChains.BooleanCoatom.excision`. All 24 declarations
are recorded in `lean.declarations`. Definitions have real data. The named
theorems `signedDeletion_comm`, `inclusion_deletionMap`, `thetaMap_isIso`,
`reversalSuspension_comm`, and `excision` have postponed proofs (five theorems in all); each has the blueprint tag, source, and a complete natural-language proof.
No arbitrary comparison map, auxiliary mathematical assumption, or existence
choice replaces the prescribed signed construction. The inverse in `theta` is
Mathlib's uniquely determined inverse of the specified `thetaMap`.

Hypotheses and objects, clause by clause:

- A finite set E is represented by an arbitrary-universe type `E : Type u` with
  `[Fintype E]`. Its points are precisely the elements of E; `a : E` renders
  membership. `[DecidableEq E]` supplies finite-set operations and excludes no
  finite set in classical mathematics. The exact size hypothesis is
  `hcard : 2 ≤ Fintype.card E`.
- `coatom a := Finset.univ.erase a` is v. `Proper F` is the subtype of nonempty
  `S : Finset E` with `S ⊂ F`, with the induced inclusion order. Since E is
  finite, these are exactly all subsets specified by P_F, including P_v.
  `booleanComplex F := complex ℚ (Proper F)` uses the dependency's augmented
  strict chains and its integer grading without rebuilding them.
- `Deleted a` removes exactly v from `Proper Finset.univ`, with inherited order.
  The first conjunct of `excision` gives `e : Deleted a` with underlying set
  `{a}` and `f : Deleted a →o Deleted a` with underlying action
  `insert a S.val.val`. The bundled order hom gives monotonicity; the inequalities
  `S ≤ f S ∧ e ≤ f S` give both pointwise comparisons. This formula determines
  the union map on every element; its existential binder is not an arbitrary-map
  hypothesis.
- `∀ n : ℤ, IsZero ((complex ℚ (Deleted a)).homology n)` gives acyclicity in
  every integer degree using the recorded Mathlib homology object, including
  augmentation degree -1.
- `inclusionOrder` is the subtype inclusion, and `inclusion` is the recorded
  entrywise monotone chain map `map ℚ (inclusionOrder a)`. Thus it is literally
  the chain-basis inclusion. The third conjunct asserts injectivity of every
  component. The fourth states that its degree -1 component fixes the empty
  generator; since both degree -1 modules are free on this generator, that is
  exactly the identity on their canonical copies of ℚ.
- `quotientComplex a := cokernel (inclusion a)` and
  `projection a := cokernel.π (inclusion a)` are the canonical quotient complex
  V and projection p. Mathlib's `HomologicalComplex.HomologicalComplexLimits`
  construction computes colimits degreewise; `eval` preserves them. Thus this
  cokernel is the degreewise quotient, rather than an unrelated complex with
  an assumed map. In modules, `ModuleCat.cokernelIsoRangeQuotient` identifies
  each component with the ordinary quotient by the range; its projection
  compatibility is `cokernel_π_cokernelIsoRangeQuotient_hom`. These existing
  constructions provide the quotient without any new proof axiom or choice
  from an undetermined existence theorem.
- `suspension K` has `X n := K.X (n - 1)` and
  `d i j := -K.d (i - 1) (j - 1)`, exactly the stated suspension convention.
  Its structural shape and square-zero fields merely reuse K's laws.
- `signedDeletion a n` is the linear extension on each strict-chain basis
  generator c. If its last underlying vertex is v it returns
  `(-1 : ℚ) ^ n.toNat • bracket ℚ (n - 1)
  (smallerVertices a c.val.dropLast)`; otherwise it returns zero. For n≥0,
  `n.toNat` is n. Maximality of v says precisely that the preceding vertices
  of a surviving chain belong to `Proper (coatom a)`, so `smallerVertices`
  retains every one of them. Its filter has no effect on a surviving prefix.
  For c=[v] the prefix is empty and the sign is 1. On the empty list and in
  lower degrees the map is zero.
- `deletionMap` packages that actual linear extension as a chain map, using
  the named proof obligation `signedDeletion_comm`.
  `thetaMap := cokernel.desc ... (deletionMap ...) ...` descends it through p,
  using the named annihilation theorem `inclusion_deletionMap`.
  `thetaMap_isIso` states invertibility; `theta` packages this same map and
  its unique inverse as a chain isomorphism. Its docstring supplies the inverse
  formula: append v and multiply by the same (-1)^n.
- The fifth conjunct asserts `IsZero` of both V_n and (ΣB_v)_n for every n<0.
  This makes theta in those degrees the unique map between zero objects.
  The sixth conjunct identifies theta on the image of every ambient strict
  generator under p with `signedDeletion`. This includes every surviving
  generator, [v], all killed generators, and the empty generator; it does not
  only assert a homology or abstract object isomorphism.
- `reversalEmbedding` is the complex-shape embedding q↦-q, and `reversal` is
  its Mathlib restriction functor. Consequently check K has term K_(-q) and
  the unchanged differential, and morphisms are reversed in exactly the same
  indices. `reversalSuspensionIso` has identity components after the index
  equality -q-1=-(q+1). Both differentials have the minus sign; it identifies
  check(ΣB_v) with (check B_v)[1].
- `[HasDerivedCategory.{w} (ModuleCat.{u} ℚ)]` chooses the localization and
  morphism universe exactly as the recorded derived-category dependency does;
  w is independent of u. `derivedComparison` is Q applied to the reversal of
  `projection a ≫ (theta a hcard).hom`, followed by the canonical reversed
  suspension/shift identification and Q's `commShiftIso 1`. Its codomain is
  literally `Q.obj (reversal.obj (booleanComplex (coatom a)))⟦1⟧`.
  The last conjunct `IsIso (derivedComparison a hcard)` is therefore the
  specified derived isomorphism, with its requested chain representative.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.AugmentedPosetChains`:
  `AlgebraicTopology.AugmentedPosetChains.Simplex`, `chains`, `bracket`, `boundary`,
  `boundary_laws`, `complex`; I read the complete module and docstrings.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology` is `(K.sc i).homology`; the cycle and homology
  signatures were read. `ShortComplex.moduleCatHomologyIso` in
  `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` identifies this with
  kernel modulo image, as required by the chain-homology dependency.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, Q's localization/inversion instances,
  and `Q.CommShift ℤ`. I read its universe convention and these definitions
  and instances. `CochainComplex.shiftFunctor` in
  `Mathlib.Algebra.Homology.HomotopyCategory.Shift` has the exact shift sign.
- Proof dependency `Sheaf.AlgebraicTopology.AugmentedPosetChainPrism` supplies
  `mapComponent`, `map_comm`, `map`, `map_id`, `map_comp`, `prismComponent`,
  `prism_identity`. The complete module was read. It is a public import because
  the statement's actual chain-basis inclusion uses its `map` construction.
- Proof dependency `lem-weil-pbc-complex-ses-homology-long-exact` is Mathlib;
  it needs no repaired Lean record. I read the full signatures/docstrings of
  `CategoryTheory.ShortComplex.ShortExact.δ`, `homology_exact₁`,
  `homology_exact₂`, `homology_exact₃` in
  `Mathlib.Algebra.Homology.HomologySequence`. This module is a proof-only import.

Edge cases checked before and while writing:

For |E|=2, D is the singleton {a}, with augmented complex ℚ→ℚ by identity;
v is a singleton, P_v is empty, B_v is ℚ in degree -1 only, and V is ℚ in
degree 0 only. The formula sends [v] to the empty generator with sign +1.
For n=1, the quotient boundary and the suspension boundary agree because
(-1)^0=-(-1)^1, including the smaller complex's augmentation. Degree -1
inclusion is identity, so V_(-1)=0; lower degrees vanish. For |E|≥3 the last
vertex v is still maximal and every preceding vertex is a nonempty proper
subset of v. Empty P_v is allowed and no Nonempty assumption is imposed on it.
The source hypothesis |E|≥2 is retained; no assertion is made for |E|=0,1.
Universes u and w are explicit and independent. No file-local notation,
local instance, private declaration, auto-bound variable, or `let` appears in
a statement.

Searches actually run via the prescribed `msearch.py Q54 <item>` wrapper
(the unmodified results are retained in `searches.jsonl`):

- LeanFinder: "Deleting a coatom from the proper Boolean subset poset gives an
  acyclic augmented chain complex and a signed quotient suspension isomorphism".
  Eight hits: Dold--Kan summands, alternating-face augmentation, augment/truncate,
  split simplicial complexes and representation resolutions. None states the
  coatom deletion, its signed quotient map and the specified derived arrow.
- Loogle: `"HomologicalComplex", "Finset"`. Two Euler-characteristic formulas,
  neither a chain-basis or derived-map identification.
- Grep in `Algebra/Homology`:
  `coatom.*(chain|complex)|Boolean.*(chain|homolog)|reindex`. Zero hits.
- LeanSearch: "The quotient of augmented strict chains on proper subsets of a
  finite set by chains avoiding one coatom is the signed suspension of the
  proper subset chain complex of that coatom". Eight hits on augmentation,
  homotopy-category localization and acyclicity; none is the item.
- Direct `rg` in Mathlib's AlgebraicTopology, Algebra/Homology and Order directories
  for Boolean/coatom-chain names found no exact declaration (an unrelated Zorn
  lemma uses the word coatom). `rg` in `lean/WeilConjectures` and `lean/Sheaf`
  for coatom/Boolean quotient, proper-subset and the exact item tag found only
  the related `ProductChainProperIntervalHomology` proof text. I read that
  entire module: its theorem gives homology dimensions of product intervals,
  not this signed quotient representative. The existing augmented chain and
  prism modules are reused, not duplicated.

Source audit: I opened the current `literature/blueprint/latest/` direct-images
proof, including paragraph (3). It concerns proper/open direct images and does
not contain the combinatorial assertion. The Lean docstrings and this report
honestly retain the node's agent-written source status; an exact combinatorial
literature reference remains WANTED as in the accepted split. No mathematical
counterexample, ill-typed node clause, or statement correction was found.
No STATEMENT-DISPUTED flag is introduced. No new nodes or dependency repairs
are needed: all helpers belong to this node's explicit quotient/comparison.

Validation: the final module compiled through `scompile.py` in both sandbox and
library module contexts, with no errors or warnings (2.9 s and 3.9 s reported).
Earlier compiler diagnostics were repaired: the reversal embedding is reducible
so its existing Mathlib `IsRelIff` instance is found, its component indices are
explicit, and the long line was removed. No global build or direct live edit
was run. The prescribed delivery dry run follows.

## Second reading by Q54

This is a fresh clause-by-clause rereading by the same dispatched worker;
no separate agent was started and no independent-worker review is claimed.
The maintainer's independent delivery review is still required by the dispatch.
I reopened the accepted node, its three statement-dependency records and the
final Lean module, and checked every binder and conjunct against the mapping
above. I specifically checked that P_v uses subsets of v, not all subsets of E;
that D deletes v, not {a}; that the degree -1 generator is included; that theta
uses (-1)^n rather than a sign-free truncation; that negative quotient degrees
vanish; and that the derived codomain is a shift by +1. The comparison's map
is fixed by its concrete basis formula and cokernel descent. The quotient uses
existing degreewise cokernels rather than a selected arbitrary complex. All
six node proof steps appear in the main docstring and helper docstrings.
No mismatch remained after the compile-driven reversal/index repairs.
The node diff contains only `lean`, with the complete main signature verbatim.
