## Worker report

The module `Sheaf.CategoryTheory.CoverNerveComparison` defines the actual canonical
map `CategoryTheory.SiteCechComplex.functorComparison` and states
`CategoryTheory.SiteCechComplex.cover_nerve_comparison`. Only the theorem is postponed,
with `sorry`; the definition chooses the unique map furnished by the target tuple
universal property, applied to the mapped source projections. Its compatibility
argument is composed directly from `Functor.map_comp`, `S.comm`, and `congrArg`.
Thus the data do not come from a mere existence of an unspecified object or
isomorphism. No new node or dependency repair is needed: the helper constructs the
canonical map already introduced in the item's own statement.

Hypotheses and clauses, in the order of the node:

- Small sites C and D in the common universe: `{C D : Type u}`, `[Category.{u} C]`,
  `[Category.{u} D]`, `(J : Precoverage C)`, `(K : Precoverage D)`,
  `(hJ : J.IsSiteForCoverings)`, and `(hK : K.IsSiteForCoverings)`.
  This is the recorded presieve-site convention, including only the existence of
  covering pullbacks, rather than a global pullback instance. `T : Type u` puts
  covering indices in that same universe. No independent universe is implicitly bound.
- The functor u is `F : C ⥤ D`; the covered object, family and arrows are `U`,
  `f : T → C`, and `hom : ∀ t, f t ⟶ U`.
- The fixed source covering is `hcover : Presieve.ofArrows f hom ∈ J U`.
- Its image is a covering exactly by `himage`, the membership of the image family
  in `K (F.obj U)`. There is no quantification over other coverings.
- Preservation of the binary base change of each original member along every
  `a : V ⟶ U` is `hbase : ∀ (t : T) (V : C) (a : V ⟶ U),
  PreservesLimit (cospan a (hom t)) F`. This is equivalent to the node's
  invertibility of the canonical binary comparison, with no additional preservation:
  `hJ` and `hcover` give the source binary pullback, and `hK` and `himage` give
  the target binary pullback along `F.map a`. In the imported Mathlib module,
  `PreservesPullback.of_iso_comparison` gives one implication and the
  `IsIso (pullbackComparison F a (hom t))` instance gives the other.
  This predicate says nothing about any other cospan.
- The arbitrary chosen tuple products and all index maps are precisely the
  dependency's `S : SiteCechComplex f hom` and
  `P : SiteCechComplex (fun t ↦ F.obj (f t)) (fun t ↦ F.map (hom t))`.
  Neither choice is constrained to be recursive or to agree with the other.
- The tuple indexed by `t : Fin (n + 1) → T` is `S.W n t` in the source and
  `P.W n t` in the target. Their projections are `S.pr n t k` and `P.pr n t k`.
  The map c_t is `functorComparison F S P n t`, built using `P.universal`.
  The first conjunct states its defining projection equations for every k;
  uniqueness follows from that same universal property, so this is the canonical map.
- The second conjunct says `IsIso (functorComparison F S P n t)` for every
  `n : ℕ` and every tuple, including n = 0.
- The third conjunct quantifies over every `n m`, tuple, and arbitrary function
  `α : Fin (m + 1) → Fin (n + 1)`. `t ∘ α` is the tuple tα and the chosen
  index maps are `S.indexMap t α` and `P.indexMap t α`. Its equality
  `F.map (S.indexMap t α) ≫ functorComparison F S P m (t ∘ α) =
  functorComparison F S P n t ≫ P.indexMap t α` is exactly the node's
  displayed naturality equation, in Lean's left-to-right composition convention.
- There are no continuity, cocontinuity, final-object, finite-limit, or arbitrary
  pullback hypotheses. The source's global continuity is used by the DAG only
  through its two fixed-cover conditions, as the node explicitly specifies.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: its full signature and docstring
  were read. This is used for both sites; its third clause gives exactly the
  covering base changes needed to interpret `hbase`.
- `WeilConjectures.CategoryTheory.SiteCechComplex`,
  `CategoryTheory.SiteCechComplex`: read the full structure, its docstring and
  the surrounding existence and uniqueness results. The module uses the actual
  `W`, `pr`, `comm`, `universal`, and `indexMap` fields. In particular it imports
  the upstream module directly, avoiding the retired duplicate Sheaf version.
- `def-weil-size-convention` is recorded as a metatheoretic convention, with no
  declaring module. Its instruction is implemented by the explicit single universe u.
- Mathlib's `PreservesLimit` and `cospan` are used through
  `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks`. The binary comparison,
  its projection equations, and both directions of the preservation equivalence
  were inspected in that module and `Limits/Shapes/Pullback/HasPullback.lean`.

Sources read: local Stacks `sites-cohomology.tex`, the proof of
`lemma-pullback-injective-pre-limp` (0D6X), including the displayed iterated
fibre-product identity; local `sites.tex`, `definition-continuous` (00WV),
conditions (1) and (2). The latest blueprint's `sk-i-curve-zero/_section.md` and
`lem-trf-local-term-locality` statement and proof were read to verify the ancestor
route. The module docstrings explain all six proof steps of the accepted DAG,
including arbitrary tuple choices and all index maps. The node statement and
its dependencies and proof have not been changed. No statement fault or dispute arose.

Edge cases checked before writing: an empty T has no functions `Fin (n + 1) → T`,
so all conclusions are vacuous; no nullary product occurs. For n = 0 the dependency
prescribes the original object with its identity projection, and the comparison
has those canonical singleton data (up to the dependency's equality transports).
Repetitions and arbitrary permutations are permitted because α is any function,
not just an order embedding. Face maps and degeneracies are included. For F the
identity functor, independent choices are compared by their universal properties;
the definition never requires the chosen objects to be definitionally equal.
The induction proof uses base changes only of an original member of the fixed
cover, along a prefix structure map, and never a final object.

Searches for reuse (msearch.py, group Q65, this item):

- LeanFinder: "A functor preserving base changes of members of a fixed covering
  family preserves all nonempty tuple fibre products and all index maps".
  Eight hits: base-change stability, `CoverPreserving`, `CompatiblePreserving`,
  and globally preserving pullbacks. None states this fixed-family tuple result.
- Loogle: "pullbackComparison,PreservesPairwisePullbacks". Zero hits, with
  "unknown identifier 'pullbackComparison'". The declaration was located by
  source grep and inspected directly rather than treating this as a no-match proof.
- Mathlib grep: "pullbackComparison|PreservesPairwisePullbacks|[Cc]ech.*[Cc]omparison"
  in CategoryTheory. Twenty-three hits. Binary comparison and pairwise preservation
  are existing inputs, not a theorem about all nonempty tuples under this local
  assumption. The relevant source signatures were read.
- LeanSearch: "Preservation of pullbacks along one family implies preservation
  of nonempty finite iterated fibre products". Eight hits, including
  `hasPullback_of_preservesPullback`, `isLimitOfHasPullbackOfPreservesLimit`,
  pullback associativity, and finite limits from terminal objects and all pullbacks.
  None has the requested hypotheses and all-index-map conclusion.
- Local `rg` over `lean/WeilConjectures` and `lean/Sheaf` for covering nerve/tuple
  comparisons and `pullbackComparison`: related Cech-complex transport and
  refinement modules exist, but no fixed-cover preservation induction or canonical
  tuple comparison with this statement. A literal search for this node id in
  `WeilConjectures` had no hit. Searches for the proposed names found no
  `CategoryTheory.SiteCechComplex.functorComparison` or `cover_nerve_comparison`.

Validation: scompile.py compiled the delivered module cleanly both as the sandbox
module and at its intended library path (2.2 s and 1.2 s). No compiler error or
unexpected warning. All Lean lines have length at most 100. The required deliver2.py --no-push dry run passed server preflight and
per-file compilation: OK (dry run), commit 77492927114. The final delivery
runs those checks again before pushing.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
