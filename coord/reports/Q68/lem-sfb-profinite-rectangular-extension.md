## Worker report

The module `Sheaf.Topology.ProfiniteRectangularExtension` states
`Topology.profinite_rectangular_extension`, with its proof left as `sorry`.
There are no new definitions, dependency modules, or statement corrections.

Source read: `literature/stacks-project/topology.tex`, Tags 08ZY
(`lemma-profinite`, including the nonempty-block convention in its proof) and
08ZZ (`lemma-profinite-refine-open-covering`). As the node says, the extension
assertion is an agent-formulated auxiliary consequence, rather than the literal
statement of either tag. All seven accepted proof steps appear in the theorem's
docstring, including the empty cases, common Boolean-atom partition, and zero
assignment off K.

Hypotheses and clauses, matched to Lean:

- Size convention: explicit `universe u v`, `T : Type u`, and `M : Type v`.
  The dependency `def-weil-size-convention` has a convention record, with no
  module or declaration to import. This statement uses no sites, skeletons,
  derived categories, or colimits; the universe levels are unrestricted.
- Compact Hausdorff totally disconnected T: `[TopologicalSpace T]`,
  `[CompactSpace T]`, `[T2Space T]`, `[TotallyDisconnectedSpace T]`.
- Positive integer k: `(k : ℕ) (hk : 1 ≤ k)`. Positive integers are equivalently
  positive natural numbers. The power is `Fin k → T`, with Mathlib's product
  topology, and no extra choice of topology.
- Closed K with the subspace topology: `(K : Set (Fin k → T))`
  and `(hK : IsClosed K)`; `K` in `C(K, M)` is the canonical subtype.
- Finite abelian group with the discrete topology: `(M : Type v)` with
  `[AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]`.
  No homomorphism property is required of c or h.
- Continuous c: `(c : C(K, M))` uses Mathlib's bundled continuous maps.
- One finite clopen partition: `α : DiscreteQuotient T`. Its blocks are precisely
  the fibers `α.proj ⁻¹' {a}` for `a : α`. These fibers are nonempty by
  `DiscreteQuotient.proj_surjective`, clopen by `isClopen_preimage`, pairwise
  disjoint because distinct fibers of a function are disjoint, and cover T
  because every point has a projection. The block type is finite by Mathlib's
  `[CompactSpace T] : Finite α` instance. Conversely, any finite partition in
  the node defines this open-class setoid by belonging to the same block.
  Thus this is the same notion, not a finiteness assumption on T or a
  partition that permits empty blocks.
- Continuous extension: the witness `(h : C((Fin k → T), M))` is continuous,
  and `∀ x : K, h x.val = c x` is exactly restriction to K.
- Constant on every product cell: `∀ x y : Fin k → T,
  (∀ i : Fin k, α.proj (x i) = α.proj (y i)) → h x = h y`.
  Two tuples satisfy the antecedent exactly when they belong to the same
  product of blocks of α. There is a single α for all coordinates.
- Zero on every cell disjoint from K: `a : Fin k → α` indexes arbitrary
  choices of blocks. The set `{x : Fin k → T | ∀ i, α.proj (x i) = a i}`
  is their product cell. Its `Disjoint ... K` hypothesis implies
  `∀ x, (∀ i, α.proj (x i) = a i) → h x = 0`, exactly the required zero clause.
- Empty T or K and the zero group: there are no `Nonempty T`, `Nonempty K`,
  or nontriviality binders.

Dependency and interface sources read:

- `def-weil-size-convention`: `lean.convention = true`; implemented here by
  explicit universe binders, as its note directs.
- Proof dependency `lem-weil-pbc-profinite-clopen-basis`:
  `Mathlib.Topology.Separation.Profinite`, `isTopologicalBasis_isClopen`
  (line 66), and its pointwise equivalent `compact_exists_isClopen_in_isOpen`
  (line 76). Read the full statements and the section hypotheses.
- Proof dependency `lem-weil-pbc-tychonoff-product-quasi-compact`:
  `Mathlib.Topology.Compactness.Compact`, `Pi.compactSpace` (line 1183).
  Read its full instance signature, which imposes no Hausdorff assumption.
  Both proof modules have plain, non-public imports.
- Statement interfaces: `Mathlib.Topology.DiscreteQuotient`, `DiscreteQuotient`
  (line 81), `proj` (109), `proj_surjective` (115), `isClopen_preimage` (132),
  and its finite-quotient instance (355); `ContinuousMap` from the public
  import closure; `AddCommGroup` from `Mathlib.Algebra.Group.Defs`.
  The module reuses these notions directly.

Edge cases checked before writing:

1. T empty and k positive: the power is empty. A quotient of the empty set has
   no blocks; no empty block is inserted. The unique h satisfies every clause.
2. K empty and T nonempty: the one-block quotient and h = 0 satisfy the
   extension, cell constancy, and zero requirement. All cells disjoint from K
   really are forced to zero, not only cells missing a chosen finite cover.
3. M the zero group: it remains an allowed finite additive commutative group;
   both c and h have their unique possible value.
4. k = 1: the cells are the blocks themselves, giving the usual closed-subspace
   extension. k = 0 is excluded exactly as in the node.
5. K the whole power: every product cell is nonempty, so no cell is disjoint
   from K. The extension is c and the conclusion is common-coordinate
   factorization of c. There is no requirement that c be an additive map.
6. Arbitrarily large universes for T and M remain available independently;
   finite M uses `Finite`, not a chosen enumeration or a fixed finite type.

Searches performed for the full statement and interfaces:

- `msearch.py leanfinder`: "A continuous finite discrete valued map on a closed
  subset of a finite power of a compact Hausdorff totally disconnected space
  extends and is constant on rectangles of one finite clopen partition".
  Eight hits, led by `Profinite.NobelingProof.fin_comap_jointlySurjective`,
  Nobeling's Boolean-coordinate functions, and finite approximation results.
  None states the present extension with a common coordinate partition and
  prescribed zero values. The finite approximation signature was read in
  `Mathlib/Topology/Separation/DisjointCover.lean`: its domain is the whole
  space, and it does not supply this rectangular closed-subspace extension.
- `msearch.py loogle`: `"LocallyConstant", "extend"`: zero hits.
- `msearch.py grep`: `ClopenPartition|clopen_partition|rectangular`, subdirectory
  `Topology`: three hits, including `exists_clopen_partition_of_clopen_cover`
  and its LightProfinite use; neither is this full theorem.
- `msearch.py leansearch`: "A map from a closed subset of a finite power of a
  profinite space to a finite discrete group extends constantly on rectangles
  of a common finite clopen partition": eight hits; Boolean-coordinate
  Nobeling factorization, finite fibers, and profinite group limits, with no
  exact match.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `ClopenPartition|clopenPartition|clopen_partition|rectangular.*[Ee]xtension|RectangularExtension`:
  related partition-reconstruction, invariant partition, and w-local results;
  no statement of this item. The invariant finite partition signature and
  reconstruction module were read. The latter already uses `DiscreteQuotient`
  for exactly the same finite clopen partition convention.
- `rg` for the item id in `lean/WeilConjectures`: no hits.
- `rg` for `profinite_rectangular_extension|exists_profinite_rectangular_extension`
  in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no name collision.
- DAG search for `DiscreteQuotient|finite clopen partition|finite.*clopen.*partition`
  located existing uses of this Mathlib interface. No missing definition is
  introduced by this statement.

No statement dispute or node fault was found. The old CompactObject example
module is now withdrawn; the live module-mode convention was followed using
`module`, public statement imports, and `@[expose] public section`.

## Second reading by Q68

Self-check only: the dispatcher explicitly forbids starting other agents, and
assigns the independent delivery review to the maintainer. No independent
second worker is claimed here. Rereading the node and module confirms that
quotient blocks are nonempty, finite, and clopen, that the single α is shared
by every coordinate, and that the zero clause tests disjointness from K itself.
The restriction equality uses all points of K. Both source and coefficient
spaces have explicit universe parameters. No correction was needed.
