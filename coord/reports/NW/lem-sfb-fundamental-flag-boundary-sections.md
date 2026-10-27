## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FundamentalFlagBoundarySections`
states `AlgebraicGeometry.exists_fundamental_flag_boundary_sections`, with the
single postponed proof `sorry`. The item statement and its dependencies are
unchanged. No new definition, dependency repair, or statement correction is needed.

Read the item's complete statement and four proof steps, all seven statement
dependencies and their records, and the declarations/docstrings in
`ReductiveBorelPairStructure`, `SimplyConnectedCharacterLattice`,
`BruhatLongestCellCharts`, `HomogeneousLineBundleSections`, and
`AssociatedCharacterLineBundle`. Also read the actual `GrpObj`, `Field`,
`IsAlgClosed`, semisimplicity, Borel, maximal-torus, normalizer, residue-fibre,
and irreducible-component definitions, and the Cartier dual-ideal declaration.
Source checked directly: Milne, Remark 22.49, printed p.480 (PDF p.492), including
the warning about the opposite positive-root convention. The source's divisor
formula at negative fundamental characters, reindexed by -w₀, gives the individual
boundary supports. The current blueprint's latest directory contains no separate
statement for this auxiliary node.

Hypothesis and object correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Semisimple group S: `G : Grp (Over (Spec (.of F)))` and `hG :
  IsSemisimpleGroupScheme G.X`. The recorded predicate spells out smooth,
  connected, affine, finite type, and absence of a nontrivial smooth connected
  solvable normal closed subgroup, using the scheme-theoretic derived series.
- Simply connected: `hsc` is exactly the recorded character-lattice theorem's
  quantification over semisimple source group schemes and homomorphisms with
  surjective underlying map, finite scheme-theoretic kernel, and commutation
  of that kernel with every point after every scalar extension. It concludes
  `IsIso f`. No restriction to reduced kernels or characteristic is imposed.
- Split maximal torus T and Borel B containing T: `T`, `B`, `iT`, `iB`, `j`,
  `hT`, `hsplit`, `hB`, `hj`. These use the existing maximal-torus/Borel predicates;
  `hj` says the inclusion factors through B.
- Character lattice, roots, positive system, coroot pairing and simple roots:
  the two commutativity witnesses, `aG`, `aB`, `haG`, `haB`, `Φ`, `P`, `b`,
  `hroot`, `hpair`, `hweights`, `hpositive` reproduce the actual Hom-group
  interface of `simplyConnected_character_lattice`. The conjugation actions are
  pinned by `haG` and `haB`; `hpair` pins the integer pairing to composition with
  the power map, and `hweights`/`hpositive` identify the root/base data with the
  Lie character weights of G/B. The simple-root index is `b.support`, so no
  assumption of positive rank or an artificial enumeration is introduced.
- Fundamental characters: `ω` consists of actual torus characters, written
  additively, and `hω` is the Kronecker coroot pairing. A choice of integral
  basis is not an extra hypothesis: the node only fixes these characters by
  their pairings; their existence is the recorded character-lattice theorem.
- U and p: `U`, `iU`, `p`, `hU`, `hp`, `hkernel`, `hsemidirect` are precisely
  the Borel-structure output: largest smooth connected normal unipotent closed
  subgroup, projection restricting to the identity on T, kernel U, and
  multiplication U×T→B an isomorphism. These fix p canonically for the fixed T.
- Q=S/B: `Q`, `π`, `hπflat`, `hπsurj`, `hπinv`, `hπtorsor` are the same right
  B-torsor quotient interface used by the Bruhat theorem. Properness/finite type
  are consequences of this quotient, and are not added as hypotheses.
- Representative n₀ of the longest Weyl element: `n₀ : RankOneRoots.normalizer
  iT`; `nT` and `hnT` pin its torus automorphism to actual conjugation on every
  test scheme. `hlongest` says its inverse sends the positive root characters
  exactly to the negatives, as in the recorded Bruhat statement. It therefore
  specifies the longest coset without introducing an unpinned Weyl action.
- Open cell: `C`, `c`, `eC`, `hc`, `hcell` specify an open immersion into Q,
  identified with U by u↦un₀B. Its underlying subset is `Set.range c.left`.
  Density is a consequence of the Bruhat theorem, not an extra assumption.
- M_ω: `χ` and `hχ` fix the character as the inverse of p followed by ω_i;
  `M i : AssociatedCharacterLineBundle.Presentation ... (χ i)` uses the actual
  quotient with action (g,z)b=(gb,χ_i(b)⁻¹z)=(gb,ω_i(p(b))z). Its `.L` is the
  sheaf of sections. The theorem works for every presentation of this specified
  bundle. Invertibility, coherence, and existence are already given by
  `exists_homogeneousLineBundle_sections`; they are not stronger assumptions.

Conclusion correspondence:

- Sections exist for every simple root: existential `s : ∀ i : b.support,
  Γ((M i).L, ⊤)`.
- They are nonzero: `∀ i, s i ≠ 0`.
- Their zero loci are exactly residue-field vanishing: the existential auxiliary
  family `Z` has `Z i = {x | Scheme.Modules.residueValue (s i) x
  (Set.mem_univ x) = 0}`. `residueValue` is germ tensored with 1 in κ(x)⊗M_x.
  This is only a name for the stated subsets, not a new definition or hypothesis.
- Each zero set is closed and irreducible: `∀ i, IsClosed (Z i) ∧
  IsIrreducible (Z i)`; the latter includes nonemptiness.
- Pairwise distinct: `Function.Injective Z`.
- Exactly all boundary components: `Set.range Z` equals the image under the
  boundary inclusion of `irreducibleComponents ((Set.range c.left)ᶜ : Set Q.left)`.
  The subtype has its induced topology. No component ordering is specified.
- The particular union assertion is explicit: `(Set.range c.left)ᶜ = ⋃ i, Z i`.
- Every characteristic is permitted: no characteristic hypothesis anywhere.
- Trivial group/rank zero: `b.support` is empty, both dependent section and zero
  set families are the empty functions; the displayed empty union says the
  boundary is empty. There is no `Nonempty b.support` premise.

Dependency declarations reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and bundled `Grp`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` for subgroup/kernel notions.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`, and their shared
  terminology imports (actual Borel, semisimplicity, torus and tangent weights).
- `Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice`:
  `AlgebraicGeometry.simplyConnected_character_lattice` and its actual
  additive Hom-group `RootDatum`/`Base` interface.
- `Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts`:
  `AlgebraicGeometry.bruhat_longest_cell_charts`, with `RankOneRoots.normalizer`
  and the right-torsor/open-cell presentation.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`:
  `AlgebraicGeometry.exists_homogeneousLineBundle_sections` and its public
  `AssociatedCharacterLineBundle.Presentation` interface. No associated bundle
  or section-module construction is duplicated.
- `WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber`:
  `AlgebraicGeometry.Scheme.Modules.residueValue` and `residueFiber`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, `IsIrreducible`.
- Proof-only import `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules`
  (O(D)=the dual ideal). The other two proof-only nodes,
  `lem-sfb-opposite-schubert-picard-basis` and
  `lem-sfb-homogeneous-line-schubert-curve-degree`, have no recorded Lean module
  on the read base; they are therefore not imported. They are not needed to
  type the statement. Their steps are reproduced in the theorem docstring.

Edge cases checked before writing: trivial group/rank zero; SL₂ with upper
triangular B (M_ω=O(1), a section vanishes at the single complementary point);
products (one component per fundamental character in each factor); arbitrary
positive characteristic including infinitesimal central kernels; distinct
components may intersect, and the conclusion does not require disjointness;
vanishing uses all scheme points and residue fibres, not only F-points. The
field and scheme universes follow the already recorded interfaces without a
new universe equality or a smaller coefficient/site universe.

Searches actually run with msearch.py (group NW, this item):

- leanfinder: "Fundamental character homogeneous line bundles on a flag variety
  have nonzero global sections whose zero sets are exactly the irreducible
  components outside the open Bruhat cell". Eight hits: residue-field evaluation
  of functions and principal-open section lemmas, not the requested flag theorem.
- loogle: `"Schubert"`. Zero hits.
- grep: `Bruhat|Schubert|fundamental.*(section|boundary)`. Three unrelated hits:
  Bruhat--Tits lattice comment, number-field cone ideals, measurable fundamental
  frontier. No match.
- leansearch: "fundamental weight line bundle nonzero sections zero locus Schubert
  boundary flag variety". Eight hits about structure-sheaf zero loci, topological
  zero sections and Lie weights. None states this result.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `fundamental.*(section|boundary)|fundamental_flag|lem-sfb-fundamental-flag-boundary-sections`:
  only unrelated purity/fundamental-class modules; no matching result.
- Local rg in those two trees and `dag/lean_names_upstream.json` for
  `exists_fundamental_flag_boundary_sections`: no prior declaration.
- The exact node-id grep in WeilConjectures has no match. Read the current
  dependency sources instead of inferring interfaces from their names.

No mathematical node fault or STATEMENT-DISPUTED finding. The first compile
found a precedence error in the function-to-character-Hom binder; repaired by
parenthesizing the Hom type. All variables/universes are explicit with
`set_option autoImplicit false`. Validation uses only the prescribed scompile.py
and deliver2.py wrappers; the read-only repository has not been edited.

Server validation: scompile.py compiled both the sandbox probe and the final library
module cleanly (7.5 s and 7.9 s respectively); no errors or unexpected warnings.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
