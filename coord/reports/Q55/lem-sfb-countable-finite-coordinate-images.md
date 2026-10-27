## Worker report

The module `Sheaf.Topology.CountableFiniteCoordinateImages` states
`Topology.countable_finite_coordinate_images`, with proof `sorry`. It introduces no new
definition. The node's statement, statement dependencies, accepted seven-step split and
proof dependencies are preserved. The docstring carries the complete proof plan and
identifies its agent origin and the outstanding request for an external reference.

The previous ending concerned a stage-1 re-split refusal. The current assignment is stage 2;
the live node has a passing Q139 stage-1 review, no Lean record, and a stage-2 queue entry.
The stage handoff at the start of `coord/brief-stage2.md` explicitly permits recording its
Lean statement. No repair note exists for this item, and no accepted split is reopened.

The hypotheses and constructions match the node as follows:

| Node hypothesis or construction | Lean rendering |
| --- | --- |
| Size convention | Explicit independent universe levels `uS uG uA uB`; countable products use `ℕ`, with no equality imposed on the four levels. |
| Compact Hausdorff space S | `(S : Type uS) [TopologicalSpace S] [CompactSpace S] [T2Space S]`. |
| Compact Hausdorff topological group G | `(G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]`. |
| Finite discrete spaces A_n | `(A : ℕ → Type uA)`, `[∀ n, Finite (A n)]`, `[∀ n, TopologicalSpace (A n)]`, `[∀ n, DiscreteTopology (A n)]`. `Finite` does not require nonemptiness. |
| Finite discrete groups B_n | The analogous `B : ℕ → Type uB` instances together with `[∀ n, Group (B n)]`. |
| Continuous coordinate maps p_n | `p : ∀ n, S → A n` and `hp : ∀ n, Continuous (p n)`. |
| Continuous coordinate homomorphisms q_n | `q : ∀ n, G →* B n` and `hq : ∀ n, Continuous (q n)`. No coordinate surjectivity hypotheses occur. |
| Diagonal P and image S_0 | `fun s n ↦ p n s` and `Set.range (fun s n ↦ p n s)`, carrying the product topology and its subtype topology. |
| Diagonal Q and subgroup image G_0 | `MonoidHom.pi q` and `(MonoidHom.pi q).range`. The latter has underlying set `Set.range (MonoidHom.pi q)` definitionally and coordinatewise group operations. |
| Corestrictions p and q | `Set.rangeFactorization (fun s n ↦ p n s)` and `(MonoidHom.pi q).rangeRestrict`; both send each point to precisely its diagonal tuple with its range membership proof. The second is a bundled homomorphism. |
| Finite-coordinate K_F | `(Subgroup.pi (F : Set ℕ) (fun n ↦ (⊥ : Subgroup (B n)))).comap (MonoidHom.pi q).range.subtype`. Membership unfolds to `∀ n ∈ F, b.val n = 1`, since membership in the bottom subgroup is equality to one. This is the node's specified subgroup, with no arbitrary choice. |

Each conclusion is retained:

| Node conclusion | Lean rendering |
| --- | --- |
| Both corestrictions continuous and surjective | The two pairs of `Continuous` and `Function.Surjective` conjuncts on those exact corestrictions. |
| S_0 compact Hausdorff | `CompactSpace (Set.range ...) ∧ T2Space (Set.range ...)`. |
| S_0 has a clopen basis | `TopologicalSpace.IsTopologicalBasis {U : Set (Set.range ...) | IsClopen U}`. |
| S_0 metrizable profinite | `TopologicalSpace.MetrizableSpace (Set.range ...)`, together with the preceding compact Hausdorff clauses and `TotallyDisconnectedSpace (Set.range ...)`. The latter spells out the profinite conclusion. |
| G_0 is a subgroup with coordinatewise operations and q a homomorphism | These are the actual data of `MonoidHom.range`, its inherited `Group` structure, and `MonoidHom.rangeRestrict`, rather than assumptions or existential choices. |
| Group image operations continuous | `IsTopologicalGroup (MonoidHom.pi q).range`, using the inherited subtype topology. |
| G_0 compact Hausdorff and metrizable profinite | The `CompactSpace`, `T2Space`, `TopologicalSpace.MetrizableSpace`, and `TotallyDisconnectedSpace` conjuncts on that exact subgroup range. |
| Each specified K_F open and normal | The `∀ F : Finset ℕ, IsOpen (...) ∧ (...).Normal` conjunct on the exact subgroup above. Being a subgroup is part of the constructed object. |
| All K_F form an identity neighbourhood basis | `(𝓝 (1 : (MonoidHom.pi q).range)).HasBasis (fun _ : Finset ℕ ↦ True) (fun F ↦ ...)`, with the same subgroups coerced to their underlying sets. The `True` is the standard unrestricted-index predicate of `Filter.HasBasis`, not an added hypothesis. |
| Equality of p-fibres exactly coordinate equality | `∀ s s' : S, Set.rangeFactorization ... s = Set.rangeFactorization ... s' ↔ ∀ n, p n s = p n s'`. |
| Equality of q-fibres exactly coordinate equality | `∀ g g' : G, (MonoidHom.pi q).rangeRestrict g = (MonoidHom.pi q).rangeRestrict g' ↔ ∀ n, q n g = q n g'`. |

Dependency declarations read and used:

- `def-weil-size-convention`: its existing convention record deliberately has no
  declaration or module. Explicit universe binders implement it; the unrelated historical
  derived-category audit declaration is not needed for this elementary topology statement.
- `def-kun-subspace-topology`: `instTopologicalSpaceSubtype`,
  `Mathlib.Topology.Defs.Induced`. The instance is the topology induced by `Subtype.val`;
  its module is imported publicly, so both ranges have the prescribed subspace topology.
- Proof dependency `lem-weil-pbc-continuous-image-quasi-compact`: `isCompact_range`,
  `Mathlib.Topology.Compactness.Compact`, imported publicly because compactness also occurs
  in the statement. Its signature only requires continuity and `CompactSpace` of the source.
- Proof dependency `lem-sfb-compact-countable-separating-metrizable`:
  `Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating`,
  `Mathlib.Topology.MetricSpace.PiNat`, imported without `public` for the proof plan.
  Its full context has an `Encodable` index, metric targets and a compact source, with
  continuity and pairwise separation hypotheses; it does not require nonempty spaces.

Standard constructors are reused directly: `MonoidHom.pi` from
`Mathlib.Algebra.Group.Pi.Lemmas`; `MonoidHom.range` and `MonoidHom.rangeRestrict` from
`Mathlib.Algebra.Group.Subgroup.Ker`; `Subgroup.pi` from
`Mathlib.Algebra.Group.Subgroup.Basic`; and `Set.rangeFactorization` from
`Mathlib.Data.Set.Operations`. Their definitions and signatures were read. `Filter.HasBasis`
is the standard neighbourhood-filter basis proposition, and
`TopologicalSpace.MetrizableSpace` asserts a compatible metric exists rather than changing
the already fixed topology.

Edge cases were checked before writing: empty S yields the empty subtype image; an empty
A_n forces S empty if the supplied map exists, and neither `Finite` nor any other space
hypothesis excludes that case. Trivial G and constant or nonsurjective coordinates yield
singleton or proper subgroup images and satisfy the same conclusions. Groups force B_n
nonempty, as in the node. For F empty, `Subgroup.pi ∅ ...` is the entire ambient product,
so its pullback is all of G_0. Noncommutative groups are covered: the statement uses
`Group` throughout, and each K_F is normal because its coordinates equal one. Independent
universe levels and `ℕ` indexing exclude no size cases. There are no completeness or
separation-of-source-points assumptions.

Searches for an existing complete statement:

- `msearch.py leanfinder`, query: “The diagonal images of a compact space and compact
  topological group in countable products of finite discrete spaces and groups are
  metrizable profinite with open normal finite-coordinate kernels”. Eight hits include
  `Profinite.pi`, `ProfiniteGrp.pi`, `Profinite.indexFunctor`, and limit constructions.
  They supply product/limit ingredients, not this combined image statement.
- `msearch.py loogle`, query `ContinuousMonoidHom.pi, MonoidHom.rangeRestrict, Subgroup.pi`:
  zero hits, with unknown identifier `ContinuousMonoidHom.pi`. Source inspection finds
  `MonoidHom.pi` as the appropriate constructor instead.
- `msearch.py loogle`, query `MonoidHom.pi, MonoidHom.rangeRestrict`: zero combined hits.
  Both individual declarations were located and read in the source.
- `msearch.py grep`, query `def (rangeRestrict|pi)|hasBasis.*(ker|pi)|def evalMonoidHom`,
  subdirectory `Topology/Algebra`: 17 ingredient hits, including profinite-group products,
  with no complete match.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `countable-finite-coordinate-images|countableFiniteCoordinate|finiteCoordinateKernel|diagonalImage`:
  no hits. `grep -rn` for the node id in `lean/WeilConjectures`: no hits.
- Direct concept search for finite coordinates and diagonal images in the project's
  topology sources finds the parent `ProfiniteMetricFunctionQuotients` proof plan and
  unrelated coordinate lemmas; the parent states descent of metric-valued functions,
  not this auxiliary statement. No duplicate of the full lemma was found.
- Direct Mathlib searches located the subgroup range/corestriction constructors,
  `Subgroup.pi`, the subtype topology, clopen-basis proposition, metrizability proposition,
  compact-image theorem and countably separating metrizability theorem; all were read.

The current blueprint's paragraph (3) was opened at `literature/blueprint/latest/`.
It motivates direct-image stability and does not supply the topological auxiliary proof;
the module preserves the node's honest agent-formulated provenance and WANTED reference.
No statement dispute or correction is needed. No new nodes or dependency modules are needed.

Validation: the module is compiled with `scompile.py` against the published live library.
The only theorem body is `sorry`; all variables and universes are explicitly bound, and
the source sets `autoImplicit` to false. The final delivery is checked by `deliver2.py`.

## Second reading by Q55

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
