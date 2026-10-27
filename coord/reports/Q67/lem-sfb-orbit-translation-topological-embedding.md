## Worker report

The module `Sheaf.GroupTheory.OrbitTranslationTopologicalEmbedding` states
`TopologicalGroup.orbitTranslation_topologicalEmbedding`, with `sorry` as its whole proof.
There are no definitions, new nodes, dependency repairs, or statement changes.

Source read: Bhatt--Scholze, *The pro-étale topology for schemes*, Section 7.1 and
Proposition 7.1.5, printed pp. 63–64, together with the node's nine-step elementary
expansion. The naturality equations use all equivariant orbit maps, as in the source.
The theorem docstring carries all nine proof steps.

Hypotheses and clauses, matched in order:

- The topological group is `G : Type u`, `[Group G]`, `[TopologicalSpace G]`, and
  `[NonarchimedeanGroup G]`. The latter extends `IsTopologicalGroup G` and says that
  every neighbourhood of the identity contains an open subgroup. `[T2Space G]` is
  exactly Hausdorffness. No compactness, completeness, normality, or finite-index
  hypothesis is imposed.
- `OpenOrbitCategory G` and `openOrbitForget G` are the recorded category and functor,
  with objects the open subgroups and arrows all equivariant maps. The inclusion and
  full forgetful functor remain the recorded `openOrbitInclusion` and
  `discreteActionForget`; no copies are made.
- Compatible universes and smallness are expressed by `Small.{u} (OpenOrbitCategory G)`
  and `∀ U V : OpenOrbitCategory G, Small.{u} (U ⟶ V)`. Thus these assert smallness of
  the actual category's objects and arrows, without choosing a different category.
  Coset sets are `G ⧸ U.toSubgroup : Type u`, with arbitrary `u`.
- The family `a : ∀ U, (G ⧸ U.toSubgroup) → G ⧸ U.toSubgroup` is a family of bijections
  exactly when `∀ U, Function.Bijective (a U)`. Its naturality is the equality
  `(openOrbitForget G).map f (a U x) = a V ((openOrbitForget G).map f x)` for every
  `U`, `V`, `f : U ⟶ V`, and `x`. The biconditional with `∃! α : Aut (openOrbitForget G),
  ∀ U x, α.hom.app U x = a U x` gives both directions of “precisely a family”, including
  uniqueness and the bijectivity of the components of every natural automorphism.
- `∃ Φ : G →* Aut (openOrbitForget G)` states the group homomorphism, and the formula
  `(Φ g).hom.app U x = g • x` pins every component to left translation. This is the
  canonical specified map, not an unconstrained map or extra hypothesis.
- `IsTopologicalGroup (Aut (openOrbitForget G))` uses the recorded pointwise topology,
  supplied by `SetFunctorAut.functorTopologyInstance` and its defining `functorTopology`.
- `IsEmbedding Φ` includes injectivity and the equality with the topology induced by
  this map. Its continuity is consequently included.
- For each `U` and representative `a : G`, the equality of sets identifies
  `MulAction.stabilizer G (QuotientGroup.mk a)` with
  `(fun h : G ↦ a * h * a⁻¹) '' (U.toSubgroup : Set G)`, exactly `aUa⁻¹`.
- For every target coset `y` and `x = QuotientGroup.mk a`, a `g₀` with `g₀ • x = y`
  is asserted. The complete fibre `{g : G | g • x = y}` equals the image of the
  stabilizer under `h ↦ g₀ * h`, its left coset, and `IsClopen` asserts both openness
  and closedness. This quantifies over every fibre and every representative.
- The final equality is `Φ ⁻¹' {α | α.hom.app U (QuotientGroup.mk 1) =
  QuotientGroup.mk 1} = (U.toSubgroup : Set G)` for every open subgroup, exactly the
  identity-coset preimage formula.

Dependency declarations inspected in full:

- `Sheaf.GroupTheory.OpenOrbitFunctor`: `TopologicalGroup.openOrbitAction`,
  `TopologicalGroup.OpenOrbitCategory`, `TopologicalGroup.openOrbitInclusion`,
  `TopologicalGroup.discreteActionForget`, and `TopologicalGroup.openOrbitForget`.
  The underlying `InducedCategory` retains all equivariant maps and their composition.
- `Sheaf.CategoryTheory.Galois.AutProfinite`: `CategoryTheory.SetFunctorAut.fiberTopology`,
  `fiberTopologyInstance`, `evaluation`, `functorTopology`, `functorTopologyInstance`.
  Their signatures admit arbitrary fibres and independent universes. The finite-fibre
  profiniteness theorem is not used as an assumption or conclusion here.
- Mathlib `Topology.Algebra.Nonarchimedean.Basic`: `NonarchimedeanGroup` as described above;
  `Logic.Small.Defs`: `Small`; the ordinary `Topology.IsEmbedding`, quotient action,
  `MulAction.stabilizer`, set images and `IsClopen` provide the remaining standard notions.

Edge cases checked mathematically: the trivial group (all cosets and fibres are singletons);
infinite discrete groups, including the identity subgroup (no finite fibres are assumed);
non-normal subgroups, for example an order-two subgroup in S₃ (the stabilizer is conjugated,
never identified with U without conjugation); the whole subgroup (the fibre is all of G);
identity representative and identity target; and an arbitrary family of functions that
fails bijectivity or naturality (the characterization then denies a natural automorphism).
No empty-group case exists for a group. Omitting Hausdorffness would permit a nontrivial
indiscrete group whose translations are not separated by these orbits, so it is retained.

Searches for existing statements:

- `msearch.py leanfinder`: “A Hausdorff topological group with a basis of open subgroups
  embeds into natural automorphisms of its open coset orbit forgetful functor”. Eight
  hits, including `PreGaloisCategory.toAutHomeo`, `toAut_continuous`,
  `exists_lift_of_quotient_openSubgroup`, and finite Galois reconstruction variants.
  These require finite fibres and do not state this result for all open orbits.
- `msearch.py leansearch`: “The action into natural automorphisms of the open subgroup
  orbit forgetful functor is a topological embedding”. Eight hits, including
  `autEmbedding_isClosedEmbedding`, `continuousSMul_aut_fiber`, `toAutHomeo`, and
  `OpenSubgroup.toSubgroup`. None supplies translation plus these clauses for arbitrary
  discrete cosets; `autEmbedding` embeds the automorphism group into its product instead.
- `msearch.py loogle`: `"Aut", "IsEmbedding"`, zero hits.
- `msearch.py grep`: `toAut_isEmbedding|openOrbit|orbitTranslation`, zero Mathlib hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `orbitTranslation|orbit_translation|openOrbit` found only the recorded orbit definitions
  and the parent complete-group reconstruction theorem. The parent adds completeness
  and states a homeomorphic isomorphism; it is not this theorem. Searching the item's id
  in `lean/WeilConjectures` found no declaration. Searching the proposed declaration name
  in Mathlib, both project roots and the upstream-name inventory found no collision.

No node fault or disputed statement was found. An initial compiler diagnostic required
coercing `U.toSubgroup`, rather than the induced-category object `U`, to `Set G`; this
was corrected without changing the mathematics. Every compile uses the prescribed
`scompile.py` server wrapper, in module mode.

Validation: the final module compiled cleanly through `scompile.py` as invoked by
`deliver2.py --no-push`. The dry run reported `OK`, with both preflight and compilation
passing. The signature record is verbatim, every Lean line is at most 100 characters,
and the sole postponed proof is the named theorem above.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
