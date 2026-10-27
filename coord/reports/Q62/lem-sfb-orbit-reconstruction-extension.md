## Worker report

The module `Sheaf.GroupTheory.OrbitReconstructionExtension` states
`TopologicalGroup.orbitReconstruction_extension`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record.

Hypothesis and clause correspondence:

- A topological group is `(G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]`. All actions and cosets lie in `Type u`, exactly as in
  the recorded orbit-functor interface; the full action category itself is large.
- The given translation homomorphism is `Φ : G →* Aut (openOrbitForget G)`.
  `hΦ` states its defining formula `((Φ g).hom.app U) x = g • x` for every group
  element, open subgroup and coset. This characterizes the named homomorphism
  uniquely, rather than assuming any additional property of the group. Its
  assumed bijectivity is precisely `hbij : Function.Bijective Φ`.
- Both automorphism groups use the existing `SetFunctorAut.functorTopologyInstance`.
  The first two conjuncts assert `IsTopologicalGroup` for these topologies, including
  the arbitrary-fibre case; no finite-fibre or compactness premise is used.
- The isomorphism of topological groups is
  `r : Aut (discreteActionForget G) ≃ₜ* Aut (openOrbitForget G)`.
  Its first conjunct identifies it, on every automorphism, with the `mapAut` of
  left whiskering by `openOrbitInclusion G`. Thus it is actual restriction.
- The inverse sends `Φ g` to translation on every discrete continuous action:
  `((r.symm (Φ g)).hom.app S) s = (S.obj.obj.ρ g).hom s`.
- For every `S` and `s`, `∃ U : OpenSubgroup G` and the membership equivalence
  `h ∈ U ↔ (S.obj.obj.ρ h).hom s = s` assert exactly that the stabilizer is open.
  The subgroup is not an unspecified auxiliary object: this equivalence fixes it.
- `q : openOrbitAction G U ⟶ S` is an actual arrow of the full discrete continuous
  action category, hence an equivariant map. The equation for every `h : G`
  fixes its underlying function as `h U ↦ h s` on every coset. The existential
  conclusion states existence of this uniquely specified canonical map; no chosen
  map is used in a definition. Substituting `h = 1` gives `q(U) = s`.
- The formula for every `α` reads
  `((r.symm α).hom.app S) s =
  (discreteActionForget G).map q (α.hom.app U (QuotientGroup.mk 1))`, exactly the
  orbit-coordinate evaluation followed by the canonical orbit map in the node.
- The final `@Continuous` states continuity of that composite into the discrete
  space `S.obj.obj.V`, with the source explicitly the recorded functor topology.
  Explicit topology arguments avoid a typeclass search failure on the underlying
  set functor's fibre; they use the action's own topology, with no extra topology
  or assumption. Along with the preceding equality this gives continuity of each
  extension-coordinate evaluation.

Dependency declarations read in full and used:

- `Sheaf.GroupTheory.OpenOrbitFunctor`: `TopologicalGroup.openOrbitAction`,
  `OpenOrbitCategory`, `openOrbitInclusion`, `discreteActionForget`,
  `openOrbitForget` (and its scoped TopCat identity forgetful interface).
- `Sheaf.CategoryTheory.Galois.AutProfinite`:
  `CategoryTheory.SetFunctorAut.functorTopology`, `functorTopologyInstance`,
  `fiberTopology`, `fiberTopologyInstance`, `evaluation`. The topology declarations
  have independent object, morphism and fibre universes and no finite-fibre premise.
  The separate finite-fibre profiniteness theorem is not assumed here.
- Mathlib: `Functor.whiskeringLeft` and its `mapAut`, `ContinuousMulEquiv`,
  `OpenSubgroup`, `QuotientGroup.mk`, and the existing discrete continuous actions.

Source read: Bhatt--Scholze, Proposition 7.1.5, printed p. 64, from the local PDF,
particularly the injectivity paragraph decomposing arbitrary actions into coset
orbits. The proof docstring reproduces all eight DAG proof steps: restriction,
open stabilizers and orbit maps, translations, bijective reconstruction,
naturality giving the coordinate formula, the group topologies, continuity of
restriction, and continuity of extension.

Edge cases checked: the empty action gives no point-indexed obligations and has
its unique automorphism; a trivial group and singleton actions cause no exception;
non-faithful actions still have their actual stabilizers; non-normal stabilizers
(e.g. a point stabilizer in the permutation action of `S₃`) use left cosets without
any quotient-group/normality assumption. Infinite coset sets are allowed. There
is no Hausdorff, compactness, completeness or open-subgroup-basis hypothesis.
No statement correction or disputed clause was needed.

Searches for an existing statement (2026-10-24):

- `msearch.py leanfinder`, query "Restriction of natural automorphisms from discrete
  continuous group actions to open subgroup orbits is a topological group
  isomorphism": eight hits, principally `PreGaloisCategory.toAutHomeo`,
  `toAutMulEquiv_isHomeomorph`, `toAut_isHomeomorph`, `toAut_continuous`, and
  `ContAction.resEquiv`. The Galois results concern finite-fibre functors and compact
  groups; restriction of scalars concerns a different functor. None matches.
- `msearch.py loogle`, query `"Aut", "whiskeringLeft"`: zero hits.
- `msearch.py grep`, query `[Aa]ut.*[Rr]estrict|[Rr]estrict.*[Aa]ut` in
  `CategoryTheory`: zero hits.
- `msearch.py leansearch`, query "Natural automorphisms of discrete continuous group
  actions are determined by their restrictions to open subgroup coset actions":
  eight hits, including `DiscreteContAction`, `stabilizer_isOpen`,
  `QuotientGroup.discreteTopology_iff`, and finite-fibre Galois facts. These supply
  ingredients, not the statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `orbitReconstruction`,
  `orbit_reconstruction`, `openOrbit`, `openOrbitForget` and translation/Aut patterns
  finds the two recorded dependency modules and
  `TopologicalGroup.completeGroup_forgetful_automorphisms`. Read that theorem:
  it assumes Hausdorffness, an open-subgroup basis and compactness/completeness,
  whereas the current node assumes only bijectivity on orbits and also specifies
  stabilizer orbit maps and the coordinate formula. It is not the same statement.
- `rg` of `dag/lean_names_upstream.json` and both Lean roots for
  `orbitReconstruction_extension|orbitReconstruction|orbit_reconstruction` finds
  no existing declaration. Search of the upstream Lean root for the node id finds
  no attachment. Search for stabilizer/quotient restriction variants finds no match.

Validation: `scompile.py` passed for the delivered module in both sandbox and
library-module modes, with no errors or unexpected warnings. The required
`deliver2.py --no-push` dry run is performed before pushing.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
