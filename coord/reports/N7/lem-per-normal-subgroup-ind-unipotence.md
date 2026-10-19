## Worker report

The theorem `Rep.normal_subgroup_ind_unipotence` states every clause of
lem-per-normal-subgroup-ind-unipotence. Its only proof is `sorry`.
`Sheaf.RepresentationTheory.SubgroupUnipotence` supplies real definitions of the missing
unipotence notions and augmentation-power annihilation; it has no postponed proofs.
The original item statement and proof remain unchanged.

Hypotheses and clauses, matched against the node and ILO XVII pp. 327–330:

- `R : Type u` and `[CommRing R]` express an arbitrary commutative coefficient ring.
  There is no Noetherian, finite-ring, field, or nonzero-ring assumption.
- `G : Type v`, `[Group G]`, `[TopologicalSpace G]`, `[IsTopologicalGroup G]`,
  `[CompactSpace G]`, `[T2Space G]`, and `[TotallyDisconnectedSpace G]` give precisely
  a profinite group. `H : Subgroup G`, `[H.Normal]`, and `hH : IsClosed (H : Set G)`
  give the closed normal subgroup.
- `Rep.DiscreteContinuousRep.{u, v, w} R G` is the published upstream full subcategory
  of `Rep.{w} R G` defined by `∀ m, IsOpen {g | ρ g m = m}`. I read its complete source
  with `scompile.py --source WeilConjectures.RepresentationTheory.DiscreteContinuousRep`.
  The group action is R-linear and invertible, since it is a representation of a group.
- `Rep.IsSubgroupUnipotent H M` is a finite increasing filtration by R-submodules,
  starting at bottom and ending at top. Its explicit stability clause is for all g in G.
  The difference `ρ h m - m ∈ F i` for `m ∈ F (i+1)` says exactly that H acts trivially
  on each successive quotient. The infinite sequence merely extends the finite filtration
  constantly after its last term; it adds no condition. Length zero is allowed.
- `Rep.subgroupIndUnipotent H` is Mathlib `ObjectProperty.ind.{w}` of that property:
  a small filtered category, an actual colimit presentation in the discrete representation
  category, and unipotence of every diagram object. It is not defined by the criterion
  that the theorem is to assert. Both the index and module carriers use universe w.
- `.IsClosedUnderSubobjects` and `.IsClosedUnderQuotients` express the submodule and
  quotient clauses through monos and epis in the discrete module category.
  `.IsClosedUnderExtensions` expresses ambient short-exact extension closure. In particular
  its middle term is an object of the discrete continuous representation category, exactly
  as required; it does not assert extension closure in all algebraic G-representations.
- `HasColimitsOfSize.{w,w}` asserts the small colimits exist in the ambient category;
  the next universal clause `.IsClosedUnderColimitsOfShape J` puts those of ind-unipotent
  diagrams back in the subcategory. Empty diagrams are included.
- For every arrow of the ind-unipotent full subcategory, `HasKernel f ∧ HasCokernel f`
  asserts existence there. `PreservesLimit (parallelPair f 0) ...ι` and its colimit dual
  say that inclusion preserves those kernels and cokernels. These are the usual
  definitions of categorical kernels/cokernels, not an arbitrary replacement map.
- `subgroupAugmentationIdeal` is the linear kernel of
  `(MonoidAlgebra.lift R R H) 1`, the actual sum-of-coefficients augmentation. It is an
  R-submodule presentation of the two-sided ideal in the possibly noncommutative R[H].
  `subgroupAugmentationPower H 0 = ⊤` and the recursive submodule product give its literal
  ideal powers, with zeroth power the whole group algebra. Multiplication is the R-span
  of products; for two-sided ideals this agrees with their ideal product.
- `SubgroupAugmentationKills H M q m` quantifies over every element of that power and
  evaluates `Representation.asAlgebraHom (M.obj.ρ.comp H.subtype)` on m. Thus the first
  iff is exactly elementwise annihilation by some nonnegative integer power, represented
  by `q : ℕ`. It uses the actual restricted representation and its canonical group-ring
  extension, with no arbitrary algebra action supplied as a hypothesis.
- Under `[Module.Finite R M.obj.V]`, the last two iff statements identify ind-unipotence,
  unipotence, and one uniform exponent annihilating every element. This is finite
  generation over R, not over R[H] or finiteness of the underlying set.
- `Subsingleton M.obj.V → subgroupIndUnipotent H M` includes every zero module.

Dependency declarations read and used:

- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`, the recorded statement dependency
  def-weil-finitely-generated-module. Its field `fg_top : (⊤ : Submodule R M).FG` and the
  definition of FG say exactly finite spanning by R-linear combinations.
- New definition node def-per-normal-subgroup-unipotence, declarations listed below.
- Proof-only import `Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct`,
  `CategoryTheory.discreteContAction_finite_orbit_coproduct`, the recorded proof dependency.
  Its full signature and proof docstring were read: it covers discrete continuous compact
  group actions by finite orbits, including the empty case. It stays a non-public import.
- Mathlib's `ObjectProperty.ind` provides the filtered-colimit definition; its full
  signature and docstring were read. The closure predicates and kernel/cokernel
  definitions are also Mathlib's existing notions.

Edge cases checked before finalizing: zero M (length n=0 and exponent q=0); R the zero
ring; trivial H or G (length at most one and augmentation ideal zero); finite groups
with nontrivial characteristic-zero representations (not all representations become
unipotent); infinite sums with no uniform nilpotence bound (ind-unipotent need not be
unipotent); empty small diagrams (zero colimit); and arbitrary non-Noetherian R.
The extension clause retains the discrete continuity of its middle term. Degree zero
was checked particularly carefully: powers of R-submodules alone have scalar-span unit,
so the delivered recursive ideal powers explicitly start with the whole R[H]. This
repair changes neither node statement nor the augmentation criterion.

Searches actually run with msearch.py, recorded in searches.jsonl:

- LeanFinder: "Filtered colimits of unipotent discrete continuous representations of a
  normal subgroup and locally nilpotent augmentation ideal action": 8 hits, including
  localCohomology.ofDiagram, localCohomology.hasColimitDiagram, Hausdorffification and
  ModuleCat.FilteredColimits constructions. None defines or states this notion.
- Loogle: "Representation, IsNilpotent": zero hits.
- Mathlib grep: "indUnipotent|ind_unipotent|augmentationIdeal" in RepresentationTheory:
  zero hits; "IsUnipotent|IsIndUnipotent|unipotent" in the same directory: zero hits.
- LeanSearch: "Finite filtration of a representation by group stable submodules with
  trivial action on successive quotients and filtered colimits": 8 hits, including
  ModuleCat.FilteredColimits.colimitModule, Ideal.trivialFiltration and
  IsModuleFiltration. These do not encode group-stable filtrations with H-trivial graded
  pieces. Mathlib's existing ObjectProperty.ind is reused rather than reimplemented.
- Direct rg of the source library and lean/Sheaf for unipotent, Unipotent, indUnipotent
  and augmentationIdeal found no such declaration. Source grep for the item's exact id
  found no occurrence. `dag/lean_names_upstream.json` has no unipotent match.
- DAG grep and `tools/blueprint_refs.py search unipotent` found consumers and the finite
  Sylow filtration lemma sk-lem-curve-sylow-trace, not a definition of these notions.
  def-per-completed-augmentation-algebra concerns a completed algebra and finite
  coefficients, not the ordinary group algebra R[H] for arbitrary R.

The theorem docstring carries all ten DAG proof steps and the two named proof dependencies.
No statement correction or disputed mathematical assertion was needed. Each delivered
module compiled cleanly through scompile.py, separately in dependency order. The theorem
is intentionally left unproved for stage 3.

## New nodes

`def-per-normal-subgroup-unipotence` defines subgroup unipotence by finite G-stable
filtrations, ind-unipotence by genuine small filtered colimit presentations, the ordinary
augmentation ideal and its powers, and annihilation by a power through the restricted
group-algebra action. Source: ILO XVII 11.1.1–11.1.2, 11.2.1(vi)–(xi), 11.3.1–11.3.4,
pp. 327–330. Its module is `Sheaf.RepresentationTheory.SubgroupUnipotence`, with declarations
`Rep.IsSubgroupUnipotent`, `Rep.subgroupIndUnipotent`, `Rep.subgroupAugmentationIdeal`,
`Rep.subgroupAugmentationPower`, and `Rep.SubgroupAugmentationKills`. The searches above
are recorded in its mathlib_searches and found no duplicate. The new node is cited by the
item's stmt_deps. These are concrete definitions; no data is supplied by sorry or choice
from an undetermined existence theorem.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
