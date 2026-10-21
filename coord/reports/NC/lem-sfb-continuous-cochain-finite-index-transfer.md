## Worker report

Item: `lem-sfb-continuous-cochain-finite-index-transfer`.
Module: `Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer`.
Main declaration: `ContinuousCohomology.exists_continuousCochainFiniteIndexTransfer`.

This is a stage-2 statement delivery, not the stage-1 split already reviewed by Q01.
The current upstream node has a nine-step proof but no Lean record or module. The
preserved sandbox contained only dispatcher briefs. This delivery adds its actual
Lean record and its statement module, repairing the previous unchanged-node rejection.
The informal statement, dependencies and proof remain unchanged.

Hypotheses and clauses, in the node's order:

- A topological field is `{E : Type u} [Field E] [TopologicalSpace E]
  [IsTopologicalDivisionRing E]`. `Field` is exactly the `mathlib_match` of
  `def-weil-field`. No characteristic or separation condition is imposed on E.
- The profinite group is `{G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G]`. An open subgroup is `H : OpenSubgroup G`, with
  its genuine subgroup structure `H.toSubgroup` and inherited subspace topology.
- Coefficients are `A : TopRep.{w} E G`. Its fields give the underlying vector
  space, topological additive group, jointly continuous scalar multiplication,
  and linear action by continuous linear operators. Mathlib's `TopRep` alone
  does NOT impose joint continuity of the G-action: the explicit binder
  `hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)` supplies exactly that condition.
  The same applies to `B` and `hB` in the naturality clauses. The quantification
  over all A and hA is inside the existential family of transfer maps, so choices
  are simultaneous, rather than a pointwise existence assertion with no naturality.
- For any topological group J, the complex terms are the existing Mathlib spaces
  `C(Fin n → J, A)`. `continuousInhomogeneousD A hA n` is a concrete linear map
  with the displayed differential. Its first term is the action on the tail;
  `Fin.contractNth` multiplies adjacent entries in the internal faces and drops
  the last entry at the final index. Its exponent `j.val + 1` is the node's
  sign convention. All its data, including the continuity and linearity fields,
  are explicitly constructed, with no sorry or arbitrary choice.
- In degree zero `Fin 0 → J` is the one-point empty tuple space. Evaluation
  identifies its continuous maps canonically with A. The differential formula
  becomes `A.ρ g v - v`; there is no preceding differential. This is the node's
  `C^0 = V` convention in standard empty-tuple coordinates.
- `continuousInhomogeneousD_comp` states square-zero. It is a named theorem
  with sorry, matching the node's assertion that this is a complex; its proof
  docstring gives alternating-deletion cancellation through the homogeneous
  coordinate comparison. `continuousInhomogeneousComplex` then uses the actual
  cochain terms and differential in `CochainComplex.of`. Only the square-zero
  proof is postponed; none of its underlying data are chosen from existence.
- `CochainComplex (ModuleCat.{max v w} E) ℕ` means an ordinary nonnegative
  complex of abstract E-vector spaces. Its ordinary homology uses kernel/image
  in ModuleCat, with no topology on the cochain spaces and no closure of images.
  The scalar, group and coefficient universes u, v, w are independent; only the
  function-space universe `max v w` is used for the ambient module category.
- `subgroupContinuousInhomogeneousComplex H.toSubgroup A hA` uses the existing
  restricted representation `TopRep.res H.subtype A`. Joint continuity follows
  by composing hA with the subtype inclusion on the group coordinate. This is
  precisely the node's H-cochains with the restricted action, not new coefficients.
- `continuousInhomogeneousRestriction` is the canonical restriction, with each
  component constructed by the existing `ContinuousMap.compCLM` along tuplewise
  subgroup inclusion. `continuousInhomogeneousRestriction_comm` states that it
  commutes with d; its named sorry and proof docstring cover exactly the node's
  cochain-map clause. No arbitrary restriction map is assumed or selected.
- `cor A hA` is a morphism from that H-complex to the G-complex, so its components
  are E-linear and land in continuous functions and its cochain identities hold.
- `homotopy A hA : Homotopy (restriction ≫ cor A hA)
  (H.toSubgroup.index • 𝟙 (continuousInhomogeneousComplex A hA))` is an actual
  linear cochain homotopy, before cohomology. Category composition is left to
  right, so `restriction ≫ cor` is the node's `cor res`. Natural-number scalar
  multiplication is the same index multiple as its image in E, in all characteristics.
- A coefficient map is `b : A ⟶ B`, a continuous equivariant E-linear map in
  TopRep. The first conjunct says pointwise that b commutes with each `cor.f n`.
  The second says it commutes with every `homotopy.hom i j`. The induced map on
  continuous functions is the existing `ContinuousLinearMap.compLeftContinuous`.
  These equalities express simultaneous coefficient naturality, including actual
  homotopy components rather than just induced maps on cohomology.
- A closed G-stable E-subspace U with the subspace topology defines another
  eligible coefficient representation; its inclusion into V is a TopRep morphism.
  Applying the two naturality conjuncts to this inclusion gives exactly the
  asserted preservation with a common choice of transfer and homotopy for all
  coefficients. This follows even without closedness; no stronger hypothesis
  on U is needed in the naturality statement. The proof docstring explains the
  same-transversal construction behind this existential natural family.
- No completeness, local compactness, Hausdorffness or discreteness of coefficient
  spaces is assumed. In particular there is no `DiscreteTopology`, `CompleteSpace`,
  `LocallyCompactSpace` or `T2Space A` binder.

Dependency declarations and source inspection:

- `def-weil-field`: status mathlib, match `Field`, read in
  `Mathlib.Algebra.Field.Defs`; imported transitively by the topological-field
  import. There are no other statement dependencies.
- `TopRep`, `TopRep.res`, and `TopRep.Hom.hom`, from
  `Mathlib.RepresentationTheory.Continuous.TopRep`; their full signatures and
  docstrings were read, including its deliberately weaker continuity convention.
- `ContRepresentation` and `ContIntertwiningMap`, from
  `Mathlib.RepresentationTheory.Continuous.Basic`, read to check precisely which
  action and coefficient continuity obligations need explicit hypotheses.
- `ContinuousMap.compCLM` and `ContinuousLinearMap.compLeftContinuous`, from
  `Mathlib.Topology.ContinuousMap.Algebra`; `Fin.contractNth`, from
  `Mathlib.Data.Fin.Tuple.Basic`; `Homotopy`, from
  `Mathlib.Algebra.Homology.Homotopy`; `Subgroup.index`, from
  `Mathlib.GroupTheory.Index`. These existing notions are reused.
- The proof dependency `lem-sfb-topological-homogeneous-cochain-coordinates` has
  no Lean record, mathlib match, or closed upstream audit. Its statement was read.
  It is not needed to type this delivery, and no unavailable module is imported.
  Its explicit homogeneous coordinate proof is cited in the proof docstrings;
  the module can acquire its proof import when that independent statement lands.
- Read the current blueprint direct-images proof paragraph (3), Stacks
  `etale-cohomology.tex` 9007–9040 (0DVG), and the node's complete finite-coset
  prism proof. As Q01 recorded, the blueprint motivates the arithmetic expansion;
  the general-coefficient transfer itself is the agent's explicit construction.

Edge cases checked before writing:

- n = 0 uses empty tuples and d(v)(g) = gv - v; square-zero includes n = 0.
  In a homotopy on the ℕ-shaped cochain complex the unsupported components vanish,
  so the bottom identity uses precisely its degree-one-to-zero component.
- H = G has index one; H trivial is permitted when open. No normality is assumed,
  so nonnormal open subgroups are included.
- Zero coefficient spaces are included by TopRep. Empty tuple index sets remain
  valid. G itself is nonempty by its group structure.
- Positive characteristic, including characteristic dividing the index, is included:
  no index division is used. Non-discrete and non-complete coefficients remain valid.
- Arbitrary and indiscrete coefficient topologies are not silently excluded.
- Naturality covers subspace inclusions, zero maps, identities, and arbitrary
  continuous intertwining maps, with the same existential family throughout.

Searches made (all through the prescribed msearch wrapper and local read-only rg):

1. LeanFinder: `Continuous inhomogeneous cochain complex topological representations
   finite index subgroup transfer homotopy`. Eight hits included the older-name
   continuous homogeneous complex and ordinary `groupCohomology.inhomogeneousCochains`;
   no continuous finite-index transfer/homotopy was found.
2. Loogle: `TopRep.homogeneousCochains`. Twelve hits gave the current homogeneous
   complex and continuous cochains functoriality; no transfer. The local source was
   opened: it is an iterated continuous-map topological-module homogeneous complex,
   not the abstract-vector-space inhomogeneous complex requested here.
3. msearch grep: `inhomogeneous|def.*[Cc]ochain` under `RepresentationTheory/Continuous`:
   zero hits. Broader rg of both project's Lean trees found only discrete integer
   cochain coordinate interfaces and finite-degree field cocycles.
4. LeanSearch: `Continuous cochain complex over a topological field with continuous
   coefficient action restriction finite index transfer natural cochain homotopy`.
   Eight hits: homogeneous complexes and general homotopy machinery, no theorem
   with this transfer or coefficient-natural restriction-index homotopy.
5. rg of the seven proposed full declaration suffixes in Mathlib, WeilConjectures
   and Sheaf: no matches. The item's ID search under WeilConjectures: no matches.
6. The existing `Rep` inhomogeneous differential in
   `Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic` was read. It
   has all functions rather than continuous functions and same-universe Rep inputs;
   its formula and `Fin.contractNth` convention are followed, without replacing
   the node's arbitrary jointly continuous coefficients by discrete coefficients.
7. Read `Rep.exists_homogeneousCochains_inhomogeneous_coordinates` and its full
   docstring in the upstream continuous-coordinate module: coefficients are discrete
   ℤ-representations. It does not provide this node's E-linear general-topology
   interface. No duplicate of that special-case construction is imported or asserted.

All seven declarations belong to the complex, restriction, and transfer introduced
by this item itself and are listed in `lean.declarations`. No independent missing
notion is introduced; no new node or dependency repair is needed. There are three
named sorry theorems, each rendering a clause of this node, with source and complete
proof docstrings; all definitions contain actual data. No statement dispute or
statement correction was found. `set_option autoImplicit false` enforces explicit
binding of every variable and universe.

Validation: the complete module passed scompile.py in both sandbox and library
module modes, with no warnings or errors (the stage-2 sorry declarations are expected).

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
