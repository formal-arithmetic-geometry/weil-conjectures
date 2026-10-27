## Worker report

The module `Sheaf.AlgebraicGeometry.LCICohenMacaulayStalks` states
`AlgebraicGeometry.isNoetherianRing_stalk_and_depth_eq_ringKrullDim_of_lci`.
Its sole theorem has `sorry` as its entire proof. The returned alias module and new
definition node have been removed. The affine-cover
condition is written directly in the theorem binder, exactly as the maintainer requested.
There are no new nodes, dependency repairs, or mathematical statement corrections.

Clause-by-clause correspondence with the node:

- A field k is `(k : Type u) [Field k]`.
- A scheme X over k is `(X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))`.
  The shared universe is the standard Mathlib scheme-morphism convention; any field and
  scheme can be placed in a common universe. There is no finiteness or cardinality bound.
- Locally of finite type is `[LocallyOfFiniteType f]`, with no quasi-compactness,
  separatedness, properness, or global finite-type hypothesis added.
- The affine-open-cover assumption is the explicit existential binder `hlci`.
  It quantifies over a family `A : I → CommRingCat`, with algebra
  structures `aA`, finite-type witnesses `ft`, and open immersions `φ i : Spec (A i) ⟶ X`.
  It requires that these immersions commute with f and the induced algebra spectrum maps,
  that every point has a preimage in some chart, and that every algebra satisfies
  `@Algebra.IsLocalCompleteIntersection k (A i) _ _ (aA i) (ft i)`.
  These are precisely affine charts with their induced k-algebra structures and the
  required complete-intersection coordinate rings. The index can be empty.
- The arbitrary point is `(x : X)`, with no closed-point restriction.
- The Noetherian conclusion is `IsNoetherianRing (X.presheaf.stalk x)`.
- Cohen-Macaulayness is the explicit equality
  `(IsLocalRing.depth (R := X.presheaf.stalk x) (X.presheaf.stalk x) : WithBot ℕ∞) =
  ringKrullDim (X.presheaf.stalk x)`. Depth is for the stalk as a module over itself,
  at its maximal ideal. The coercion embeds nonnegative depth into the dimension type;
  it neither truncates infinity nor identifies bottom with zero.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`: nontrivial commutative division ring.
- `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the coordinate maps on affine pairs
  are finite type.
- `Algebra.IsLocalCompleteIntersection` and its global predicate,
  `WeilConjectures.RingTheory.CompleteIntersectionOverField`: finite-type algebras with
  a principal-open cover by global complete intersections, including the zero ring.
- `IsNoetherianRing`, `Mathlib.RingTheory.Noetherian.Defs`: ideals finitely generated.
- `Ideal.depth` and `IsLocalRing.depth`, `WeilConjectures.RingTheory.Depth`: supremum of
  regular-sequence lengths, at the maximal ideal for the latter.
- `ringKrullDim`, `Mathlib.RingTheory.KrullDimension.Basic`: prime-chain dimension in
  `WithBot ℕ∞`.
Comparison read (not imported or used as a declaration):

- `AlgebraicGeometry.IsLocalCompleteIntersectionOver`,
  `Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion`: the existing affine-cover
  predicate described above;
  its body is now inlined in `hlci`, as requested by the maintainer. There is no
  abbreviation, no new definition node, and no import of the syntomic theorem module.

The imports also include the recorded proof-dependency modules that already exist:
affine stalk localization, localization away and at primes, polynomial-ring regularity,
regular equations of a global complete intersection, localization of quotients,
regular schemes and regular-local generators, regular sequences, quotient local structure,
Cohen-Macaulay nonzerodivisor quotients, and the depth-support bound. These are ordinary
(non-public) imports. The theorem docstring records all six proof steps of the node,
including the arbitrary-prime localization and the induction invariant.

Source read: `literature/stacks-project/algebra.tex`, `lemma-lci-CM`, Tag 00SB,
including its proof and its use of complete intersections and regular local rings.
The project's detailed proof supplies the arbitrary-prime passage via 00SC and
successive regular quotients via 02JN. No statement fault was found.

Edge cases checked before writing:

- Empty X: the cover predicate permits an empty index; no point x exists, so the
  universally quantified result is vacuous, without an added Nonempty assumption.
- Zero chart rings: allowed by the complete-intersection definition; their spectra
  contain no points, so they cannot supply an inadmissible zero stalk.
- The generic point of affine space is included; the point binder has no closedness
  test. In particular the generic point of the affine line has a field stalk with
  depth and dimension zero, whereas closed points have dimension one.
- Zero-dimensional nonreduced example k[e]/(e²): depth and dimension are both zero;
  reducedness or smoothness is not assumed.
- A polynomial presentation with no equations is permitted, and there is no assumption
  that the field is perfect, algebraically closed, or of characteristic zero.
- Non-quasi-compact schemes are allowed: only local finite type and an arbitrary
  affine cover are assumed.

Searches (the wrapper records the actual responses in `searches.jsonl`):

- LeanFinder via `msearch.py`: “Every stalk of a scheme locally of finite type over a
  field with an affine cover by local complete intersection algebras is Noetherian and
  has depth equal to Krull dimension”. Eight hits, including the Noetherian stalk
  instance, `IsLocallyNoetherian`, and `LocallyOfFiniteType.stalkMap`; none gives the
  complete-intersection depth conclusion.
- LeanSearch via `msearch.py`: “A local complete intersection scheme over a field has
  Cohen Macaulay local rings”. Eight hits about schemes and local Noetherianity,
  including `isLocallyNoetherian_of_affine_cover`; none states this theorem.
- Loogle via `msearch.py`: `Algebra.IsLocalCompleteIntersection, IsLocalRing.depth,
  ringKrullDim`. Zero hits; the service reports the first identifier unknown because
  it belongs to the project rather than Mathlib.
- Mathlib grep via `msearch.py`:
  `CohenMacaulay|IsLocalCompleteIntersection|depth.*ringKrullDim|ringKrullDim.*depth`.
  Zero hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `IsLocalCompleteIntersection` found the upstream ring definition and the existing
  scheme predicate. Reads of both signatures and bodies confirm they are usable.
  Other hits concern field change, completions, syntomic criteria and curve smoothing.
- Direct `rg` for `lci.*[Cc]ohen|[Cc]ohen.*lci|stalk.*[Cc]ompleteIntersection|
  depth_eq_ringKrullDim_of` found no exact theorem. The curve-smoothing docstring uses
  the mathematical assertion without stating it as a separate declaration.
- The prescribed recursive search for this item id in `lean/WeilConjectures` found
  no attachment. The proposed declaration name has no occurrence in Mathlib's project
  source trees or `dag/lean_names_upstream.json`.
- DAG search for the existing scheme predicate located
  `lem-trf-syntomic-geometric-fibres-affine-criterion` and
  `def-trf-local-complete-intersection-scheme-over-field`. The former module contains the base
  predicate, but its node is a theorem; the latter records only the distinct
  scalar-extension helper. This repair writes the affine-cover condition directly
  in the hypothesis and adds no definition node.

## Second reading by Q26

I reopened the current live node, the repaired module, and the full bodies of
`Algebra.IsLocalCompleteIntersection`, `Ideal.depth`, `IsLocalRing.depth`, and
`IsLocalCompleteIntersectionOver`. The node's field, scheme and structure map are
`k`, `X`, and `f`; local finite type is `[LocallyOfFiniteType f]`. The existential
`hlci` gives finite-type coordinate algebras, open immersions from their spectra,
compatibility with `f`, coverage of every point, and the recorded ring-lci predicate.
It is the body of the old scheme predicate with only bound variables renamed.
The unrestricted `x : X` gives both Noetherianity and depth equal to Krull dimension
for its stalk. The explicit coercion embeds depth into `WithBot ℕ∞`.
No closed-point, finite-cover, nonempty, smoothness or characteristic restriction
was introduced. The empty index remains permitted. The sole theorem proof is
`sorry`, with the original six-step natural-language proof retained in its docstring.
All universe variables are explicit and `autoImplicit` is disabled.

## Returned review repaired

The immutable head 23bc83817079 was returned under H12 because the added definition
node was newly unreachable from the live targets; the previous retry changed only
its report. I inspected the saved packet first and ran the prescribed unchanged
initial dry run: `OK (dry run): commit 8da5f998a16 passes the preflight and compiles;
nothing pushed`. That mechanical success does not resolve the independent reach
finding. This repair therefore applies L's specific simulated-check correction:

- Removed the new definition node
  `def-sfb-local-complete-intersection-scheme-over-field` from the packet.
- Removed its alias module
  `Sheaf.AlgebraicGeometry.LocalCompleteIntersectionSchemeOverField`.
- Restored the item's `stmt_deps` to the six entries on current main.
- Inlined the body of `IsLocalCompleteIntersectionOver` in `hlci`, using only
  `Algebra.IsLocalCompleteIntersection` (owned by the existing
  `def-weil-pbc-complete-intersection-over-field`) and Mathlib constructions.
- Removed the alias import; the module has no syntomic-theorem import. The open
  immersion module is now a public statement import.

I compared the retained packet to current main without running Git in the shared
repository: only `lean` differs in the item JSON after this repair. The item statement,
proof, all original dependencies, and all maintainer fields are unchanged. The wrapper
constructs the delivery on the live branch. This is a mathematical-interface repair
in the Lean file and node record, not a report-only re-push. No reachability flags
or other node chains were edited.

Validation: the repaired sole module passed `scompile.py` in both sandbox and
library mode (2.1 s and 3.2 s), with no errors or non-sorry warnings. A renewed
project search found no existing declaration with the theorem's name or item id.
