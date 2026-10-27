## Worker report

The module `Sheaf.AlgebraicGeometry.UniformProjectiveFibreVanishing` states
`AlgebraicGeometry.UniformProjectiveFibreVanishing.exists_uniform_projective_fibre_vanishing`.
It has one postponed theorem, with the five accepted DAG proof steps in its docstring.
The two helper definitions have real data: `cohomology` is the recorded module-sheaf
right derived functor followed by restriction of scalars along the specified structural
map, and `zeroSections` is Mathlib's canonical degree-zero right-derived isomorphism.
The node statement, accepted split, proof and dependency lists are unchanged.

The inherited ending concerned an unchanged stage-1 assignment. The live node has a
stage-1 PASS dated 2026-10-23, no Lean record, and a stage-2 queue entry. The explicit
stage handoff in `coord/brief-stage2.md` §0 authorizes this stage-2 delivery. No stage-1
review is reopened. The returned delivery is repaired below under H13; its mathematical statement was accepted by the independent reviewer.

Clause-by-clause statement correspondence:

- The fixed nonnegative dimension is `n : ℕ`; no positivity condition is imposed.
  `P : Polynomial ℚ` and `hP : ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ z : ℤ,
  P.eval (d : ℚ) = (z : ℚ)` express exactly eventual integer-valuedness.
- `∃ m : ℤ, 1 ≤ m ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k] ...`
  puts the uniform bound before the field and subscheme. Thus it depends only on `n,P`.
  The field and scheme universe is arbitrary and explicitly declared.
- `Z : Scheme.{u}`, the map `i` into
  `ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))`, and `IsClosedImmersion i`
  express an arbitrary closed subscheme of the recorded base-change projective space.
  `ULift` places the finite coordinate set in the scheme universe without changing it.
- `ProjectiveHilbertPolynomial.IsCoordinatePolynomial k n i P` is the exact recorded
  eventual coordinate-dimension predicate, rather than an assumed Euler equality.
- `i.ker.toModules` is the existing ideal sheaf associated with the kernel of the
  immersion. For a closed immersion its defining subscheme is canonically the given
  subscheme, so it is the stated kernel of the structure-sheaf restriction.
  `RingedSpace.IsCoherent ... i.ker.toModules` expresses coherence in the node's
  finite-type-and-relations sense. This is the existing upstream Stacks 01BV
  predicate, imported directly without rebinding the dependency node.
- The first `∀ j : ℕ, 1 ≤ j → j ≤ n → Subsingleton ...` is precisely regularity:
  `RingedSpace.moduleCohomology` applied to
  `i.ker.toModules ⊗ₘ ProjectiveSpace.twist ... (m - (j : ℤ))`.
  `⊗ₘ` is the established scheme-module tensor notation. No independent regularity
  notion or duplicate twist is introduced.
- `∀ d : ℤ, m ≤ d →` retains every integer twist in the node. Its first conjunct
  quantifies over every `j > 0`, not just `j ≤ n`, and asserts both vanishings.
  The second sheaf is exactly `(Scheme.Modules.tensorPullback i).obj (twist ... d)`.
  Vanishing of the underlying module is `Subsingleton`, since the underlying carrier
  is a type; it is equivalent to the zero cohomology module.
- Three `Module.Finite k` conjuncts assert finite dimension for the ideal cohomology,
  the literal homogeneous degree-`d.toNat` polynomial submodule and closed-subscheme
  cohomology. Here `d ≥ m ≥ 1`, so `d.toNat` is the original integer degree and loses
  no cases. `cohomology` restricts scalars along the projective-space projection or
  `i` followed by that projection, respectively. No arbitrary field action is used.
- `Module.finrank ... = P.eval (d : ℚ)` is exactly the required dimension formula.
- The isomorphism `σ` identifies the literal homogeneous polynomial submodule with
  ambient degree-zero module cohomology. Its value on every standard chart is forced
  to be `chartRingEquiv ... (dehomogenizeX ... F.val) • twistGenerator ... d a`.
  Therefore this is the canonical monomial identification; its existence is a
  conclusion and imposes no extra hypothesis. The standard charts cover, so the
  displayed values determine the map uniquely, including dimension zero.
- The arrow `β` has source that same literal homogeneous polynomial module and
  target the closed-subscheme degree-zero cohomology. On each inverse-image standard
  chart its section is forced to be `tensorPullbackSection i` of the preceding
  dehomogenized polynomial section. This is the existing section-normalized tensor
  pullback and hence canonical restriction, not an unconstrained map.
- The left arrow is the module-cohomology map of the existing ideal inclusion
  `i.ker.toModulesι ▷ twist ... d ≫ (λ_ ...).hom`, restricted to `k`, followed by
  `σ.inv`. `Function.Injective`, `Function.Exact ... β` and
  `Function.Surjective β` give respectively the left zero, middle exactness and right
  zero of the displayed short exact sequence. Both arrows are morphisms in
  `ModuleCat k`, so the sequence is `k`-linear, not just a sequence of sets.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, its canonical
  projection and standard-open construction.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`;
  `TwistTensor` supplies the existing `twistGenerator` used to specify local values.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection` and its normalized
  adjunction; no private copy of pullback is made.
- Mathlib `Field` and `IsAlgClosed`, from the field and algebraic-closure nodes.
- `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality`:
  `ProjectiveHilbertPolynomial.IsCoordinatePolynomial`, with its underlying actual
  equations, quotient and dimension definitions read in full.
- `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent` (direct upstream
  import, with no dependency-record change), and Mathlib `SheafOfModules.IsFiniteType` / `IsQuasicoherent`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology` and
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `sheafCohomologyAndHigherDirectImages`, `moduleCohomology` and
  `globalSectionsFunctor`. Cohomology here is computed in module sheaves, rather
  than the separate abelian-sheaf `Scheme.Modules.H` construction.

The stated proof-dependency modules are imported without `public`, including the
homogeneous-ideal presentation, closed-immersion cohomology/coherence/projection,
coherent kernels, free-quotient regularity, regularity consequences, Picard projective
space cohomology, Euler characteristic, Proj scalar extension and polynomial scalar
extension. The field coordinate--Euler lemma and closed-cokernel cohomology lemma
have no recorded modules yet, so they cannot be imported; their uses remain explicitly
named in the proof docstring. They are proof prerequisites and no extra hypothesis
replacing them is added to this statement.

Sources read: Stacks `varieties.tex` 08AG (`lemma-bound-quotients-free`), 08A6
(`lemma-m-regular-up`), 08AE (`lemma-hilbert-polynomial-H0`);
`coherent.tex` 01XT (`lemma-cohomology-projective-space-over-ring`), and
`modules.tex` 01BV (`definition-coherent`). The latest blueprint unit and its direct-image
proof were read; this auxiliary Hilbert-bound item does not alter that unit's statement.

Edge cases checked mathematically before writing: for `n=0`, the range `1 ≤ j ≤ n`
is empty and every positive cohomology degree remains covered. For empty `Z`, the ideal
is the structure sheaf, `P=0`, the target is zero and the exact sequence reduces to the
monomial identification. For full projective space the ideal is zero and restriction
is the monomial isomorphism. Nonreduced subschemes require no extra assumption.
An unrealizable numerical polynomial makes the conclusion for subschemes vacuous.
There is no nonemptiness, reducedness, characteristic, or extra size assumption.

Searches actually run with `msearch.py` (recorded in `searches.jsonl`):

- LeanFinder: "Uniform bounded regularity and cohomology vanishing for ideal sheaves
  of projective subschemes with fixed Hilbert polynomial". Eight hits, including
  `ProjectiveSpectrum.vanishingIdeal` and `AlgebraicGeometry.Proj`; none states the
  uniform bound with its restriction and finite-dimension conclusions.
- Loogle: `"regular", "Sheaf"`. Twelve hits about regular topologies and sheaf
  conditions, not Castelnuovo--Mumford regularity or this statement.
- Mathlib grep in `AlgebraicGeometry`: `Castelnuovo|Mumford|hilbertPolynomial|HilbertPolynomial`.
  Zero hits.
- LeanSearch: "Coherent sheaf is finite type and kernels of maps from finite free
  sheaves on every open subset are finite type". It finds Mathlib `IsFiniteType`,
  finite presentation and local generators; these provide ingredients, not the
  uniform theorem. The exact coherent definition was found upstream by source search.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  uniform projective fibre vanishing, `HilbertUniform`, Hilbert polynomial,
  regularity, module cohomology and polynomial sections found the dependency APIs
  above and no declaration stating the item. The relative uniform-section theorem
  is not an exact match: it concerns families and lacks this field regularity and
  all-positive-cohomology conclusion. Its source is not imported into this module.

No new nodes and no statement correction. No STATEMENT-DISPUTED issue found.
The theorem has deliberately not been proved at stage 2. The module was compiled
through `scompile.py`, both as sandbox and library module, with no errors or warnings.
The first compile detected the scheme-module tensor notation issue; using the existing
`⊗ₘ` notation resolved it without changing any mathematical object or universe.

## Repair of return H13

The independent review of immutable head `6bd4901c1991` accepted the item mathematics
clause by clause and returned only the dependency-record rebind. Removed
`dag/nodes/sec-abelian-varieties/pqf-def-coherent.json` from this delivery. The live
Q25 record still owns `Sheaf.AlgebraicGeometry.CoherentFiniteType` and
`AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`; this repair does not
change that node, its declarations, or its module ownership.

The item already directly imports `WeilConjectures.AlgebraicGeometry.Coherent` and
uses `AlgebraicGeometry.RingedSpace.IsCoherent`. Reading that definition confirms
Stacks 01BV: finite type plus finite type of the kernel of every finite free map
on every open. It supplies exactly the coherent-ideal conclusion. Q25's separate
quasi-coherent-and-finite-type declaration remains available to its existing
consumers. This explanation is now also in the item's `lean.note`.

The Lean module is byte-identical to the saved returned packet, with SHA256
`9b6885902c1d85e92a76f2108666370c822e294c1a53724874296ad0e45ffaa1`.
Only the item's `lean.note` and report are revised, and the dependency JSON is
omitted. Comparison with the current read-only main node confirms that the item's
only changed field is `lean`. No theorem statement, helper, import, dependency
list, or proof plan changed. No dependency module or new node is delivered.

The initial saved-packet dry run passed preflight and compilation as commit
`ed1d3416079`; that pass did not itself fix the independently identified H13 fault.
The repaired packet is recompiled and dry-run before delivery.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
