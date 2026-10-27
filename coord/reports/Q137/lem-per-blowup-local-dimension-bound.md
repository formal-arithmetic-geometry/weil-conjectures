## Worker report

Item: lem-per-blowup-local-dimension-bound. The module
`Sheaf.AlgebraicGeometry.BlowupLocalDimensionBound` states four clauses of this one DAG
node, all with `sorry` proofs. There are no new definitions, auxiliary axioms, new nodes,
statement corrections, dependency repairs or disputed statements. Each theorem carries
its source and the corresponding detailed proof steps from the node.

Hypothesis and conclusion correspondence:

- `blowup_local_dimension_bound`: `A : Type u`, `[CommRing A]`, `[IsLocalRing A]`,
  `[_root_.IsReduced A]`, `[IsNoetherianRing A]` render exactly the reduced Noetherian
  commutative local ring. `n : ℕ` and `hn : ringKrullDim A = (n : WithBot ℕ∞)`
  render finite Krull dimension n, without imposing quasi-excellence or characteristic.
  `T : OrdinaryBlowupTower (Spec (.of A))` retains every intermediate scheme, ideal,
  arrow, identification with its ordinary blowup, and composite. `hcoh` is coherence of
  each actual ideal module, using the full finite-type-kernel predicate. `hdense` says
  each center support is nowhere dense. No nonemptiness is imposed on centers.
  The first three conjuncts give reducedness, Noetherianness and dimension ≤ n of the
  last stage. `W`, its closed immersion `j`, `[IsReduced W]` and
  `IsNowhereDense (Set.range j)` render every reduced nowhere dense closed subscheme.
  The implication `1 ≤ n → ...` gives both dimension ≤ n−1 and the same upper bound
  for every stalk ring. Natural subtraction occurs only within that implication.
- `blowup_stalk_dimension_bound`: `X`, `[IsReduced X]`, `[IsNoetherian X]`, `x`, `n`
  and the equality on `ringKrullDim (X.presheaf.stalk x)` are the scheme formulation's
  hypotheses. The tower, coherent-center and nowhere-density hypotheses are identical.
  `pullback (T.toBase (Fin.last T.length)) (X.fromSpecStalk x)` is the actual canonical
  base change of the final composite, rather than a separately chosen modification.
  The conclusions repeat all five bounds/properties of the ring formulation for this
  scheme and its arbitrary reduced nowhere dense closed subschemes.
- `blowup_quasiExcellent`: the additional hypothesis is exactly
  `GabberModification.QuasiExcellent X`, meaning quasi-excellence on every affine open.
  The first conjunct gives reduced, Noetherian, quasi-excellent local schemes for every
  `x : X`. The second gives these properties for all tower stages and Noetherianness and
  quasi-excellence for every reduced closed subscheme of each stage. The third gives
  the same for all stages pulled back to every local scheme and their reduced closed
  subschemes. For this permanence clause no nowhere-density is imposed on the closed
  subschemes, exactly as in the node's final sentences.
- `blowup_rationalInputs`: `q : X ⟶ Spec (.of (ULift.{u} ℚ))` is the given rational
  structure morphism. The five conjuncts package local schemes, original stages, their
  reduced closed subschemes, local base-changed stages and their reduced closed
  subschemes as existing `QERationalResolutionInput` objects. `D.scheme = ...` fixes
  the underlying scheme and `HEq D.structureMap ...` fixes precisely the composite
  rational structure map. HEq accommodates the displayed equality of source schemes;
  it does not replace the canonical map with an arbitrary existential arrow.

The statement dependency records were read in full, and their actual source signatures
and docstrings inspected. Interfaces used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly exposing
  `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModules`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`;
  `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`;
  `Mathlib.AlgebraicGeometry.Pullbacks`: scheme pullbacks.
- Added already-landed statement dependencies (no new notion):
  `def-trf-ordinary-resolution-rule` supplies `OrdinaryBlowupTower` and `toBase` in
  `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`;
  `def-per-gabber-modification-data` supplies `GabberModification.QuasiExcellent` in
  `Sheaf.AlgebraicGeometry.GabberModificationData`;
  `def-per-qe-ordinary-resolution-rule` supplies `QERationalResolutionInput` in
  `Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule`.

Every recorded proof dependency's module is imported, with proof-only imports nonpublic.
At inspection, lem-sfb-generic-residue-transcendence-dimension-bound,
lem-per-quasi-excellent-localization and lem-per-quasi-excellent-finite-type-stability
had no Lean declarations and are only proof dependencies, so no speculative import or
statement was added for them. The remaining Mathlib matches and the closed upstream
flat-blowup-base-change audit declarations are imported from their recorded modules.

Edge cases checked against the exact signatures: length zero is included by
`OrdinaryBlowupTower.length : ℕ`; its initial isomorphism handles the base. Empty centers
are allowed (the unit ideal), with no nonempty-center assumption or deleted-stage
requirement. Empty W is allowed by universally quantifying schemes without Nonempty,
with topological dimension bottom. At n=0 the dimension-n assertion still applies,
and the n−1 assertions are correctly guarded by `1 ≤ n`. The node's proof observes
that a nowhere dense closed W is then empty, but the statement does not separately
assert this extra clause. Reducible rings such as the localization of k[x,y]/(xy),
DVRs and fields meet the intended hypotheses without domain, catenarity or positive
characteristic restrictions. No finite type over Q, separatedness, regularity of
centers, pure dimension or finite global dimension of X is imposed. Universe u is
shared by rings and schemes, including stalks and every tested closed subscheme.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: “Finite towers of blowups of reduced Noetherian local schemes have dimension
  at most the base and nowhere dense closed subschemes have strictly smaller dimension”.
  Eight related ring/module dimension and locally Artinian hits; no combined theorem.
- Loogle: `ringKrullDim, topologicalKrullDim`. One hit,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, identifies the two dimensions
  but supplies none of the blowup or center assertions.
- Mathlib grep in AlgebraicGeometry: `(blowup|blowUp).*(dim|tower)|(dim|tower).*(blowup|blowUp)`.
  No hits.
- LeanSearch: “The dimension of a tower of ordinary blowups of a reduced noetherian
  local scheme and of a nowhere dense closed subscheme”. Eight dimension definitions,
  quotient bounds and finite local dimension results; no blowup-tower theorem.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for the item id and dimension/blowup
  names: no existing item statement. Conceptual tower/quasi-excellence searches found
  the existing interfaces listed above; their node statements and complete source
  definitions were read and reused. DAG definition search and blueprint_refs.py search
  found no missing independent notion. Proposed full names were also searched in
  Mathlib, project source and dag/lean_names_upstream.json: no clashes.

Source checked: Temkin's linked original PDF, arXiv:0904.1592v2, printed p.30,
section 4.3 “Extensions 1,...,n”, especially its W∩X_i^{≤d}⊆W^{≤d−1} inclusion;
local Stacks source more-algebra.tex lemma-finite-type-over-excellent (07QU), and
morphisms.tex lemma-dimension-formula-general (0BAE). This assembly adds no source
hypothesis. The current blueprint ancestor and node's seven proof steps were read.

Validation: scompile.py compiled the sandbox and actual module successfully (6.4 s and
9.4 s), with no errors or unexpected warnings. An initial type-inference error under
`topologicalKrullDim` was fixed by specifying `(C := Scheme.{u})` on that pullback.
No declaration, universe, definition or mathematical statement changed in that repair.

## Second reading by Q137

The dispatcher prohibits starting another agent; this is a separate self-review pass,
not a claim of an independent reader. The maintainer's independent reading remains the
review step. I reread the node and all four signatures side by side: checked every
ring hypothesis, every center hypothesis, both final-scheme dimension bounds, the
local-ring consequence, the exact canonical stalk base change, affine-local
quasi-excellence for local schemes and all resulting stages and reduced closed
subschemes, and the final Q-category assertion with fixed structure maps. The three
already-landed notion nodes were added to stmt_deps after this check; no private
copies were written. No mismatch or mathematical statement fault was found. The
only elaboration repair was the explicit scheme category on the topological-dimension
pullback; no extra mathematical hypothesis was introduced.
