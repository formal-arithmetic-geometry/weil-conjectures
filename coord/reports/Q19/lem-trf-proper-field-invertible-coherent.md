## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFieldInvertibleCoherent` states
`AlgebraicGeometry.Scheme.Modules.proper_field_invertible_coherent` with a single
`sorry` proof. No definition, dependency repair, new node or statement correction
is needed. The item's node changes only in `lean`.

Hypothesis and conclusion correspondence:

- A field k: `(k : Type u) [Field k]`.
- A scheme Y proper over k: `(Y : Scheme.{u})`
  and `(f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]`. The specified structure
  morphism is explicit; no extra structure on Y is assumed.
- An invertible O_Y-module N: `(N : Y.Modules) [N.IsInvertible]`, the recorded
  upstream local-rank-one notion. Its quasi-coherence is a consequence of local
  triviality, not an additional premise.
- Y is locally Noetherian: the first conjunct `IsLocallyNoetherian Y`.
- Y is quasi-compact: the second conjunct `CompactSpace Y`. Mathlib's compactness
  does not include a Hausdorff assumption.
- N is coherent: the third conjunct `RingedSpace.IsCoherent Y.toRingedSpace N`.
- O_Y is coherent: the fourth conjunct uses that same predicate on
  `SheafOfModules.unit Y.ringCatSheaf`, the structure sheaf as a module over itself.
- No dimension, reducedness or connectedness condition: none occurs among the
  binders. No nonemptiness or algebraic-closedness hypothesis occurs either.

The exact coherence predicate is used, including finite type for every kernel of
an arbitrary finite free map on every open. The dependency's retained
`IsQuasiCoherentFiniteType` abbreviation alone is not substituted for coherence.

Statement dependencies read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  Mathlib.AlgebraicGeometry.Morphisms.Proper. Its universally-closed condition
  implies quasi-compactness, so locally finite type here gives finite type.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  Mathlib.AlgebraicGeometry.Noetherian.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`, Mathlib.Topology.Defs.Filter.
- `pqf-def-coherent`: import Sheaf.AlgebraicGeometry.CoherentFiniteType, which
  publicly exposes `AlgebraicGeometry.RingedSpace.IsCoherent` from
  WeilConjectures.AlgebraicGeometry.Coherent. The predicate and its full docstring
  were read, as was the retained quasi-coherent finite-type conjunction.

Proof dependency declarations were read and their modules imported privately:
`IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs), `AlgebraicGeometry.Spec`
(Mathlib.AlgebraicGeometry.Scheme), `AlgebraicGeometry.LocallyOfFiniteType`
(Mathlib.AlgebraicGeometry.Morphisms.FiniteType),
`LocallyOfFiniteType.isLocallyNoetherian` (the public Noetherian module),
`QuasiCompact.compactSpace_of_compactSpace` and
`quasiSeparatedSpace_of_quasiSeparated` (Mathlib's corresponding morphism modules),
`AlgebraicGeometry.tilde`, `tilde.toOpen`, `tilde.toOpen_res`
(Mathlib.AlgebraicGeometry.Modules.Tilde), and
`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`
(WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian).
The theorem docstring gives all four proof steps, including the affine
structure-module comparison s ↦ s · τ(1).

Sources read directly: literature/stacks-project/coherent.tex, lines 2225–2241,
Tag 01XZ, explicitly asserts coherence of O_X and invertible modules on a locally
Noetherian scheme. morphisms.tex, lines 2765–2778, Tag 01T6, supplies local
Noetherianity and the quasi-compactness argument. These support the unchanged node.

Edge cases checked mathematically before writing: the empty scheme (all module
conditions hold locally and compactness is vacuous); Spec k; the nonreduced proper
scheme Spec(k[ε]/ε²); a finite disconnected union of proper schemes; positive
characteristic; proper schemes of arbitrary dimension. There is no restriction
excluding any of these. One common universe for k and Y follows the scheme API;
both can be placed in a common larger universe. No quantification over smaller
auxiliary schemes or test rings is introduced.

Searches, all through the prescribed msearch.py wrapper on 2026-10-24:

- leanfinder: "A proper scheme over a field is Noetherian and every invertible
  module and its structure sheaf are coherent". Eight hits including IsNoetherian,
  isNoetherian_iff, IsLocallyNoetherian, and IsProper.toLocallyOfFiniteType; none
  states the coherence conclusions together with Noetherianity.
- loogle: "AlgebraicGeometry.IsProper, AlgebraicGeometry.RingedSpace.IsCoherent".
  Zero hits; the search service does not index the project coherence predicate.
- grep of Mathlib/AlgebraicGeometry:
  `IsCoherent.*IsInvertible|IsInvertible.*IsCoherent|coherent.*invertible|invertible.*coherent`.
  Zero hits.
- leansearch: "On a proper scheme over a field an invertible module and the
  structure sheaf are coherent". Eight hits concerning algebraic invertible
  modules, scheme modules, structure sheaves, tilde and quasi-coherence; none
  states the item.
- rg on lean/WeilConjectures and lean/Sheaf for the node id, coherence/invertibility
  and proper/coherent combinations. Hits include the existing local coherence
  criterion, invertible quasi-coherence, and docstring references from consumers;
  there is no exact existing declaration. Exact proposed-name search has no hits.

No statement dispute or node fault was found. Compilation and preflight results
are recorded below after the checks finish.

## Second reading by Q19

I reread the node and completed module in a separate pass. This is a self-check;
no second agent was started, as required by the dispatch brief. The maintainer's
independent review remains the independent reading of this delivery.

The three mathematical hypotheses are exactly the field, the proper structure
map and the invertible module. The conclusion has precisely the four clauses:
local Noetherianity, compactness, coherence of N, and coherence of the structure
module. The structure sheaf is the canonical unit, not an arbitrary module.
Coherence uses the full finite-type-kernel predicate. The choice of an explicit
structure map expresses proper over k without a further premise, and the last
sentence of the node is respected by the absence of dimension, reducedness and
connectedness assumptions. All variables and the universe are explicitly bound,
with autoImplicit disabled. No mismatch was found or statement changed.

Validation: scompile.py compiled both sandbox and library module modes cleanly
(1.7 s and 1.5 s). deliver2.py --no-push reported OK: the delivery passes the
server preflight and per-file compilation. A local JSON comparison confirms
that `lean` is the only changed node field; every Lean line is at most 100 columns.
