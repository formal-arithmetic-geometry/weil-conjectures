## Worker report

The delivery states `AlgebraicGeometry.quasiExcellent_affineOpens_of_locallyOfFiniteType`
in `Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability`. Its only postponed proof is
this theorem, with `sorry`; its docstring supplies all six steps of the node's proof.
No definition, hypothesis, node statement, proof route, or dependency record is changed.
Only the item's `lean` field is attached.

The previous retry note confused the completed stage-1 split with this stage-2 item.
I opened the current node: its Q29 `reviewed` record certifies the split and its Q29 report
is explicitly a Stage-1 report; it has no `lean` or `reviewed_lean` record. Thus this work
uses the reviewed split without splitting it again.

Clause-by-clause statement match:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Schemes X and Y and their morphism h | `{X Y : Scheme.{u}} (h : X ⟶ Y)` |
| h locally of finite type | `[LocallyOfFiniteType h]` |
| Every affine open of Y has quasi-excellent coordinate ring | `hY : ∀ V : Y.affineOpens, IsQuasiExcellent Γ(Y, V)` |
| Every affine open of X has quasi-excellent coordinate ring | First conjunct `∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U)` |
| If X is quasi-compact | Antecedent `CompactSpace X` of the second conjunct |
| X has a finite affine open cover | `∃ (n : ℕ) (U : Fin n → X.affineOpens), (⨆ i : Fin n, (U i : X.Opens)) = ⊤ ∧ …` |
| Its coordinate rings are Noetherian | `∀ i : Fin n, IsNoetherianRing Γ(X, U i)` |
| No finite-dimensionality or universal catenarity hypothesis | Neither appears among the binders or antecedents; the hypothesis uses `IsQuasiExcellent`, not `IsExcellent` |

The second conjunct renders the node's explicit finite-cover characterization of
Noetherianness directly, without an auxiliary definition. `Fin n` describes every finite
cover up to reindexing, including the empty cover. Mathlib's
`AlgebraicGeometry.IsNoetherian` is local Noetherianness plus quasi-compactness;
`isNoetherian_iff_of_finite_iSup_eq_top` and
`isNoetherian_iff_of_finite_affine_openCover` confirm the finite-cover characterization.
The result does not assume that h is quasi-compact, that Y is quasi-compact, or that
X itself is quasi-compact in order to conclude the first conjunct.

Recorded statement dependencies opened and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`. I read the structure's
  local-affine condition and the scheme morphism interface.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`. Its signature requires finite type on every
  affine pair; the recorded cover equivalence identifies it with the node's definition.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsQuasiExcellent`.
  I read its full definition: Noetherian, G-ring, and open regular loci for all finite
  type algebras in the ring universe. This is the recorded notion; no replacement
  scheme-level predicate is introduced.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
  I read its separation-free `isCompact_univ` field. No Hausdorff condition is added.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the abbreviation for the ring being Noetherian as a module over
  itself, equivalently every ideal finitely generated.

Proof dependencies are retained through ordinary (non-public) imports:
`Mathlib.AlgebraicGeometry.Noetherian` supplies `AlgebraicGeometry.IsLocallyNoetherian`;
`Sheaf.RingTheory.FiniteTypeGRing` supplies `isGRing_of_finiteType`;
`Sheaf.AlgebraicGeometry.GRingAffineCover` supplies
`AlgebraicGeometry.isGRing_of_affine_open_cover`; and
`Sheaf.AlgebraicGeometry.JTwoAffineCover` supplies
`AlgebraicGeometry.j2_of_affine_open_cover`.
Their source declarations and docstrings were read. The recorded ring finite-type
leaf `Algebra.FiniteType.isNoetherianRing` and the bare-ring-map notion
`RingHom.FiniteType` are in `Mathlib.RingTheory.FiniteType`, imported through the
recorded finite-type and G-ring modules. `IsGRing` from `Sheaf.RingTheory.GRing` is
imported by `ExcellentRing` and the G-ring proof modules. These use the same shared
notions as the item's proof, with no private copies. In particular the J-2 locality
lemma requires local Noetherianness, established before it is applied in the docstring.

Source check: I opened `literature/stacks-project/morphisms.tex`, labels
`lemma-locally-excellent` (0HAB) and `lemma-finite-type-excellent` (0HAC), and
`more-algebra.tex`, `definition-excellent` (07QT) and
`lemma-finite-type-over-excellent` (07QU). The former states the quasi-excellent
alternative for locally finite-type morphisms with no quasi-compactness condition.
I also opened `properties.tex`, `definition-noetherian` (01OV), for the second clause.
The statement is unchanged and agrees with these sources.

Edge cases checked before writing:

- Empty X: the first conjunct includes its affine opens and zero coordinate rings;
  the second allows `n = 0` and the supremum of the empty cover equals top on the
  empty space. No `Nonempty` or nontrivial-ring condition is imposed.
- Empty Y: a morphism to it forces X empty; no excluded case is introduced.
- An infinite disjoint union of spectra of a field over that field: locally finite
  type and quasi-excellent affine coordinate rings, but not quasi-compact; the finite
  cover conclusion is conditional, so it makes no false global Noetherian claim.
- Identity morphisms and quotient maps: no injectivity, positive dimension, or
  nontriviality condition on chart ring maps occurs.
- Schemes of arbitrary dimension and quasi-excellent rings that are not excellent:
  neither dimension nor universal catenarity is assumed.
- The scheme universe `u` is explicit; section rings and finite-type test algebras
  use the recorded dependency's same universe. There is no independent, smaller
  test-algebra universe and no auto-bound variable.

Searches for an existing theorem (2026-10-18):

- `msearch.py … leanfinder "A scheme locally of finite type over a quasi excellent
  scheme has quasi excellent affine coordinate rings and is Noetherian if quasi
  compact"`: eight hits, headed by `AlgebraicGeometry.IsNoetherian`,
  `IsLocallyNoetherian`, `isNoetherian_iff`, and
  `LocallyOfFiniteType.isLocallyNoetherian`; none states quasi-excellence permanence.
- `msearch.py … loogle "IsQuasiExcellent, AlgebraicGeometry.LocallyOfFiniteType,
  AlgebraicGeometry.IsNoetherian"`: zero hits, unknown Mathlib identifier
  `IsQuasiExcellent`.
- `msearch.py … grep "IsQuasiExcellent|quasi.?[Ee]xcellent|quasiExcellent"`:
  zero Mathlib hits.
- `msearch.py … leansearch "Locally finite type morphisms preserve quasi excellent
  schemes; a quasi compact quasi excellent scheme is Noetherian"`: eight hits,
  all on locally finite type and its local-Noetherian permanence; no exact theorem.
- `rg` over `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`
  with `quasi.?[Ee]xcellent|IsQuasiExcellent|lem-per-quasi-excellent-finite-type-stability`:
  the source checkout has only a contextual mention in derived stability; the side
  library has the shared `IsQuasiExcellent` and ring theorems, but no scheme permanence
  theorem. In particular `isGRing_of_finiteType` alone has neither the J-2 conclusion
  nor the global affine-open conclusion.
- A separate exact-name `rg` for
  `quasiExcellent_affineOpens_of_locallyOfFiniteType` over Mathlib, upstream sources,
  the side library, and the upstream name index returned no hits.

No new nodes, dependency repairs, statement correction, or STATEMENT-DISPUTED fault.

Validation: the prescribed `scompile.py` compiled the sandbox statement and its library
module separately, with no errors or warnings (3.5 s and 2.7 s). No direct Lean or Lake
build was run. The required `deliver2.py --no-push` preflight follows this report.


## Second reading by Q07

A fresh retry worker read the retained first worker's module, node copy, search log,
and report, alongside the current shared node and all its recorded statement and proof
interfaces. This is a second reading of the retained delivery, not a new stage-1 split.
Q29's `reviewed` field and report concern stage 1; the current shared node still has
neither `lean` nor `reviewed_lean`. The prior stale-assignment diagnosis does not apply
to the stage-2 statement requested here.

I checked the scheme and morphism binders against `Scheme` and `Scheme.Hom` and checked
`[LocallyOfFiniteType h]` against its full affine-pair definition. The sole geometric
hypothesis `hY` quantifies over every affine open of Y and uses the recorded shared
`IsQuasiExcellent` definition (Noetherian, G-ring, and J-2). The first conjunct quantifies
over every affine open of X with exactly that same predicate. The second conjunct has
`CompactSpace X` only as its antecedent and asserts a cover indexed by `Fin n`, equality
of its supremum with top, and Noetherianness of every chart ring. Thus it gives exactly
the node's explicit finite-affine-cover conclusion. No quasi-compactness of h or Y,
separatedness, dimension bound, universal catenarity, or nontriviality hypothesis occurs.

I reopened Stacks 07QT, 07QU, 0HAB, 0HAC and 01OV and matched these clauses. The empty
source allows n = 0; an infinite disjoint union requires no finite cover unless it is
quasi-compact; identity and quotient morphisms require no extra hypothesis. The explicit
scheme universe and the shared quasi-excellence predicate introduce no smaller independent
test-algebra universe. The docstring retains all six proof steps, including local
Noetherianity before J-2 locality; the recorded proof modules are imported. Searches of
the current side library, source checkout, and upstream name index still find no existing
scheme quasi-excellence permanence theorem with this statement. The inherited four actual
msearch results remain in searches.jsonl and are faithfully summarized above.

No mathematical mismatch was found and no Lean declaration or statement needed changing.
I verified programmatically that only `lean` differs from the current base node, that its
signature is verbatim from the module, and that every Lean line has at most 100 characters.
The prescribed fresh `scompile.py` run passed both sandbox (3.5 s) and module (2.7 s)
compilation with no diagnostics. The fresh prescribed `deliver2.py --no-push` printed
`OK (dry run): commit 16df7c4eaa passes the preflight and compiles; nothing pushed`.
This second-reading section is the only report addition; the delivery is dry-run again
before the final push. No live source or launcher script was edited.
