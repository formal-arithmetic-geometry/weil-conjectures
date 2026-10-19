## Worker report

The module states the Tag 057I descent lemma. It introduces schemes `X`, `B`, and `Z`, morphisms `f`, `p`, and `σ`, and the commutativity hypothesis `hσ : σ ≫ f = p`. The assumptions `[Flat f]`, `[LocallyOfFinitePresentation f]`, `[QuasiCompact f]`, and `[QuasiSeparated f]` render flatness and finite presentation (locally finite presentation, quasi-compact, and quasi-separated). The explicit hypothesis `hred` gives geometric reducedness of each scheme-theoretic fibre through `f.fiberToSpecResidueField b`; `[Scheme.Hom.IsFiniteLocallyFree p]` renders finite locally free `p`; `hp₀` says the designated fibre has a point; and `hconn` says the designated fibre is geometrically connected. The conclusion provides an open immersion `i : X0 ⟶ X`, compact (quasi-compact) `X0`, an isomorphism of the fibre map over `b₀` with the original fibre, and geometric connectedness for every nonempty fibre of `X0 ⟶ B`.

The fibre notation is Mathlib's `Scheme.Hom.fiber`, and the maps to residue-field spectra are `Scheme.Hom.fiberToSpecResidueField`. The special-fibre equality is rendered by `IsIso (Scheme.Hom.fiberMap (a := i ≫ f) (b := f) i rfl (B.fromSpecResidueField b₀))`. The finite locally free dependency is the upstream declaration `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` in `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`; the fibre map is `AlgebraicGeometry.Scheme.Hom.fiberMap` from `WeilConjectures.Mathlib.AlgebraicGeometry.Fiber`. Other dependencies are Mathlib declarations recorded by their nodes: `Scheme`, `Flat`, `LocallyOfFinitePresentation`, `CompactSpace`, `GeometricallyReduced`, `GeometricallyConnected`, `IsOpenImmersion`, and `Scheme.residueField`.

Edge cases checked: `hp₀` excludes an empty designated multisection fibre; the conclusion quantifies only nonempty fibres, so empty fibres are allowed; `CompactSpace` imposes no Hausdorff condition; and `GeometricallyConnected` includes nonemptiness through `ConnectedSpace`.

Searches made: `msearch.py leanfinder` for a flat finitely presented family with geometrically reduced fibres and finite locally free multisection (no matching theorem); `msearch.py loogle` for `GeometricallyConnected` and `IsFinite` (no match); `msearch.py grep` for descent/finite-locally-free connected-fibre patterns (no match); `msearch.py leansearch` for finite locally free multisection descent (only general flatness/fibre results); `rg` over `lean/Sheaf` and `WeilConjectures` for connected-fibre/open-locus declarations (no existing statement). The file compiles cleanly with `scompile.py`; the expected `sorry` proof is the only postponed proof.


The final source check opened `literature/stacks-project/more-morphisms.tex`,
`lemma-descent-connected-fibres` (Tag 057I), and matched all five assumptions and both
conclusions. There is no statement correction, disputed statement, new node, or dependency repair.
The nonempty-range predicates are exactly fibre nonemptiness: a map has nonempty range if and
only if its source has a point. An open immersion's base change is an open immersion, so requiring
its canonical special-fibre map to be an isomorphism says exactly that the induced open subscheme
is the whole special fibre, rather than asserting an unrelated abstract isomorphism.

The module imports the recorded definition modules, including geometric integrality's bundle
module (which supplies geometric reducedness), and separately geometric connectedness. Proof
imports include `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
`Mathlib.AlgebraicGeometry.Sites.Fpqc`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`,
`Sheaf.AlgebraicGeometry.SectionComponentPullback`,
`Sheaf.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension`,
`WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent`, and the Mathlib proper,
quasi-finite, and universally-open morphism modules. The two component openness and
quasi-compactness proof prerequisites have no recorded module yet; the maintainer can add their
imports when those statements land. The theorem docstring records all six DAG proof steps.


The Mathlib dependency declarations, with their owning modules, are:

| Module | Declaration used |
| --- | --- |
| `Mathlib.AlgebraicGeometry.Scheme` | `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| `Mathlib.AlgebraicGeometry.Morphisms.Flat` | `AlgebraicGeometry.Flat` |
| `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` | `LocallyOfFinitePresentation` |
| `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` | `AlgebraicGeometry.QuasiCompact` |
| `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` | `AlgebraicGeometry.QuasiSeparated` |
| `Mathlib.AlgebraicGeometry.Fiber` | `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField` |
| `Mathlib.AlgebraicGeometry.Geometrically.Reduced` | `AlgebraicGeometry.GeometricallyReduced` |
| `Mathlib.AlgebraicGeometry.Geometrically.Connected` | `AlgebraicGeometry.GeometricallyConnected` |
| `Mathlib.Topology.Connected.Basic` | `ConnectedSpace` (inside geometric connectedness) |
| `Mathlib.Topology.Defs.Filter` | `CompactSpace` |
| `Mathlib.AlgebraicGeometry.OpenImmersion` | `AlgebraicGeometry.IsOpenImmersion` |
| `Mathlib.AlgebraicGeometry.ResidueField` | `Scheme.residueField`, `fromSpecResidueField` |

The scheme-conventions node introduces no declaration: its finite-presentation convention is
expanded into the three morphism-property assumptions. No empty-base case is excluded beyond
the node's own designated point binder. No properness, separatedness, global surjectivity of
`p`, constant degree, or affine hypothesis is added. The canonical fibre-map construction is
fully defined upstream; the delivery introduces no construction depending on an existence choice.

## Second reading by Q03

Independent maintainer second reading, 2026-10-18, of immutable delivery
`a498fbd8d30c8f81aac6eb6acd67bc96f9f71022`. The reader did not author this delivery.
Read the item node, all eleven statement-dependency nodes and their recorded
interfaces, the delivered module, and Stacks `more-morphisms.tex`, Tag 057I,
`lemma-descent-connected-fibres` (lines 13087–13200 in the Q03 source checkout).

| Node clause | Lean rendering | Verdict |
| --- | --- | --- |
| Schemes and structure maps | `{X B Z : Scheme.{u}}`, `f`, `p`, `σ` | Exact |
| Commutative multisection diagram | `hσ : σ ≫ f = p` | Exact composition order |
| Flatness | `[Flat f]` | Exact affine-local/stalkwise notion |
| Finite presentation | `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]` | Exact Stacks convention |
| Every fibre geometrically reduced | `hred : ∀ b : B, GeometricallyReduced (f.fiberToSpecResidueField b)` | Exact, over κ(b) |
| Finite locally free multisection | `[Scheme.Hom.IsFiniteLocallyFree p]` | Existing class extends finite, flat, locally finitely presented |
| Designated base point | `(b₀ : B)` | Exact |
| Nonempty multisection fibre at that point | `hp₀ : Set.Nonempty (Set.range (p.fiberι b₀))` | Exact: a function has nonempty range iff its domain is nonempty |
| Geometrically connected designated fibre | `hconn : GeometricallyConnected (f.fiberToSpecResidueField b₀)` | Exact; includes nonemptiness |
| Open subscheme of X | `∃ (X0 : Scheme.{u}) (i : X0 ⟶ X), IsOpenImmersion i ∧ …` | Exact representation up to its embedding |
| Quasi-compactness of that scheme | `CompactSpace X0` | Exact; no Hausdorff assumption |
| Whole designated fibre as an open subscheme | `IsIso (Scheme.Hom.fiberMap (a := i ≫ f) (b := f) i rfl (B.fromSpecResidueField b₀))` | Exact canonical base change of i, not an unrelated abstract isomorphism |
| All nonempty fibres geometrically connected | `∀ b : B, Set.Nonempty (Set.range ((i ≫ f).fiberι b)) → GeometricallyConnected ((i ≫ f).fiberToSpecResidueField b)` | Exact, allows empty fibres |

Read `Scheme.Hom.fiberMap` in upstream `WeilConjectures/Mathlib/AlgebraicGeometry/Fiber.lean:58`:
it is the actual pullback map induced by i and identities. Thus its isomorphism
condition identifies the induced open with the whole fibre, including its scheme
structure. Read `Scheme.Hom.IsFiniteLocallyFree` in upstream
`AlgebraicGeometry/Morphisms/FiberDegree.lean:782`: its parents are precisely
`IsFinite`, `Flat`, `LocallyOfFinitePresentation`. All other notions reuse the
recorded Mathlib declarations; no private or hollow definition is introduced.
`GeometricallyConnected` and `GeometricallyReduced` quantify over field base
changes through `geometrically`; `geometrically_iff_of_commRing` supplies exactly
the extension-of-residue-field interpretation. `ConnectedSpace` has a `Nonempty`
field. `Scheme.residueField` is the quotient of the stalk by its maximal ideal.

Edge cases: the base point binder excludes the empty base exactly as in the node.
An empty designated Z-fibre is excluded by hp₀; p may have degree zero or empty
fibres elsewhere and need not be globally surjective or constant-degree. Empty
X is incompatible with hconn, as it should be. Empty fibres in the conclusion
are unrestricted. No Noetherian, proper, separated, affine, characteristic or
field assumption on the original schemes was added. The universe u is bound
and arbitrary, and all schemes and field tests use the standard Scheme.{u}
interface; there is no independent smaller testing universe or extra universe
equality. There is no index-family or integer parameter to restrict.

Independent duplicate search: rg over Mathlib algebraic geometry, upstream
WeilConjectures and Q03 lean/Sheaf, using `multisection`, connected-multisection,
descent-connected-fibre and exists-open-geometrically-connected patterns. No exact
existing theorem was found. `exists_open_geometricallyConnected_fibres_of_generic`
was opened: it assumes an irreducible base and concerns its generic point, so is
not this multisection theorem. The worker's LeanFinder, Loogle, grep and LeanSearch
records remain present. One definition per notion is respected.

The module and theorem docstrings give Tag 057I, the blueprint id and all six
DAG proof steps: section component after base change; two-section comparison;
finite locally free shrinking; fpqc descent; quasi-compactness; special-fibre
identity and geometric-connectedness descent. The sole local theorem has proof
`by sorry`; no local proof, axiom, helper choice, definition, notation or instance
is added. The recorded lean.statement equals the file signature verbatim, and
no Lean line exceeds 100 characters. No statement correction, new node or
dependency module was delivered or needed for the statement.

The proof plan's section-openness and component-compactness lemmas are already
named DAG proof dependencies; they are not missing objects needed to type this
statement. The report's original note that imports can be added when these proof
lemmas are stated is therefore not a replacement of a canonical construction or
a wait on a statement prerequisite. The existing proof interfaces for section
base change, connected rational points, field-extension reflection and fpqc-open
descent were also read. The source module for fpqc-open descent, absent from the
local source checkouts, was read using the authorized `scompile.py --source`
wrapper and has the recorded compatible-open, unique-descent signature.

Compilation reproduced on the immutable module with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q03 lem-trf-finite-locally-free-multisection-connected-open snapshot/lean/Sheaf/TraceFormula/FiniteLocallyFreeMultisectionConnectedOpen.lean
```

Exit status 0, no diagnostics: sandbox `Sheaf/Stage2/Sandbox0.lean` 15.0 s;
library `Sheaf/TraceFormula/FiniteLocallyFreeMultisectionConnectedOpen.lean` 7.0 s.
The installed wrapper uses the server's per-file side overlay and private
`/dev/shm/nt-tmp/nt-local-compile-bz_uxt81/.lbuild`, with a 60-second file limit.
This independently verifies the worker's recorded clean-compile claim. No global
build, direct ssh command, live Lean write, delivery, merge or Git mutation was run.

Route-pivot check: no item statement/proof dependency is in the current dropped
list; no item repair note exists at origin/newtargets-dag. The proof is ordinary
scheme geometry and introduces none of the dropped higher-category machinery
or a pro-etale substitute.

Finding and change: H11, the original Second reading section explicitly said no
second reading had occurred. Replaced that placeholder with this actual independent
reading, retaining the Worker report. No mathematical or Lean change is needed.
