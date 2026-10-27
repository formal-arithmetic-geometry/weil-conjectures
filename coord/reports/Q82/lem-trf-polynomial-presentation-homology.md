## Worker report

States `Algebra.PolynomialHomology.computationData_exists` in
`Sheaf.RingTheory.PolynomialPresentationHomology`. Its `ComputationData` records the
representable generator-fibre isomorphism, trivial Kan fibration to a singleton,
representable contractibility, and the canonical derived-colimit comparisons with
naturality in both the coefficient functor and the augmented resolution.
Only the final named theorem has `sorry`; its docstring gives all six DAG proof steps.
All helper data are explicit constructions. No statement correction or disputed assertion.

Hypotheses and clauses, individually:

- The small commutative rings and their homomorphism are `{A B : CommRingCat.{u}}`
  and `f : A ⟶ B`. The larger working universe is `max (u + 1) v`, allowing every
  containing Lean universe without identifying ring and category universes.
- All small polynomial algebras augmented over B form the existing
  `Algebra.CotangentSites.Presentations f`. Its `IsPolynomial` quantifies over every
  `E : Type u` and a coefficient-compatible polynomial-ring isomorphism; its full
  over/under category imposes precisely the structural and augmentation triangles.
  `Category` applies Mathlib `AsSmall.{v}` to raise morphisms as well as objects.
  Thus this is a small category in the containing universe. No surjectivity is imposed.
- `Q : SimplicialObject (Category f)` is exactly an augmented simplicial polynomial
  A-algebra. It includes polynomiality degreewise and all augmentation and base squares.
  Conversely any augmented simplicial polynomial A-algebra gives this functor by
  the full-subcategory construction, with no choice of polynomial coordinates required.
- The actual underlying augmentation is `augmentation Q`; its components are the
  ring augmentations, and naturality follows from the over-category triangle.
  `SSet.Enhanced.trivialKanFibration (augmentation Q)` is the required hypothesis.
- For every presentation T and arbitrary generator type E, `coordinates` quantifies
  over a polynomial isomorphism `e` and its coefficient equation. It gives an `Iso`
  from `homSet Q T` to `∏ᶜ (fun x : E ↦ fibre Q (epsilon_T (e(X x))))`.
  The following equality of simplicial maps fixes its value: projection to each fibre
  and then to Q equals `elementEvaluation` on the corresponding generator. Its
  degreewise components are exactly the generator images under each augmented map g.
  This rules out an unspecified unrelated isomorphism. Fibres are actual categorical
  pullbacks against the prescribed constant point, followed by the standard `ULift`.
- `trivial` says the unique map from each representable simplicial set to the
  constant singleton is a trivial Kan fibration. `resolution` states its homotopy
  equivalence to that singleton using the general computation's `IsResolution`.
  Its inverse and both homotopy equivalences are quantified there; this is the
  existing finite-homotopy-zigzag formulation, implied by the strict homotopy
  given by the cited trivial-Kan theorem.
- The coefficient ring is any `R : Type (max (u + 1) v)` with `[CommRing R]`, and
  F is any covariant functor to `ModuleCat` in this universe. No exactness,
  flatness, additivity of F, or augmentation-surjectivity restriction is added.
- `comparison` is a natural isomorphism of functors into the actual Mathlib `DerivedCategory` from
  the localized `evaluationComplex` to `derivedColimit bar`. `evaluationComplex`
  is literally alternatingFaceMapComplex followed by embeddingDownNat extension:
  degree -n is F(Q_n), differential is the alternating face sum, and positive
  terms are zero. `opOp`/`unopUnop` only implement the opposite-site convention.
- The target `derivedColimit bar` is the universal left-derived colimit, defined
  using the diagram category and its degree-zero embedding. The already recorded
  bar-system model has a summand for each composable string and first-vertex
  coordinates through `Computation.forwardGenerator` and `forwardDifferential`.
  Those declarations and their full signatures/docstrings were read. The comparison
  is fixed by `normalization` to `C.comparison`, so it inherits its projective-resolution
  roof and precisely its canonical signed first-vertex bar model.
- The naturality of `comparison.hom` spells out the square for every natural
  transformation F→G, with `evaluationDerived` and `colimitDerived` the actual
  localized evaluation and universal derived-colimit functors.
- `naturalityResolution` spells out `s(F(h)) ≫ a_Q' = a_Q` for every augmented
  simplicial map h between two resolutions, using the actual alternating-complex
  map and localization. No chosen inverse to a homotopy appears in these arrows.
- `bar` and `C` are parameters for the already recorded canonically normalized
  construction data, whose existence is separately stated by the existing
  `categoryColimitBarSystem_exists` and `computation_exists`. They are not new
  mathematical assumptions, and no definition selects arbitrary data from a
  merely existential postponed theorem. Normalization retains all canonical content.

Dependency declarations read and used:

- def-weil-size-convention: its recorded metatheoretic convention, rendered by
  explicit universes, `AsSmall`, and containing-universe module and derived categories.
- Mathlib.AlgebraicTopology.SimplicialObject.Basic: `CategoryTheory.SimplicialObject`,
  faces `δ` and degeneracies `σ`; actual functors and natural transformations.
- Sheaf.AlgebraicTopology.TrivialKanFibration: the repaired recorded
  `SSet.Enhanced.trivialKanFibration`, vertex surjectivity and every positive boundary
  lifting property, built from Mathlib boundary and lifting declarations.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and the existing module-category instance.
- Sheaf.CategoryTheory.SimplicialDerivedColimitComputation: `IsResolution`,
  `evaluationComplex`, `derivedColimit`, `Computation`, `ResolutionRoof`,
  `forwardGenerator`, `computation_exists`, and their full field signatures/docstrings.
- Sheaf.CategoryTheory.DerivedColimitBar: `CategoryColimitBarSystem` and its models.
- Sheaf.RingTheory.CotangentLowerShriek: `Algebra.CotangentSites.IsPolynomial`
  and `Presentations`, now attached to their own definition node.
- Sheaf.Paper.TrivialKanHomotopyEquivalence: proof import of
  `SSet.exists_section_homotopy_equivalence`, whose boundary-RLP hypothesis and
  actual section and cylinder homotopy conclusion were read.

Edge cases checked before drafting: E empty (the sole map from A and empty product),
infinite E (finite support in each polynomial, no finite-type hypothesis), zero B
(unique augmentation without a surjectivity requirement on arbitrary presentations),
zero coefficient functor and zero coefficient ring (both sides zero), constant Q
when B is itself polynomial (augmentation identity and ordinary contraction),
non-surjective presentation augmentations, and arbitrary larger coefficient universes.
The singleton map is a concrete constant map, and all variables and universes are explicit.

Searches actually run via msearch.py:

- leanfinder: “polynomial presentation category representable simplicial Hom
  contractible computes derived colimit of module valued functors”: eight hits,
  including freeYoneda, a representation-theoretic universal-cover resolution,
  finite-presentation coyoneda/filtered-colimit lemmas; none states this result.
- loogle: `"derived", "colimit"`: the two pointwise-right-derived `hasColimit`
  lemmas; their source signatures concern Kan extensions, not this computation.
- grep: `derived.*colimit|colimit.*derived|polynomial.*simplicial`: one hit in
  Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived, not this theorem.
- leansearch: “category of polynomial algebras augmented to a ring”: eight hits
  on AlgCat.of, generator rings and ordinary polynomial structures, no category.
- leanfinder: “category polynomial algebras over A with augmentation to B all
  variable sets”: eight hits including MvPolynomial.ACounit, polynomial pushouts,
  CommRingCat.free and formal smoothness, no category definition.
- grep: `Polynomial.*Presentation|Presentations|IsPolynomial` in Mathlib/CategoryTheory:
  nineteen unrelated presentation hits.
- Project rg in both WeilConjectures and Sheaf found CotangentLowerShriek's exact
  category, the bounded-variable CotangentSheaf model (insufficient here), and
  polynomial pair categories (different objects). Search of the exact item id
  found no pre-existing declaration. DAG grep and blueprint_refs search found
  no independent definition node for the unbounded category; blueprint search
  “polynomial presentation” returned only unrelated sk-d-geometry.

Sources opened: cotangent.tex lemma-identify-pi-shriek (08PS) and remark-resolution
(08QI), sites-cohomology.tex lemma-compute-by-cosimplicial-resolution (08Q9),
simplicial.tex definition-trivial-kan (08NL), and the recorded Lean declarations.

## New nodes

`def-trf-polynomial-presentation-category` attaches the existing, exact
`Algebra.CotangentSites.Presentations` and `IsPolynomial` declarations from
Sheaf.RingTheory.CotangentLowerShriek. Source: the polynomial category preceding
Stacks 08PS. Searches above found the helper but no dedicated definition node.
No notion is copied. The item also cites the already landed bar-system definition
and comparison-data definition node, because its signature uses their actual interfaces.
The existing lower-shriek module is downstream in the proof DAG; its category
helpers themselves import no declaration from this delivery. If adding the item
as a proof import there would close a Lean import cycle, that future proof import
must be skipped under stages/2-statements.md §3(7), retaining the exact definitions.

`def-trf-simplicial-derived-colimit-computation-data` attaches the existing
`Computation`, `ResolutionRoof`, resolution predicate, alternating evaluation,
derived colimit, and canonical map definitions in the general computation module.
The node asserts no existence; its source is Stacks 08Q9 with 08PG/08PH/08PD.
Searches found the exact project helper but no independently owned definition node.

## Dependency modules

`def-weil-pbc-trivial-kan-fibration`: the recorded module was absent locally and
`scompile.py --source` reported it unavailable. The dependency module supplies its
exact interface (vertex surjectivity and boundary lifting), not a second notion.
Only its lean record changes. The accepted stage-1 review explicitly retains this
classical combinatorial dependency and explains why it is not dropped machinery.

## Second reading by Q82

Dispatcher assigned a single worker and explicitly prohibited other agents;
this is a separate self-review pass, not a claim of an independent agent review.
I reread the node, all six proof steps, source 08PS/08Q9, the general computation
record, and every new declaration. The category includes all small polynomial
algebras with all compatible arrows, including non-surjective augmentations;
using its existing full subcategory avoids choosing polynomial coordinates of Q.
The coordinate equation fixes the generator-image isomorphism, rather than a
bare Nonempty Iso. Both naturality equations have the right direction. The
normalization field retains the canonical bar roof. The containing-universe
lifts are explicit and do not restrict rings or coefficients. I corrected the
augmentation morphism projection's type annotation, made ULift universe arguments
explicit, and simplified the fibre-coordinate projection after compiler feedback.
The dependency definition has the exact node's surjectivity/boundary conditions.
No statement clause was removed or weakened; no proof is attempted in this stage.

Elaboration repair: the coordinate normalization is stated as an equality of simplicial
maps, using the explicit natural map `elementEvaluation`, avoiding expensive reduction
of the chosen categorical product and pullback at each degree. Its mathematical
content is the same coordinate formula. All compiler probes remain sandbox-only.

`def-trf-simplicial-derived-colimit-computation-data` separately attaches the existing
`Computation`, `ResolutionRoof`, resolution predicate, evaluation complexes, derived
colimit and first-vertex coordinate helpers. It asserts no new existence theorem.
Source 08Q9 specifies the roof, with 08PG/08PH/08PD specifying the bar maps.
The new searches found no Mathlib match; project source and DAG declaration searches
found the exact helper declarations owned by the general computation theorem, but
no definition node. The item's stmt_deps now names this definition; its proof_deps
continues to name the existing theorem that supplies these data.

New-node ownership: `def-trf-simplicial-derived-colimit-computation-data` is named explicitly here and attaches the existing comparison data declarations.

## Delivery gate conflict

The dry run rejected the existing `def-weil-pbc-trivial-kan-fibration` stmt_dep and
its required module as route-pivot dropped machinery. This conflicts with this
item's accepted stage-1 review (2026-10-22), which expressly says this classical
boundary-lifting notion is retained on the Stacks 08QI/08PS route, not the dropped
infinity/dg machinery. The unchanged node statement itself requires it. Removing
it would violate the brief's preserve-statement-dependencies rule and avoid a gate,
so the original dependency and exact compiled statement are retained for correction
of the gate by maintenance. No push was attempted.

## Resumed delivery check (2026-10-23)

The required first action on the saved packet was a fresh `deliver2.py Q82
lem-trf-polynomial-presentation-homology --no-push`. It again failed preflight
with reasons (b) and (c): the original statement dependency
`def-weil-pbc-trivial-kan-fibration` appears in `coord/route-pivot-dropped.txt`,
and the item imports that dependency module. I reread the current upstream
item and its accepted 2026-10-22 review: its maintainer note expressly retains
this exact dependency as the classical boundary-lifting notion on the Stacks
08QI/08PS route. The current item still includes it in both statement and proof
dependencies. Consequently replacing the wrapper with the exact Mathlib match
would not repair reason (b), and removing the dependency would violate the
preserve-accepted-split rule. No gate, launcher script or live source was edited.
The saved packet is retained; no push was attempted.

## Dispatcher retry: fresh dry run (2026-10-23)

Ran the prescribed first dry run on the preserved packet again. `deliver2.py
Q82 lem-trf-polynomial-presentation-homology --no-push` completed with exit 1,
reporting exactly two preflight failures: (b) the item's statement dependencies
name route-pivot-dropped `def-weil-pbc-trivial-kan-fibration`, and (c) the item
imports its `Sheaf.AlgebraicTopology.TrivialKanFibration` module. The current
upstream item still requires that dependency, and its accepted review explicitly
retains it as the classical boundary-lifting notion rather than dropped machinery.
The allowed lean-only dependency repair or replacement by the existing Mathlib
interface cannot clear (b). Removing the accepted statement dependency would
alter the reviewed split to bypass the gate. No scripts, live files or gates
were changed, and nothing was pushed. This retry confirms the same tool refusal;
the packet is preserved for maintenance to resolve the contradictory gate.

## Preserved-packet dry run, retry 4 (2026-10-23 06:46 UTC)

Ran the required first `deliver2.py Q82 lem-trf-polynomial-presentation-homology --no-push` on the saved packet. It exited 1 with the same two concrete preflight failures: (b) the item names route-pivot-dropped `def-weil-pbc-trivial-kan-fibration` in stmt_deps; (c) the item imports its module `Sheaf.AlgebraicTopology.TrivialKanFibration`. Rechecked the current upstream node: its unchanged accepted stmt_deps include that definition, and its passing 2026-10-22 review expressly retains the classical boundary-lifting notion on the Stacks 08QI/08PS route. The dropped-list entry remains at coord/route-pivot-dropped.txt:1343. There is no item repair note. A lean-only dependency repair cannot remove failure (b); removing the accepted dependency would violate the preserved split, and no source-based statement defect justifies a correction. The launcher brief forbids patching or bypassing a wrong gate. No live file or script was changed and no push was attempted. The packet is preserved.

## Preserved-packet dry run, retry 5 (2026-10-23 06:51 UTC)

Ran the prescribed first `deliver2.py Q82 lem-trf-polynomial-presentation-homology
--no-push` on the saved packet. It exited 1 with exactly the same two preflight
failures: (b) `stmt_deps` names route-pivot-dropped
`def-weil-pbc-trivial-kan-fibration`; (c) the item imports its
`Sheaf.AlgebraicTopology.TrivialKanFibration` module. Rechecked the current upstream
node and its passing 2026-10-22 review: the unchanged accepted statement requires
that definition, and the maintainer expressly retains the classical
boundary-lifting notion on the Stacks 08QI/08PS route. The definition remains in
`coord/route-pivot-dropped.txt:1343`; no item repair note is present.

A lean-only repair using the exact Mathlib interface would leave failure (b).
Removing the accepted dependency would violate brief-stage2 §0 and §5; the
source-based statement-correction authorization supplies no reason to remove it.
The launcher brief prohibits patching or working around a wrong gate. Therefore
this is the quoted tool refusal, not a missing mathematical dependency. No live
file or launcher script was modified, and nothing was pushed. Packet retained.

## Resumed provider-interrupted turn (2026-10-23)

Inspected the preserved report before running the required fresh dry run:
`deliver2.py Q82 lem-trf-polynomial-presentation-homology --no-push`.
The process completed (exit 1), not an interrupted or pending delivery.
Preflight reports exactly (b) the unchanged statement dependency
`def-weil-pbc-trivial-kan-fibration` is route-pivot dropped and (c) the item
imports its module `Sheaf.AlgebraicTopology.TrivialKanFibration`.

Rechecked the current read-clone node and its accepted 2026-10-22 review:
the statement and both dependency lists retain this definition, and the review
expressly says this classical boundary-lifting notion is not dropped machinery.
The conflicting entry remains at `coord/route-pivot-dropped.txt:1343`.
No item repair note exists in the current read clone. An exact Mathlib-interface
repair would still leave rejection (b); deleting the accepted dependency is not
an authorized correction of a mathematical statement defect. The brief prohibits
patching or working around this wrong gate. No live source or launcher script
was edited, and nothing was pushed. Saved packet retained.

## Continued interrupted dispatch (2026-10-23 07:24 UTC)

Inspected the saved report and ran the required first dry run. Checked the
interrupted tool session to completion before taking further action: it exited 1
with `PREFLIGHT FAILED, nothing pushed`, reporting exactly reasons (b) and (c).
Reason (b) rejects the unchanged `stmt_deps` entry
`def-weil-pbc-trivial-kan-fibration` as route-pivot dropped; reason (c) rejects its
required `Sheaf.AlgebraicTopology.TrivialKanFibration` import.

Verified the current accepted node's `reviewed.note` (line 207): the maintainer
explicitly retains this classical boundary-lifting notion on the Stacks
08QI/08PS route and says it is not dropped machinery. The same dependency still
appears at `coord/route-pivot-dropped.txt:1343`. No item repair note was found.
A lean-only dependency-interface repair cannot remove rejection (b), while
removing the accepted dependency is forbidden by the stage-2 preserved-split
rule and is unsupported by a source statement defect. The explicit launcher
instruction forbids patching or working around a wrong gate. This remains an
actual contradictory tool refusal, not a missing notion or an unresolved compile.
No live source, gate, or launcher script was edited. No push was repeated or
attempted; the packet is retained unchanged apart from this report entry.

## Preserved-packet dry run (2026-10-23 07:34 UTC)

Inspected the saved report and ran the required fresh `deliver2.py Q82
lem-trf-polynomial-presentation-homology --no-push`. The dry run completed
with exit 1 and `PREFLIGHT FAILED, nothing pushed`. It reports exactly two
reasons: (b) the unchanged statement dependency
`def-weil-pbc-trivial-kan-fibration` is route-pivot dropped; (c) the item's
`Sheaf.AlgebraicTopology.TrivialKanFibration` import belongs to that node.

Rechecked the current upstream item: its accepted split retains this dependency,
and its 2026-10-22 passing `reviewed.note` explicitly identifies it as the
classical boundary-lifting notion retained on the Stacks 08QI/08PS route,
not dropped machinery. The conflicting dropped-list entry remains at
`coord/route-pivot-dropped.txt:1343`; there is no repair note for this item
or the dependency. A lean-only interface repair cannot clear reason (b).
Deleting the accepted dependency would violate brief-stage2 sections 0 and 5;
there is no source statement defect authorizing such a correction. The launcher
brief expressly forbids patching or working around a wrong gate. This is an
actual contradictory tool refusal. No live source, script, or gate was edited;
no push was attempted. The packet is preserved.

## Current dispatch: preserved-packet validation (2026-10-23)

Read the saved report and ran the prescribed first dry run:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q82 lem-trf-polynomial-presentation-homology --no-push`.
It completed with exit 1, `PREFLIGHT FAILED, nothing pushed`, and exactly two
reasons: (b) the item's unchanged stmt_deps names route-pivot-dropped
`def-weil-pbc-trivial-kan-fibration`; (c) the item imports that dependency's
`Sheaf.AlgebraicTopology.TrivialKanFibration` module.

Verified the current accepted node's 2026-10-22 passing reviewed.note: it explicitly
retains this exact classical boundary-lifting notion on the Stacks 08QI/08PS route
and states that it is not dropped infinity/dg machinery. The conflicting entry is
still at coord/route-pivot-dropped.txt:1343. No repair note for the item or dependency
was found. A lean-only interface repair leaves rejection (b); deleting the accepted
statement dependency violates the preserved-split rule, with no source statement
fault justifying a correction. The brief explicitly prohibits patching or working
around a wrong gate. No live source or launcher script was changed, and no push
was attempted. The saved packet remains intact.

## Fresh saved-packet check (2026-10-23 07:54 UTC)

Inspected report.md first and ran the prescribed deliver2.py --no-push.
A second invocation was needed to capture the completed diagnostic after the
first process handle expired. The captured invocation exited 1 with
`PREFLIGHT FAILED, nothing pushed`, with exactly these reasons:

- (b) the item's stmt_deps name route-pivot dropped
  `def-weil-pbc-trivial-kan-fibration`: “state it without them”.
- (c) the item imports its module
  `Sheaf.AlgebraicTopology.TrivialKanFibration`.

Rechecked the current accepted node, its passing 2026-10-22 reviewed.note,
and coord/route-pivot-dropped.txt:1343. The review explicitly retains this
classical boundary-lifting notion on the Stacks 08QI/08PS route and says it
is not dropped machinery. The saved statement is verbatim the current accepted
statement and retains every accepted statement dependency. Neither this item
nor that dependency has a repair note. A lean-only interface repair cannot
clear (b); deleting the accepted dependency has no source-based correction
justification and violates the preserved-split rule. The launcher brief forbids
patching or working around a wrong gate, so this is an actual contradictory
tool refusal. No live source or launcher script was edited. No push was attempted.
The packet is retained.

## Current resumed dry run (2026-10-23)

Read the preserved packet report and ran the required first dry run with
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q82 lem-trf-polynomial-presentation-homology --no-push`.
The completed process exited 1: `PREFLIGHT FAILED, nothing pushed`, with two reasons:
(b) the item's stmt_deps names route-pivot-dropped
`def-weil-pbc-trivial-kan-fibration`; (c) its module imports that dependency's
`Sheaf.AlgebraicTopology.TrivialKanFibration` module.

Rechecked the current upstream node's passing 2026-10-22 review, which expressly
retains this classical boundary-lifting definition on the Stacks 08QI/08PS route,
and the contradictory dropped entry at coord/route-pivot-dropped.txt:1343.
No repair note supplies a changed interface or statement. A lean-only repair
cannot clear (b), and deleting this accepted dependency has no source-based
statement-correction justification. The brief prohibits patching or bypassing a
wrong launcher gate. The packet is preserved; no live source or script was
modified, and no push was attempted.

## Latest dispatcher retry (2026-10-23)

Inspected the preserved packet and ran the required initial `deliver2.py Q82
lem-trf-polynomial-presentation-homology --no-push`. It completed with exit 1,
`PREFLIGHT FAILED, nothing pushed`, rejecting (b) the accepted statement dependency
`def-weil-pbc-trivial-kan-fibration` and (c) its required module import as
route-pivot dropped. The current upstream passing review explicitly retains this
classical boundary-lifting dependency on the Stacks 08QI/08PS route; its statement
and both dependency lists still name it. The conflicting dropped-list entry
remains at coord/route-pivot-dropped.txt:1343. No repair note exists for either id.
A lean-only dependency repair cannot clear (b), and no mathematical statement
fault authorizes removing the accepted dependency. The brief forbids patching or
working around a wrong launcher gate. No live source, launcher script, or gate
was edited; no push was attempted. The saved Lean and node packet is retained.

## Successful resumed validation (2026-10-23)

Read the saved report and ran the prescribed initial dry run. It reported the
historical route-pivot conflict and two new schema diagnostics: both new definition
nodes lacked `import_flags`. Added `import_flags: []` to those two sandbox node
files, as required by the current schema, and reran the prescribed dry run.
It returned `OK (dry run): commit 0d23b92d118 passes the preflight and compiles;
nothing pushed`. The earlier gate conflict no longer occurs; the historical
blocked entries above are superseded by this successful validation. No live source,
launcher script, or gate was edited.

Final self-check retained the saved Lean statement and its full clause mapping.
The item's statement is verbatim the current accepted statement; only `lean` and
allowed additions to `stmt_deps` differ. The existing dependency copy differs only
in `lean`. Both new definition nodes retain their exact existing declarations.
Checked recorded delivered signatures against their files, explicit universe and
variable binding, line widths, the single named postponed theorem, its six-step
proof docstring, and the existing polynomial-category interface (all variable sets,
all compatible algebra maps, no augmentation-surjectivity condition). The passing
dry run verifies preflight and compilation. Proceeding with the required delivery.
