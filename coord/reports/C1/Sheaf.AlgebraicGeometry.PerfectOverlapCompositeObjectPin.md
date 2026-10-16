## What changed

Replaced the original hole in `AlgebraicGeometry.perfect_overlap_composite_object_pin`
by a complete categorical pasting proof, preserving its entire signature. It uses
separate site and projection component statements on each Boolean branch.

Constructed `perfectOverlapNestedPullbackSquare` explicitly and proved its
restricted-map equality. The existing `compositionTo` and
`compositionTo_triangle` supply named-composite associativity; the second
reader removed the duplicate local API.

Constructed `perfectOverlapCompositeStageMapAt` from the mapped site counit,
nested-square inverse, restricted local composition comparison, and stage-object
comparison. `perfectOverlapCompositeStageMap` selects its two branches, with
proved branch formulas. These are real constructions, with no new existence
choice and no hole in their data. Both components refer to this common map.
Keeping its Boolean wrapper unexposed prevents the final proof from repeatedly
expanding the transport diagram while checking dependent object types.

Only the item module existed in the repository. No existing definition,
statement, visibility, target signature, or tool was changed.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.perfect_overlap_composite_object_pin`.

Added exactly two holes, so this is a decomposition, not a net proof of the
remaining target closure:

- `AlgebraicGeometry.perfectOverlapCompositeSiteComponent`
  (`lem-pc-perfect-overlap-composite-site-component`). It still needs the
  nested-restriction coherence calculation, gamma identification by localization,
  and the final site-triangle/counit pasting. Its statement has no second
  cartesian square, base-change comparison, eta, or projection equation.
- `AlgebraicGeometry.perfectOverlapProjectionCompositionComponent`
  (`lem-pc-perfect-overlap-projection-composition-component`). It still needs the
  six-face pullback-composition prism, followed by the site counit and the
  existing natural-comparison component formula. Its equation has no psi,
  theta, or gamma. The local identifications enter its common source interface;
  they are not extra hypotheses on the projection calculation.

Each residual theorem has its complete proof in words in its docstring and
node. Neither is the original pin under a new name. The original proof combines
both equations by associativity and transitivity, rather than invoking a
single restatement. No private theorem or definition contains a hole.

Also proved, without new holes:
`perfectOverlapNestedRestrictedMaps`, `perfectOverlapCompositeStageMap_false`,
and `perfectOverlapCompositeStageMap_true`. The constructions themselves are
`perfectOverlapNestedPullbackSquare`,
`perfectOverlapCompositeStageMapAt`, and `perfectOverlapCompositeStageMap`.

All statements allow empty, equal and total opens and unbounded derived objects.
No boundedness, cover, nonemptiness or perfection hypothesis was added.

Validation: individual module checks and the isolated full reduction compiled.
All five delivered modules compile together cleanly. The required
`deliver3.py --no-push` check printed OK: compilation, declaration checks and
preflight pass, except for the second reading explicitly reserved for the next
worker. No delivery was pushed. The final check repeats this validation after
clarifying the residual proof outlines and recording the experiments.

## No longer needed

Removed these direct proof imports from the item:
`DerivedOpenRestrictionIsoDescent`, `DerivedOpenRestrictionLocalization`,
`DerivedPullbackComposition`, `PerfectOverlapStageEquivalence`, and
`TwoOpenComparisonDiagram`. Their necessary APIs remain available through the
actual component dependencies; this is not a claim that their entire modules
leave the target import closure. No existing library module is withdrawn.

The old direct proof-dependency edges removed from the item node are
`def-pc-perfect-overlap-stage-equivalence`,
`def-pc-two-open-comparison-diagram`,
`lem-pc-derived-open-restriction-is-localization`,
`lem-pc-ringed-spaces-derived-pullback-composition`, and
`lem-sc-derived-open-restriction-iso-descent`. These remain indirect
dependencies of the residual arguments; no whole module is pruned from the
target closure.

The item's proof no longer performs its own global-object lift. Essential
surjectivity is needed only in the site component's gamma argument. Unused
coherence experiments and the inherited override of `PerfectOverlapStageEquivalence`
are excluded from the delivery. The library's current comparison normalization
is used unchanged.

## Where the brief, the DAG or earlier work was wrong

The inherited attempt did not provide a compiling top-level reduction.
Directly combining its expanded component formulas repeatedly unfolded
transport-diagram fields and inverse-image intersections during dependent type
checking. A constructed common stage map fixes that interface problem; the
verified top-level proof now uses only the named map and the supplied opaque
isomorphism parameters. The site's two branches are independent of the second
cartesian square, so those extra parameters are absent there.

No mathematical statement is disputed. The remaining computations are true
coherence identities, not missing geometric hypotheses. The DAG now records
these actual components and the explicit common map. No blueprint unit statement
or realized proof step is bypassed. Continuing proof experiments are preserved
in the sandbox scratchpad for the second reader, including the concrete
nested-square, site and projection pasting arguments; none is substituted for
a compiled delivered proof. In particular,
`scratchpad/sitework/lean/Sheaf/AlgebraicGeometry/SiteApexProjectionReductionProbe.lean`
contains the generic gamma-localization and counit pasting arguments; with a
one-million-heartbeat scoped budget its first branch reports no error, but the
second branch exhausts that budget. The two-million-heartbeat experiment exceeds
60 seconds and is not delivered. Projection prototypes and command profiles are
in `scratchpad/fallback/lean/Sheaf/AlgebraicGeometry/` and
`scratchpad/projection-command-profile.log`. The profile identifies repeated
comparison of scheme presentations of inverse-image intersections and expensive
private-module linting. These experiments need an improved API for those
constructed functor objects; increasing the compile limit or moving a proof to
another file is not the proposed remedy.

## New nodes

`lem-pc-perfect-overlap-nested-pullback-square` records the restricted square,
and its constructed comparison. Named-composite associativity reuses the
existing `compositionTo_triangle` API.

`def-pc-perfect-overlap-composite-stage-map` records the four-factor local map,
its Boolean wrapper and the two proved branch formulas. The wrapper's source
is exactly the transported diagram object used by the original statement.

`lem-pc-perfect-overlap-composite-site-component` records the first residual
identity, with gamma localization and the canonical site triangle as its proof.

`lem-pc-perfect-overlap-projection-composition-component` records the second
residual identity, with the cartesian prism, site counit and eta component formula.

`lem-pc-perfect-overlap-canonical-site-triangle` attaches the existing, proved
`PerfectOverlapCanonicalSiteTriangle` U/V API to the DAG. Its source module is
used unchanged and is not copied into this delivery.

`def-pc-perfect-overlap-core-comparisons-api` attaches the existing proved
comparison API in `PerfectOverlapObjectRealizationCoreComparisons`.
This records the helper constructions rather than the parent realization
theorem, which would create a DAG cycle. Its Lean module is unchanged.

`def-pc-perfect-overlap-composite-transport-api` attaches the existing proved
composite-transport API in `PerfectOverlapObjectRealizationCoreTransport`.
Its explicit diagram, kappa, theta and site constructions supply the common
interface. Its Lean module is unchanged.

All new nodes have sources, complete proof plans, actual search
records and Lean attachments. LeanSearch returned Internal Server Error and is
recorded as unavailable; LeanFinder, Loogle and grep searches returned actual results. The change record
`coord/changes/perfect-overlap-composite-object-pin-local-settings.md` describes
the original module's added local elaboration settings; every existing declaration signature and visibility stays identical.

## Earlier second reading (a previous round; superseded)

1. **Statements and accidental changes.** I diffed the delivered item against
the repository version and checked every existing declaration signature. The
target statement is byte-for-byte unchanged; only proof imports, local
elaboration settings, and the proof body differ. The four auxiliary modules
are new modules and their declarations match their DAG attachments. Verdict:
pass.

2. **Proof and axioms.** I compiled all five delivered modules together with
`lcompile.py --all`. The target has no `sorry`; the only remaining `sorry`s are
the two named component theorems listed above, each with a public declaration,
docstring proof outline, and matching node. No definition contains a hole and
no forbidden declaration occurs. Verdict: pass for the proved target and
documented split statements.

3. **New statements.** I checked the two split component statements and the
constructed nested-square and stage-map interfaces against their uses. The
components are strict reductions of the target (site equation and projection
equation separately), not restatements of the target; the constructions contain
real data rather than arbitrary witnesses. Search records and node attachments
are present, and no duplicate upstream declaration was found. Verdict: pass.

4. **Pruning and route.** The top-level proof uses the named site and projection
components and the elementary pasting lemma. The five direct imports removed
from the old proof are no longer referenced by this module; the node records
the reduced proof dependencies. The unit route remains represented by the
existing transport and comparison APIs. Verdict: pass.

5. **DAG and report consistency.** I checked each changed node's `proof`,
`proof_deps`, `proof_origin`, Lean attachment, source, chapter, and unit against
the delivered declarations. The report lists the closed target, the two holes
left, removed imports, and all newly added nodes. Verdict: pass.

I changed only this report section during second reading; no Lean statement or
proof was altered after the successful compilation.



## Second reading by C1

1. **No accidental interface changes — pass.** Read all five delivered modules
and diffed the only pre-existing module against the shared repository. Compared
the raw text from `theorem perfect_overlap_composite_object_pin` through the
end of its type: it is byte-for-byte identical. The declaration parser also
reports no changed statement, removed declaration, or changed public import.
The local attribute block is documented in the existing change record; it does
not change any imported definition. The other four modules are new. None of
the unchanged comparison/transport modules attached to new nodes is delivered.

2. **Proofs, constructions and axioms — pass as a decomposition.** Recompiled
all five modules together through `lcompile.py --all`: no errors or warnings,
with individual compilation times 5.4, 30.5, 39.1, 22.6 and 40.2 seconds.
The original theorem rewrites the supplied rho equality and pastes the site
and projection equations separately on each Boolean branch. Its private
pasting lemma is proved by associativity. The only two textual holes are the
public component theorems named under `Proved and sorry left`; both have
source/proof docstrings and matching nodes. A scratch `#print axioms` check
of all nine public delivered declarations reports only `propext`,
`Classical.choice`, and `Quot.sound` for the six construction/branch declarations;
the two components and original theorem additionally report `sorryAx`.
No forbidden declaration or hole in a definition occurs. Thus one original
hole closes and two holes are added: net minus one, not a completed proof of
the original theorem's import closure.

3. **Residual statements and searches — pass.** Checked the directions of
all four factors of `perfectOverlapCompositeStageMapAt`: mapped site counit,
nested-square inverse, restricted local-composite map, then stage-object map.
The nested square is constructed by whiskering the pinned inclusion
comparisons and composing pullback comparisons across the proved equality of
restricted scheme maps. There is no new witness chosen from existence.
The site statement removes the entire second cartesian presentation, hmap,
projection comparison and eta; its remaining phi dependence cancels by the
canonical site triangle. The projection statement contains none of psi, rho,
theta or gamma; hmap supplies precisely its middle commuting face. The
constructor equalities retain the original sigma/eta/chi interface. Neither
statement is the original equation under another name. The docstrings give
the localization/naturality argument and the six prism triples, respectively.
Empty overlap, either empty open, equal opens, total opens and zero objects
require no cancellation of a noninvertible map: the arguments use open
immersions, natural isomorphisms, essential surjectivity and invertible
composition comparisons, and impose no boundedness assumption.

Repeated searches with different terms through msearch LeanFinder (pullback
pseudofunctor coherence and commuting squares), Loogle (`NatTrans.naturality`),
and grep, and read the project matches `PerfectOverlapNestedOpenSquarePasting`,
`PerfectOverlapCanonicalGammaLocal`, `PerfectOverlapCanonicalOpenPrismU`,
`PerfectOverlapSquarePrismAbstract`, `PerfectOverlapTransportPrismHom` and
`PerfectOverlapProjectionPrism`. These provide partial cube/prism and first-open
identities; none states either full residual component or the constructed
nested exact-restriction isomorphism. The existing `compositionTo_triangle`
and site-triangle API are already retained by the residual proof plans. Closing
either residual requires further pasting and, for the site equation, both
branches; neither is an immediate application missed by the worker.

4. **Top-down reduction, imports and route — pass.** The original theorem
uses only the two components and elementary pasting. Checked all five old
proof-dependency edges against `No longer needed`: every removed edge and
its direct import are listed. They remain indirect dependencies, so no whole
module is claimed pruned. Public imports of the new definitions are needed
by signatures or exposed construction bodies. In particular, testing a plain
import of `PerfectOverlapStageEquivalence` in the nested-square module made
the exposed body unable to refer to its inclusion comparison; restored the
original public import. No Lean change from that test remains. The unit
`sk-thm-picard-semicon` is unchanged (its existing realized lists are empty);
this delivery neither fills that earlier bookkeeping gap nor bypasses any
recorded realized step. It keeps the restriction, localization and fixed
composition argument below the unit level.

5. **DAG agreement — pass.** Checked all eight supplied node files against
their modules, including the three attachments to unchanged existing APIs.
Every primary Lean declaration exists and each stored statement matches the
normalized declaration text. The existing item node changes only `proof`,
`proof_deps` and `proof_origin`; its two new edges are exactly the two theorem
applications in the proof. New-node proof dependencies equal the union of
the steps' uses, and the nodes carry sources, search records, origin,
creation/item/group, blueprint ancestry, chapter/unit and Lean attachments.
The residual nodes describe the actual common-map factorization rather than
an arbitrary comparison isomorphism. No definition or target statement is
changed, and there is no forced adaptation.

Second-reading changes: added this independent review and its explicit axiom,
search, edge-case and net-hole accounting. The tested import edit was reverted;
all delivered Lean and DAG content remains as read. Axiom scratch commands
are retained under `scratchpad/second-reading/` and excluded from delivery.
