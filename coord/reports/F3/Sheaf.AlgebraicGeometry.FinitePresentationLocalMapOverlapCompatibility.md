## What changed

Reduced `AlgebraicGeometry.finitePresentation_local_maps_eventually_compatible`
to two strictly smaller statements: eventual descent of the prescribed local
family, and functorial transport of its recovery equation. The upper proof applies
the overlap statement to the recovered map
`e₀.inv.app Fj ≫ φ ≫ e₀.hom.app Gj`, and takes its arbitrary global composition
maps to be `z.hom.app Fj` and `z.inv.app Gj`. The recovery statement is applied to
four schemes and six maps. The four triangles follow from base-change composition,
Spec functoriality and cone naturality. The proof combines the affine cover,
descent morphism and recovery equation.

Two concrete definitions share the formulas:
`AlgebraicGeometry.localMapPullbackFamily` is the original five-map composite,
and `AlgebraicGeometry.localMapRecovery` is the original recovery equation on
every member of the pulled-back cover. Neither definition contains sorry or
chooses witnesses. The definition boundaries fix the earlier kernel timeout:
the upper module now compiles in about 11 seconds, within the unchanged
60-second limit. The original mathematical statement is preserved, including
the prescribed family and all canonical comparisons. The unused lets are
prefixed with underscores; their order is retained for the existing caller.
No Challenge target changes. The interface refactoring and its users are
recorded in `coord/changes/finitePresentation-local-family.md`.

The delivery contains five Lean modules: the upper module, two split theorem
modules and two definition modules. The sole direct caller,
`Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum`, compiles unchanged
against the sandbox. No forced adaptation is needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.finitePresentation_local_maps_eventually_compatible`
(node `lem-pc-fp-local-map-overlap-compatibility`).
Its proof contains no sorry and combines the two smaller obligations in Lean.

Two added holes remain, each exactly `:= by sorry` in a public named theorem,
with its node, source and complete natural-language proof:

- `AlgebraicGeometry.finitePresentation_local_maps_eventual_overlap_equations`
  (node `lem-pc-fp-local-map-overlap-equations`).
- `AlgebraicGeometry.finitePresentation_local_maps_recovery_transport`
  (node `lem-pc-fp-local-map-recovery-transport`).

This is a decomposition: one upper hole closed and two lower holes added.
It is not a complete mathematical proof or a positive net sorry reduction.
Both new definitions have concrete bodies and no proof holes.
The private `map_stage` helper is proved.

All five modules compile locally. The unchanged direct caller also compiles.
The scratch FormulaCheck compiles three reflexivity checks: the exact recovery
equation, the exact five-map family, and equality of descent components with
ordinary restrictions. `deliver3.py F3
Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility --no-push`
printed OK: compilation and preflight pass, with only the independent second
reading left to the next worker. No axiom-probe timeout was reported. Nothing pushed.

## No longer needed

Removed the upper module's direct proof import
`Sheaf.Algebra.FinitePresentationColimit`. Its node
`lem-pc-fp-module-map-descent-affine` is no longer a direct proof dependency.
The overlap obligation uses the existing scheme-level
`lem-pc-fp-zero-map-descent` /
`Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent`, which accepts directed
preorders. The algebra colimit module may remain needed transitively; no global
pruning of it is claimed.

Removed the unnecessary `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`
import from the new family-definition module: its signature states ordinary
restriction explicitly. Other modules still need the modules pseudofunctor,
so this is not a claim that PullbackUnit leaves the targets' import closure.

The recovery module needs no ring diagram, finite presentation, Noetherian rings,
affine cover or descent existence. The overlap module needs no tensor composition
isomorphism: its global precomposition and postcomposition maps are arbitrary.
No other existing node or module is claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The affine algebra descent declaration alone does not state the scheme-level
overlap argument or the canonical-comparison coherence calculation. These are
the two separate lower obligations. The affine declaration assumes a partial
order; the existing scheme-level zero-map descent accepts directed preorders.

The earlier sandbox report included an obsolete second reading and conflicting
claims that the final dry run passed despite a kernel timeout. That review is
removed because it predates this repair. The timeout was reproduced, including
after ordinary elaboration completed. Factoring the repeated recovery equation
into a concrete predicate fixes it without increasing the time limit or splitting
the upper proof for performance.

Searches are retained in searches.jsonl. LeanSearch was unavailable; LeanFinder,
Loogle and local source searches were used. A fresh search found
`Sheaf.AlgebraicGeometry.OpenCoverMapLiftTransport`: its conclusion is existence
of some recovering chart map at a later stage. It does not identify that map with
the prescribed five-map family, so it cannot replace the recovery obligation.
The blueprint search for "local recovery" found no matching node. The ancestor
helper cannot follow the newer module-name created.item records; the new node
retains the explicit ancestor and route used by the existing item.

The source pages [01ZR](https://stacks.math.columbia.edu/tag/01ZR),
[0095](https://stacks.math.columbia.edu/tag/0095), and
[0096](https://stacks.math.columbia.edu/tag/0096) were read.
01ZR's first proof explicitly omits the Zariski gluing details; these are expanded
in the lower obligations. The recovery proof plan is marked non-elementary and
names the adjunction and canonical comparison nodes it uses.

## New nodes

`lem-pc-fp-local-map-overlap-equations` states eventual descent of the fixed local
family recovering one global map, with an affine pulled-back cover and naturality
under two arbitrary global maps. Its proof takes pairwise defects, uses
scheme-level zero-map descent on each quasi-compact intersection, chooses a finite
common upper bound, constructs the descent morphism and composes it with the two
global maps. Empty covers, empty intersections, zero modules and identity
transitions impose no additional requirements.

`lem-pc-fp-local-map-recovery-transport` states a comparison calculation for four
schemes and six maps satisfying four triangles. It has no finite-stage,
finite-presentation or descent assertion. Canonicality of the three supplied
comparisons is explicit. Its proof uses functoriality, coherence of mates of
pushforward composition and adjunction triangle identities. It applies to
arbitrary covers, zero maps and identity factorizations.

`def-pc-local-map-pullback-family` records the explicit five-map construction.
It chooses no local map, module or comparison. Its ordinary-restriction signature
is definitionally the earlier descent-component signature.

`def-pc-local-map-recovery` records the explicit recovery equality as a predicate.
Unfolding it gives exactly the old equality on each pulled-back cover member.
For an empty cover it is vacuous; zero maps give zero on both sides; identity
factorizations obey the same canonical comparisons. It creates no proof hole.

Change record: `coord/changes/finitePresentation-local-family.md`.

## Second reading by F3

1. I compared the delivered upper module with the repository version. The
   theorem's binders, hypotheses, conclusion, universes, and visibility retain
   the original mathematical content; repeated formulas are named by concrete
   definitions, and unused local lets are only renamed with an underscore.
   The change record documents this interface refactoring. Verdict: unchanged
   statement in substance, with the declared change record.

2. I compiled all five delivered modules individually with `lcompile.py`.
   There are no forbidden declarations and no `sorry` in a definition. The
   only remaining holes are the two named split theorems, each public, named,
   documented, and represented by a DAG node. The upper theorem is proved.
   Verdict: proof checks pass with the documented split obligations.

3. I inspected the two split statements and their nodes. The overlap statement
   is the strictly smaller eventual descent and component construction needed
   by the upper theorem; the transport statement is the independent coherence
   calculation. Both retain all necessary hypotheses, have source and proof
   descriptions, and are not restatements of the upper item. The two concrete
   definitions contain no chosen witnesses or hollow data. Verdict: split
   statements are true as stated and exactly the required reductions.

4. I checked the proof route and imports against the DAG. The upper proof uses
   the overlap and transport nodes and the two concrete definitions; the old
   direct algebra-colimit import is no longer used. The unit's route remains
   represented by the realized upper node and its split dependencies. Imports
   needed by public signatures remain public, while proof-only theorem modules
   are plain imports. Verdict: dependencies and pruning records agree with the
   Lean proof.

5. I checked the definitions and edge cases in their docstrings and scratch
   formula checks: unfolding gives the former five-map family and recovery
   equality, including empty covers, zero maps, and identity transitions. The
   unchanged direct caller compiles against the sandbox. No target statement is
   altered. Verdict: definitions and downstream compatibility are sound.

I changed only this report section during second reading; no Lean proof or node
content required repair.
