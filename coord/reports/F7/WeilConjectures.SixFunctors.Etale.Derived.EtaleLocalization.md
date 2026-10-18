## What changed

Replaced the hole in
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
by a compiling composition of adjunctions, with its original signature. Constructed a
compactification of the etale map from the graph in a proper base change of a
compactification of its composite; this avoids adding quasi-compactness assumptions
on either of the other maps. Used the existing source-library compact-support
composition theorem and exact derived etale sum-extension adjunction.

Added four helper modules. `EtaleCompactificationGraphMap` constructs the actual
clopen-graph projection and its transpose using adjunction units and canonical
comparisons. `EtaleCompactificationAcyclic` proves acyclicity for open extension in
any etale compactification by proper base change to geometric fibres, the finiteness
of their etale maps, and exactness of finite direct image. `EtaleCompactSupportComparisonGeneral`
proves the passage from the sheaf comparison to all unbounded complexes: K-injective
comparison, acyclic terms, pointwise finite cohomological dimension, and uniqueness
of the derived functor. `EtaleCompactificationGraphIso` states the remaining
invertibility of the constructed sheaf graph map.

The original public imports are preserved. All new imports in the item are private
proof imports. No existing definition, signature, target, or visibility changed.

## Proved and sorry left

Original item: one hole; now zero. Closed/reduced the declaration
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`.
The already-proved isomorphism-descent theorem is unchanged.

New proved declarations:

- `AlgebraicGeometry.Etale.etaleCompactification_acyclic`
  (`lem-f7-etale-compactification-acyclic`): full Lean proof from proper base change,
  exact inverse image, finiteness over the Artinian geometric-point base, clopen
  direct-image comparison, and exactness of finite direct image.
- `AlgebraicGeometry.Etale.nonempty_iso_etale_compactSupport_general`
  (`lem-f7-etale-compact-support-comparison-general`): full Lean proof from acyclicity
  and invertibility of the underived graph comparison.
- `AlgebraicGeometry.Etale.etaleCompactificationGraphMap`
  (`def-f7-etale-compactification-graph-map`): a real construction with no data hole
  and no choice of an arbitrary witness from a mere existence theorem.

Exactly one new hole remains:

- `AlgebraicGeometry.Etale.isIso_etaleCompactificationGraphMap`
  (`lem-f7-etale-compactification-graph-iso`). It needs the graph projection's
  compatibility with proper degree-zero base change and the finite geometric-fibre
  sum-to-product calculation. Its complete argument and edge cases are in its
  docstring and node. The map itself and the independent acyclicity argument are
  already implemented. The existing
  `openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap` and
  `unit_map_openImmersionLowerShriekBaseChangeMap_app` supply the open-extension
  part of the remaining compatibility; these are recorded in its proof plan.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes
closed by this delivery. A separate compiled check proves the graph map is invertible
for the standard compactifications of an identity morphism and, more generally,
of every open immersion, over every commutative ring. These temporary checks are not
delivery modules.
The new lower statement concerns ordinary sheaves and the
explicit map only; it contains no exceptional inverse image, arbitrary f or h, or
unbounded derived comparison. Existing named dependencies with sorry are reused as
intended by stage 3. Compiled all five sandbox Lean files with lcompile.py.
`#print axioms` for the graph-map construction reports only `propext`,
`Classical.choice` and `Quot.sound`. The acyclicity theorem additionally reports
`sorryAx` through existing proof dependencies; it is a completed proof from the
project declarations, not a claim that all of those declarations are now discharged.

## No longer needed

No original public import was removed. The proof does not import
`Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`, whose statement is restricted
to Noetherian schemes and includes stronger normalization assertions. The final
acyclicity proof also removes the exploratory import
`Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`; finite direct image on
geometric fibres replaces that entire input. No theorem in this new proof branch
uses its normalized-comparison package. This also removes
`lem-asd-etale-compact-support-normalization` from the acyclicity node's proof_deps.
The new graph-isomorphism node does not need
`lem-sfb-etale-geometric-fibre-compact-sections`: the Mathlib finite-over-Artinian-base
lemma and the existing finite-etale comparison suffice for its fibre computation.

The proof also avoids
`WeilConjectures.SixFunctors.Etale.Derived.Composition`, whose chosen upper-shriek
composition API imposes quasi-compactness of the composite. Instead it applies the
already-proved lower-shriek composition and right-adjoint uniqueness directly.

The following parts of the locality node's planned proof are not needed directly
for this existence statement: cofilteredness
`lem-cbc-compactifiable-cofiltered`, compatible towers
`lem-cbc-compactifiable-compatible-tower`, and the explicit refinement and coherence
work in `lem-amb-unbounded-proper-open-interchange` and
`lem-cbc-extension-zero-composition`. The existing source compact-support composition
theorem supplies the required composition comparison;
these tools may still be dependencies of that theorem or other project items, so
this delivery does not claim to remove them globally. Derived direct-image composition
(`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`) remains needed in the
acyclicity proof and is not pruned. No module is withdrawn.

Pruned exploratory helper `EtaleCompactificationSheafModel` before delivery: its
acyclicity clause is proved in `EtaleCompactificationAcyclic`, and its existence-only
sheaf comparison is replaced by the explicit graph map and its invertibility theorem.
It was never a repository module and is not part of the delivery. Removed redundant
proof imports from the helper modules after compilation. In particular the general
comparison imports `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`
instead of `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.

## Where the brief, the DAG or earlier work was wrong

No DAG node's lean.module attached to the item module when work began. The docstring
references `lem-amb-etale-adjoint-locality`, but that node's attached declaration is
`AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso` in a different
Sheaf module. Its compact-support comparison assumes Noetherian schemes, whereas
the assigned existing theorem has arbitrary schemes. Its direct application would
silently add hypotheses. Added a node for the actual general source-library locality
theorem, preserving its statement.

The node `lem-sfb-etale-geometric-fibre-compact-sections` has a Lean attachment,
but its recorded file is absent from this checkout. This delivery does not duplicate
it or depend on it: existing finite-etale direct-image results supply the fibre
calculation instead.

The item's docstring also said that etale extension by zero was unavailable. The
library now has `etaleLowerShriek`, its exactness and both the sheaf and derived
adjunctions. Updated this explanation and used those existing constructions.

The acyclicity proof's first elaboration timed out while inferring a long isomorphism
chain. Explicit intermediate isomorphisms and a single integer degree fixed this;
no compile or heartbeat limit was raised and no definition was weakened.

## New nodes

`def-f7-etale-compactification-graph-map`: the explicit clopen-graph map, in its own
new module; constructed, with all choices fixed by existing adjunctions.

`lem-f7-etale-compactification-graph-iso`: the single remaining sheaf-level obligation,
with no Noetherian hypothesis. The empty fibre gives the zero-to-zero isomorphism;
nonempty fibres give the finite sum-to-product isomorphism. Identity maps and proper
etale maps give the expected identity and finite sum/evaluation comparisons.

`lem-f7-etale-compactification-acyclic`: the proved acyclicity statement. Its proof
uses no Noetherian normalization. The geometric fibre map is finite by Mathlib's
`IsFinite.of_locallyQuasiFinite`, and its ordinary direct image is exact.

`lem-f7-etale-compact-support-comparison-general`: the proved unbounded comparison
from the two sheaf-level ingredients, with pointwise rather than globally uniform
cohomological bounds.

`lem-f7-etale-adjoint-locality-general`: attaches the assigned source-library
statement and records its actual graph-compactification/adjunction proof route.

`lem-f7-proper-pointwise-cohomological-bound` and
`lem-f7-compact-support-composition-general`: attach existing proved source-library
tools in their actual arbitrary-scheme generality. No new Lean files or holes for
these two attachments.

Mathlib searches were run through msearch.py: LeanSearch, LeanFinder, Loogle and
grep. The generic adjoint-uniqueness tools were reused; searches did not supply an
etale compact-support comparison. Blueprint and DAG searches found the existing
Noetherian normalization and locality nodes; their more restrictive scope is why
these general helper nodes are distinct. A subsequent direct Mathlib search found
`IsFinite.of_locallyQuasiFinite` and removed the normalization input completely. Generic tools from other units are
listed
in split_report.tool_uses on the nodes. No change record is needed because every
existing mathematical interface is preserved.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
