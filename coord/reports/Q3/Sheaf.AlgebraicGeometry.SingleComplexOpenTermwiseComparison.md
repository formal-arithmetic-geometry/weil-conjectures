## What changed

Replaced the sorry in `AlgebraicGeometry.exists_singleComplexOpen_termwise_comparison`
with a reduction through the ordinary tensor comparison, the pinned pullback counit
restriction equation, and categorical cancellation. The existing signature is unchanged.

Reuse `AlgebraicGeometry.openRestriction_isKFlat` for literal termwise open
restriction and `AlgebraicGeometry.SingleComplexBaseChange.counit_isIso_kFlat`
for invertibility of the pinned counit. The second reader removed the duplicate
private proofs after finding these existing declarations.

Added a constructed localized ordinary restriction map, reusing
`openPinnedHomotopyTensorRestrictionIso`. No new object is chosen from mere existence.
Reuse the general `AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoTensorPullback`
from `AffineSpectrumOrdinaryComparisonSquare`, and prove that composing
`comparisonIntoPullback` with the counit recovers it. The affine spectrum square
itself is not used; its definition has no affine hypotheses.
The complex-level counit compatibility is obtained from the existing
`open_pinned_counit_homotopy_restriction` equation.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_singleComplexOpen_termwise_comparison`
(node `lem-pc-single-complex-open-termwise-comparison`).

Added one lower hole:
`AlgebraicGeometry.exists_singleComplexOpen_ordinary_comparison`
(node `lem-pc-single-complex-open-ordinary-comparison`).
It isolates scalar transport and comparison compatibility into the ordinary
termwise tensor pullback, without K-flatness or derived pullback counits.
This is a decomposition: one upper hole closed and one lower hole added,
not a net reduction in the number of holes. The main theorem has no sorry.

The construction `AlgebraicGeometry.singleComplexOpenTensorRestrictionMap`, the
counit cancellation lemma `AlgebraicGeometry.comparisonIntoPullback_comp_counit`,
and `AlgebraicGeometry.singleComplexOpen_termwise_counit_compatibility` are proved.
The existing imported theorem `AlgebraicGeometry.open_pinned_counit_homotopy_restriction`
still has its independently tracked sorry; it is reused, not copied or adapted.

## No longer needed

No original import of the item's module is removed and no whole module is claimed
pruned. The source-transport and pullback-naturality modules remain needed for
public comparison definitions; their fixed-square naturality theorems are not
applied. The new construction module now imports
`SingleComplexBaseChangeStalkCondition` directly instead of the larger
`StalkComparisonPullbackNaturality`; the latter is imported publicly by the new
ordinary-comparison module, where its definition occurs in a theorem signature.
The two existing K-flat helper modules are proof-only imports of the item.

Every original proof dependency removed from the item's direct `proof_deps` is:

- `def-pc-base-derived-tensor-cohomology-model`
- `def-pc-derived-open-restriction-maps`
- `def-pc-single-complex-open-restriction-data`
- `lem-pc-kflat-pullback-preservation`
- `lem-pc-kflat-stalk-criterion`
- `lem-pc-module-pullback-adjunction`
- `lem-pc-open-restriction-stalk-extension-iso`
- `lem-pc-ringed-spaces-derived-pullback-composition`
- `lem-pc-stalk-comparison-pullback-naturality`
- `lem-pc-stalk-comparison-source-transport`

These are direct-dependency removals, not claims that their modules leave the
transitive import closure. Their definitions still occur in the statement or
in the lower lemmas. The K-flat computation now cites
`lem-pc-open-restriction-kflat-model` and `lem-pc-isomorphism-pullback-counit`.

The earlier attempt's unfinished source-existence module has been removed from
the delivery. No existentially chosen comparison map is introduced as a definition.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the original sorry and only proved a helper; that was
not a delivery. The fixed-square naturality theorem cannot directly transport
between different open stalk rings. The new ordinary-comparison node isolates
that missing argument, and the main proof now actually combines it with the
proved representative properties and counit compatibility.

The existing homotopy counit restriction equation already states the derived
compatibility needed here. It is used as a categorical tool from
`sk-thm-picard-f-representable`; the current unit's `realized` record has no
statement or proof-step node bypassed by this use. Its definition module also
provides the ordinary tensor restriction isomorphism, so it is reused rather
than duplicated.

An unrelated module named `SingleComplexOpenCounitCompatibility` landed while
this work was in progress. This delivery instead uses
`SingleComplexOpenTermwiseCounitCompatibility`, and adapts no existing module.

The local literature checkout contains only literature metadata. The cited
Stacks pages 0DJ7, 0DJ9, 0098, 08DW, 08HY, 08FE and 0D5S were read at their official
URLs. The new proof sketch expands the original node's scalar-transport plan;
it adds no base flatness, boundedness or quasi-coherence assumptions.
Empty opens have no point z; top opens, zero complexes and zero stalk rings
satisfy the same naturality and isomorphism identities. No comparison map is
asserted invertible merely because its source and target are transported.

## New nodes

`def-pc-single-complex-open-tensor-restriction-iso`: constructs the localized
ordinary target map from existing homotopy restriction and exact localization
factors, with no new choice or sorry.

`lem-pc-single-complex-open-counit-compatibility`: the representative-level
counit square, before stalks and cohomology; proved by specialization and
cancellation from the existing homotopy equation.

`lem-pc-single-complex-open-ordinary-comparison`: the remaining scalar transport
square into ordinary tensor pullback, with its source, full proof in words,
edge-case checks, and recorded Mathlib searches. LeanSearch was unavailable;
LeanFinder, Loogle and grep returned constituent lemmas but no exact match.

No change record is needed: no existing interface is changed and no module held
by another group is adapted.


## Second reading by Q3

1. Compared all four delivered modules with the repository. Three are new; the
   sole existing declaration is `exists_singleComplexOpen_termwise_comparison`.
   Its complete signature is byte-for-byte unchanged. Original public imports
   are unchanged. No existing definition, target, or other group's module is
   adapted. Read the landed restriction-data and affine representative change
   records; this delivery uses their current interfaces. Verdict: pass.

2. Read every proof and construction, scanned all delivered sources for forbidden
   declarations and holes, and compiled each through `lcompile.py`. The only
   new sorry is the named ordinary-comparison theorem listed above. Explicit
   `#print axioms` checks in a scratch copy show only `propext`, `Classical.choice`,
   and `Quot.sound` for the constructed restriction map, counit cancellation,
   and reused ordinary comparison definition. The main theorem, termwise counit
   compatibility, and ordinary-comparison hole additionally use `sorryAx`, as
   expected from the named remaining dependencies. No data is chosen from a new
   existence theorem; beta is a concrete composite. Verdict: pass as a
   decomposition, not a completed axiom-free proof.

3. Checked the new ordinary-comparison statement against the construction of
   the four stalk rings, universal derived tensor counit, tensor-algebra action,
   tensor-stalk map, and exact restriction factors. It is the scalar-transport
   part of the argument before any derived pullback counit is inverted, and
   applies to arbitrary complexes. Empty opens have no z; top opens give the
   canonical ring identifications; zero complexes and zero rings introduce no
   nonzero or invertibility assumption. Its docstring supplies the full
   natural-language argument and its node records the source and dependencies.
   Independent LeanFinder, Loogle, Mathlib grep, and searches in both local
   source roots found constituent tools but no existing general open square.
   They did find an identical ordinary comparison definition, now reused.
   The affine spectrum square has different coordinate hypotheses, and the
   fixed-square naturality theorem does not compare different stalk rings.
   Verdict: true and strictly part of the original proof; one lower hole remains.

4. Read the proof from the main theorem down. Replaced the two duplicate private
   K-flat/counit proofs with existing proved declarations, and removed the
   duplicate ordinary comparison definition. The remaining cancellation is
   elementary; derived restriction compatibility is reused from the existing
   homotopy equation. Checked import visibility: every added import of the item
   is proof-only, and every public import of a new module supplies a definition
   or a symbol in its public signatures. Enumerated all ten old direct proof
   dependencies removed, with no claim of whole-module pruning. The
   `sk-thm-picard-semicon` realized arrays are empty; no realized unit statement
   or step is bypassed. The homotopy equation is used as a generic categorical
   tool, and only the general definition from the affine spectrum module is
   used. Verdict: pass.

5. Checked each node against the actual Lean declarations, statement and proof.
   Every proof_deps list equals the union of its proof-step uses; every referenced
   node exists. New nodes carry source, search records, origin, creation,
   blueprint, unit/chapter and Lean records. Updated the main route to cite the
   two reused helper nodes, and removed the deleted duplicate declaration from
   the ordinary node's declaration list. Verdict: pass.

Second-reading changes: reused the ordinary comparison definition and both
K-flat helper theorems; narrowed the new restriction construction's import;
supplied explicit local additive/zero-morphism instances to avoid a typeclass
search timeout; updated node routes/searches and completed the pruning report.
The final main proof and explicit axiom scratch compiled without warnings.
