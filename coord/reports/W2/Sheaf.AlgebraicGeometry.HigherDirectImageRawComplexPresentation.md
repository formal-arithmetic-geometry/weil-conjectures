## What changed

Proved `AlgebraicGeometry.Etale.nonempty_higherDirectImageRaw_complex_presentation`
from two independent intermediate statements: natural comparison of raw module
cohomology with restricted abelian cohomology, and construction of the geometric
complex data for restricted abelian coefficients. The final proof supplies both
comparison squares by simplifying the fixed raw diagram and cocone and applying
naturality to their actual stage arrows and cone projections. It uses no continuity
theorem to produce the presentation.

Added `RawModuleRestrictedAbelianNaturalIso.lean`,
`RestrictedOverAbelianComplexData.lean`, and
`EtaleComplexCohomologyPresentationData.lean`. The first two each contain one named
intermediate theorem. The last is an equivalent one-constructor representation of
the existing existential presentation, necessary to bring the full file below the
60-second compile limit. All 24 witnesses, all equations, and the final True binder
are preserved literally. No existing declaration signature or visibility changes. The second reader also
removed redundant direct public imports of LowerShriek and UpperLowerStar.Coherence;
the presentation-data module publicly imports both, preserving their availability.
The existing `EtaleComplexCohomologyPresentation.isColimit` proof eliminates the new
constructor and passes its witnesses explicitly to the same continuity theorem.

The four delivered modules compile locally without warnings. The original
`AbelianRawCoconeComplexPresentation` and `RestrictedAffineComplexSystemNatural`
are checked unchanged against the new predicate. No forced adaptation is delivered.
The change record is `coord/changes/EtaleComplexCohomologyPresentation.md`.

Repair of reviewer X-4596e H4: changed only the presentation declaration prefix
from `def` to `abbrev`, with its binders and body unchanged; made the identical
prefix correction in the definition node's `lean.statement` and in the change
record's `## New` section, retaining `## Old` verbatim. Corrected the requested
second-reading sentence. Recompiled all four delivered modules without errors or
warnings (the item took 49.5 seconds). Recompiled unchanged copies of all three
direct importers against the repaired delivery overlay:
`AbelianRawCoconeComplexPresentation` (27.3 seconds),
`RestrictedAffineComplexSystemNatural` (4.8 seconds), and
`HigherDirectImageRawAffineClassVanishing` (30.4 seconds), all without errors or
warnings. No importer adaptation is necessary or included.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.nonempty_higherDirectImageRaw_complex_presentation`
(node `lem-sbc-higher-image-raw-complex-presentation`). No sorry remains in the item.
The previously proved `EtaleComplexCohomologyPresentation.isColimit` remains proved.

Added two holes, each strictly a separate part of the original argument:

- `AlgebraicGeometry.Etale.exists_rawModule_restrictedAbelian_natural_iso`
  (`lem-sbc-raw-module-restricted-abelian-natural-iso`): no limit, qcqs or affine
  assumptions and no presentation conclusion; only scalar-forgetting comparison
  and its naturality for the fixed raw maps.
- `AlgebraicGeometry.Etale.restrictedOverAbelianCocone_complex_data`
  (`lem-sbc-restricted-over-abelian-complex-data`): only abelian coefficients and
  geometric complexes; its two comparison squares are explicit hypotheses, and
  it neither proves scalar comparison nor asserts cohomology continuity.

This is a decomposition: one upper hole closed and two lower holes added, net -1
before any subsequent pruning. The intermediate proofs remain work for later
workers. The new data predicate and all explicit coefficient/cohomology/map
definitions have no sorry. No arbitrary existence witness is chosen in a definition.

## No longer needed

Removed redundant direct imports of
`Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality`,
`Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
They remain reachable through the raw diagram, the scalar-comparison intermediate,
and the inverse-image coherence imports, respectively. Consequently no module or
node in the target closure is claimed pruned. All five old proof dependencies are no longer used directly by the item's proof:
`def-weil-pbc-etale-site`, `lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-colimit-constant-connected-diagram`,
`lem-weil-pbc-injective-module-abelian-acyclic`, and
`sbc-lem-higher-image-raw-over-naturality`. They remain in the plans of the two new
intermediates or in the raw diagram; this is replacement of direct dependencies,
not removal from the mathematical argument or target closure.

Also removed the redundant direct public imports of
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`. Both are publicly
exported by `EtaleComplexCohomologyPresentationData`, so downstream availability
is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing abelian cocone presentation cannot be imported here: it already imports
this item and would close a cycle. It also assumes a directed preorder and natural
cohomological degree, whereas this theorem has a small cofiltered category and an
integer degree. Its geometric plan remains applicable after those restrictions are
removed for fixed coefficients. The separate scalar comparison is indispensable:
raw-over naturality into the associated higher-image sheaf is not itself an
isomorphism with abelian complex cohomology.

The original nested-existential encoding made kernel/elaboration work expensive.
The equivalent constructor encoding repairs that representation without weakening
a statement. The unit record `sk-lem-failure-field` has no realized slot containing
this item, and its prescribed higher-direct-image-limit step is retained. The
construction remains on the original 09Z1/0EZM/03FD route. Checked edge cases:
negative degrees give zero on both sides; an empty etale test object gives zero
complexes; a cofiltered index is nonempty and connected after taking opposites;
no continuity is assumed in either intermediate.

## New nodes

`lem-sbc-raw-module-restricted-abelian-natural-iso`: the additive scalar-forgetting
comparison, natural for the actual five-factor pullback.

`lem-sbc-restricted-over-abelian-complex-data`: the geometric presentation for an
abelian coefficient sheaf with explicit comparison squares.

`def-sbc-etale-complex-cohomology-presentation-data`: one Prop-valued constructor
encoding exactly the old presentation witnesses, with no selected object or
continuity conclusion. Change record:
`coord/changes/EtaleComplexCohomologyPresentation.md`.

## Earlier second reading (a previous round; superseded)

1. **Interface and meaning — pass.** Compared the item with the repository using
   `diff` and extracted the raw signature text of all three existing declarations.
   All three declaration types and binders are unchanged, and visibility is unchanged; the presentation name is an abbrev of the bundled predicate.
   The sole definition-body change is declared in
   `coord/changes/EtaleComplexCohomologyPresentation.md`. Compared the old
   existential binders with the new constructor binders: every one of the 24
   witnesses and every equation is byte-for-byte identical, with the final True
   represented by a True constructor argument. Constructing or eliminating the
   constructor therefore gives precisely the old existential tuple. No target
   statement changes, and the predicate is not used in a target's data definitions.
   `downstream.py --uses` confirms the three named users in the change record;
   both external users compile unchanged against the sandbox overlay.

2. **Proof and axioms — pass as a decomposition.** Compiled all four delivery
   modules with `lcompile.py --all`, without errors or warnings. After removing
   the redundant imports, compiled the item again successfully. There are exactly
   two delivered sorries, the two public named intermediate theorems listed above;
   both have sources, complete proof docstrings and matching nodes. No forbidden
   declaration or data-producing sorry occurs. A scratch module prints the axioms
   of all delivery declarations, including the new constructor. The predicate,
   constructor and all three coefficient/cohomology/map definitions use only
   propext, Classical.choice and Quot.sound. The item, the two split theorems and
   the existing continuity application additionally use sorryAx from open proofs.
   Thus one original hole is closed by a checked reduction, two are added, and
   no claim of an axiom-free proof of the mathematical item is made.

3. **Split statements and searches — pass.** Read the actual fixed five-factor raw
   maps and the explicit restricted coefficient/pullback definitions. The scalar
   lemma has no diagram, limit or affine hypotheses and supplies only the natural
   comparison. The geometric lemma assumes both comparison squares and handles
   only abelian single complexes and their geometric presentation. Neither merely
   renames the original module-coefficient claim. Checked the zero ring and zero
   sheaf, q=0, negative q, the empty etale object, a one-object identity system,
   and cofiltered categories with parallel arrows: inverse-image coherence handles
   parallel arrows, and the opposite index is nonempty and connected. Negative
   degree groups vanish on both sides; emptiness introduces no selected witness.
   Read Stacks [03FD](https://stacks.math.columbia.edu/tag/03FD),
   [03Q8](https://stacks.math.columbia.edu/tag/03Q8),
   [09Z1](https://stacks.math.columbia.edu/tag/09Z1) and
   [0EZM](https://stacks.math.columbia.edu/tag/0EZM). The geometric construction
   precedes the continuity assertion and does not require it.
   Ran fresh leanfinder, loogle and grep searches with different queries, recorded
   in the new nodes, and searched both library roots. Read
   `EtaleFreeSheafDerivedSections`, `EtaleModuleCohomologyForget`,
   `ModuleAbelianDerivedDirectImageComparison`, `RawRestrictedCohomologyNaturalIso`,
   `RestrictedAffineComplexSystemNatural` and the abelian presentation module.
   These supply parts of the argument; none supplies the integer-degree scalar
   comparison with these exact transition maps or the required general cofiltered
   geometric presentation. The latter two presentation modules import this item
   and cannot supply an upstream proof. Neither remaining hole closes in a few
   minutes from the available declarations.

4. **Route and pruning — pass after report repair.** The item combines the scalar
   comparison and geometric construction, discharging its two comparison squares
   by naturality at D.map f and c.π.app i. No continuity conclusion is used to
   manufacture a presentation. The existing isColimit proof passes precisely the
   supplied witnesses to the same continuity theorem. The unit
   `sk-lem-failure-field` has empty realized slots, and its higher-direct-image
   limit route is retained. Checked all five old proof_deps; the revised
   `No longer needed` section names every one and distinguishes direct replacement
   from closure pruning. No whole module is claimed pruned.

5. **DAG and records — pass.** The item's two proof steps name the two actual
   intermediate theorems and their proof_deps union agrees with the reduction.
   Each new theorem has its matching verbatim Lean signature, source, complete
   construction/comparison plan, searches, chapter, unit, blueprint origin and
   created record. The new definition node describes exactly the constructor.
   The existing definition node records its equivalent representation change.
   No other existing statement was edited.

Second-reading changes: removed the redundant direct public imports of
LowerShriek and UpperLowerStar.Coherence from the item (both remain publicly
exported through the data module), removed an extra blank line, expanded the
pruning report to name all old dependency ids, corrected doubled TeX backslashes
in the new data node, and recorded the independent searches and review. No proof,
statement, hypothesis or witness was changed by this reading.

## Second reading by W2

This reading checks the repaired delivery against the current repository, including
reviewer X-4596e's H4 return, rather than relying on the superseded reading above.

1. **Visible interface and meaning: pass.** Diffed the delivered item against
   `lean/Sheaf/AlgebraicGeometry/HigherDirectImageRawComplexPresentation.lean`.
   The signatures of `EtaleComplexCohomologyPresentation.isColimit` and
   `nonempty_higherDirectImageRaw_complex_presentation` are byte-for-byte unchanged.
   All three existing declaration types and binders are unchanged, and visibility
   is unchanged; the presentation name is an abbrev of the bundled predicate.
   Its representation change is explicitly recorded in
   `coord/changes/EtaleComplexCohomologyPresentation.md`. A textual extraction
   verified that all 24 constructor binders, including every map equation, are
   byte-for-byte the old existential binders. The final True is still required.
   Constructor introduction and elimination therefore preserve exactly the old
   proposition, with no new hypothesis, omitted witness, or continuity conclusion.
   No Challenge target or target data definition changes. The H4 prefix repair is
   present in Lean, the existing node's lean.statement, and the change record's
   New section; its Old section retains the original def and existential body.

2. **Proof and axioms: pass as a decomposition.** Compiled all four delivered
   modules through `lcompile.py --all` with no errors or warnings; the item took
   55.5 seconds on the successful full-set run. An initial full-set run timed out
   at 60 seconds under concurrent machine load; a separate unchanged item compile
   took 50.8 seconds. A scratch copy of the actual item with `#print axioms`
   appended compiled in 50.2 seconds. The predicate, constructor, and explicit
   coefficient, cohomology, and map definitions depend only on propext,
   Classical.choice, Quot.sound. Both split theorems, the reduction, and the
   existing continuity application additionally depend on sorryAx from open
   proofs. There are exactly two delivered sorry occurrences, both the named
   public theorems listed under Proved and sorry left; no axiom, unsafe, opaque,
   extern, implemented_by, or sorry in a definition. The comparison witnesses
   are eliminated inside a proposition proof, never selected to define data.
   This closes one original syntactic hole and adds two simpler ones (net -1);
   it is not a claim that the mathematical theorem is axiom-free.

3. **Split statements and shortest routes: pass.** Read the actual
   `restrictedOverCohomologyMap`, `rawAffineRestrictedCoefficient`, and raw
   diagram/cocone formulas. The scalar statement gives only additive comparison
   and naturality, with no limit or geometric presentation conclusion. The
   geometric statement assumes the stage and apex comparison squares and supplies
   only the geometric complexes for a fixed abelian coefficient sheaf. It does
   not prove scalar comparison. These are genuinely different parts of the
   argument. Read Stacks [03FD](https://stacks.math.columbia.edu/tag/03FD),
   [03Q8](https://stacks.math.columbia.edu/tag/03Q8),
   [09Z1](https://stacks.math.columbia.edu/tag/09Z1), and
   [0EZM](https://stacks.math.columbia.edu/tag/0EZM). The source cohomology and
   fibre-product comparisons support the scalar argument; the fixed-coefficient
   geometric construction uses pullback universal properties and inverse-image
   coherence before invoking any continuity result. The general cofiltered
   construction does not need the source's preorder restriction: all coefficients
   pull back from W and identify on the limit with one constant complex.
   Checked q=0, q<0, zero ring/sheaf, empty U, the identity singleton system,
   and cofiltered categories with parallel arrows. Degree-zero complexes have
   zero negative cohomology. Empty U introduces no witness selection. Cofiltered
   I is nonempty and its opposite connected, as required for the constant cocone.
   Coherence, rather than uniqueness of arrows, handles parallel arrows.
   Fresh leanfinder, loogle, and grep queries are recorded in both split nodes;
   also searched both library roots. Read EtaleFreeSheafDerivedSections,
   EtaleModuleCohomologyForget, ModuleAbelianDerivedDirectImageComparison,
   RawRestrictedCohomologyNaturalIso, RestrictedAffineComplexSystemNatural, and
   AbelianRawCoconeComplexPresentation. The first results cover natural-degree
   comparisons in coefficients, not this complete integer-degree comparison
   natural for the fixed raw scheme maps. The geometric results import the item
   itself and have directed-preorder hypotheses. No existing complete statement
   can replace either split without a cycle or further real argument, and neither
   remaining hole is a few-minute proof from the available interfaces.

4. **Top-down route and pruning: pass.** The reduction obtains the natural scalar
   comparison, then applies geometric complex data. Its two remaining goals
   simplify the actual H.map and B.ι formulas and apply naturality to D.map f and
   c.π.app i respectively. The existing isColimit proof eliminates precisely the
   same data and applies the same continuity theorem with explicit instance
   arguments. No continuity is used to manufacture a presentation. Checked
   `dag/units/sk-lem-failure-field.json`: the item's node is in no realized slot;
   the unit's higher-image-limit step remains the route. All five old proof_deps
   are named under No longer needed, and no whole module is claimed pruned.
   Public imports supply declaration types; the scalar comparison and continuity
   imports are private proof imports. The two removed direct public imports remain
   exported by the data module, preserving downstream availability.

5. **Lean, DAG, and records: pass.** The item's node records exactly the two
   intermediate applications and naturality reduction. For every delivered node,
   proof_deps equals the union of its proof-step uses. Only proof, proof_deps,
   proof_origin change in the old theorem node; only lean changes in the old
   definition node. Every new node has the required source, chapter, unit,
   created/blueprint record and verbatim Lean signature. Both remaining theorems
   have complete source-based natural-language construction proofs in their
   docstrings. The definition node states the same existential data and has no
   proof dependencies. The named downstream-use check finds the same three
   modules listed in the change record. Unchanged copies of the two external
   named users and HigherDirectImageRawAffineClassVanishing are checked against
   the freshly compiled delivery overlay; no forced adaptation is delivered.

Changes in this second reading: recorded fresh independent searches in the two
split nodes, clarified the additional direct-importer check in the change record,
and appended this review. No Lean proof, declaration, import, hypothesis, or
witness was changed in this reading.

Current downstream timings against the fresh overlay: unchanged
AbelianRawCoconeComplexPresentation 27.8 seconds,
RestrictedAffineComplexSystemNatural 4.9 seconds,
HigherDirectImageRawAffineClassVanishing 30.8 seconds, all clean. The optional
scratch theorem converting the old nested existential to the constructor and back
hit the 60-second limit on both attempts; this reading does not claim that scratch
file compiled. The equivalence verdict uses the verified byte-identical binders
and direct introduction/elimination argument, independently of that optional probe.
