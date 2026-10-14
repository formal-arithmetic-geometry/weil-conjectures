## What changed

Corrected the false intermediate interface
`AlgebraicGeometry.singleComplexOpenComparison_union_ses_compatibility`.
It now constructs compatible short exact cylinder rows from a prescribed strict
chain square and three component comparison equations. Its proof is complete,
including degreewise splitting, contraction of the identity cone, the row map,
and the localized middle-component equation. The cylinder implementation follows
the already proved private implementation in `StandardSingleUnionSESPresentation`;
no new existence theorem is used to define any data.

Added `Sheaf.AlgebraicGeometry.SingleComplexOpenUnionCompatibleChainData`, stating
the remaining geometric construction before the cylinder step. It asks for chain
maps and compatible cone models, not short exact rows, monomorphisms or epimorphisms.

Adapted `Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESPresentation` only as
forced by the interface correction: obtain compatible chain models, then apply
the cylinder construction. Its statement, universes and visibility are unchanged.
Updated the two existing DAG proof routes and recorded the corrected statement.
Change record: `coord/changes/single-complex-union-compatibility.md`.

All three sandbox modules compile without warnings through lcompile.py. The
original parent fails against the corrected interface, while the adapted parent
compiles. No Challenge target or definition was changed.

## Proved and sorry left

The corrected `AlgebraicGeometry.singleComplexOpenComparison_union_ses_compatibility`
is proved without any sorry and without new proof dependencies. Its private
helpers are proved. The old false universal assertion is repaired, not claimed
as a proof of that assertion.

One hole added:
`AlgebraicGeometry.singleComplexOpenComparison_union_compatible_chain_data`, node
`new-single-complex-open-union-compatible-chain-data`. This is the geometric
resolved-diagram construction, retaining the specified comparison maps and cone
homotopy before passing to a strict square. Its docstring contains the complete
construction plan. The delivery is an interface repair and a decomposition:
one old hole removed, one narrower geometric hole added, net zero.

`AlgebraicGeometry.singleComplexOpenComparison_union_ses_presentation` remains
proved from the new geometric statement and the proved cylinder construction;
there is no sorry in its proof. The original and adapted parent signatures match
verbatim. No other existing holes were edited.

## No longer needed

Removed the parent's proof import
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESObjects` and dependency node
`new-single-complex-open-union-ses-objects`. That node's object-only route through
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESCore`, node
`new-single-complex-open-union-ses-core`, is no longer needed by this presentation.
These two modules are not imported by other modules, apart from their own chain,
so both leave the target import closure along this route.

The item no longer imports `SingleComplexOpenComparison`, QuasiCompact,
QuasiSeparated or BinaryBiproducts directly: its cylinder statement is generic
and Mathlib DerivedCategory.ShortExact supplies its categorical requirements.
Its original planned proof dependencies `lem-pc-cone-diagram-ses-presentation`
and `prop-pur-kinjective-resolutions-exist` are not used by the cylinder proof.
The former omits middle-component compatibility; the proved concrete cylinder
construction establishes that missing equation directly. K-injective theory is
still needed by the new geometric node, so it is not claimed globally pruned.

The parent node's obsolete baseline dependencies are replaced by exactly the
compatible-chain-model node and cylinder-construction node. Its old list included
`def-pc-derived-base-change-map`, `def-pc-single-complex-open-comparison`,
`lem-pc-cone-diagram-ses-presentation`, `lem-pc-derived-base-change-source-iso`,
`lem-pc-derived-direct-image-composition`, `lem-pc-derived-pullback-tensor-qcoh`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-single-complex-nested-coefficient-coherence`,
`lem-sc-ringed-space-injective-restriction-surjective`, and
`prop-pur-kinjective-resolutions-exist`. Some remain needed below the geometric
node or for definitions; this is pruning of this parent's direct proof plan,
not a claim that all those modules are absent from the entire target closure.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-f3288 return: B9 records the blueprint ancestor
`lem-pc-coherent-hi`, the requested Tag 0DJ9 place and all seven intervening
nodes, with `same_as: []`. B7 records the first Mathlib search verdict as
`unavailable`, retaining its date of 2026-10-14. These are metadata corrections.

STATEMENT-DISPUTED (old statement): short exactness imposes no relation between
arbitrary row maps and arbitrary comparison arrows. Take identity scheme maps
on Spec(Z), K=K'=0, and U=V=top. Let A be the structure module concentrated in
degree zero, and let a constantly be the identity arrow on Q(A). Set P=P' to
the split row A → A⊕A → A, choose the canonical localized isomorphisms, and
choose m=0. Every old hypothesis holds, but its first equation says 0=id on
Q(A), impossible since A has nonzero degree-zero cohomology. Even tying a to
the coefficient comparison would leave arbitrary m unconstrained.

The parent applied this false assertion after independently choosing its rows.
`SingleComplexOpenUnionSESCore` explicitly chooses alpha=beta=0 and therefore
cannot supply geometric comparison compatibility. It is correct for its weaker
object-only statement and has not been modified. Arbitrary triangle completion
would also not identify the prescribed overlap map; the new node retains the
homotopy from the resolved geometric diagram before strictification.

The corrected cylinder theorem is the explicit construction of
[Stacks 013N](https://stacks.math.columbia.edu/tag/013N), with termwise-split
quotient as in 014G and contraction as in 013O. The geometric node follows
[08HZ](https://stacks.math.columbia.edu/tag/08HZ) for resolved restriction rows,
[08HY](https://stacks.math.columbia.edu/tag/08HY) for the base-change mate, and
[0DJ9](https://stacks.math.columbia.edu/tag/0DJ9) for the comparison diagram.
These sources were read online on 2026-10-14; local literature files are absent
in this remote checkout. No unit statement or unit-level induction step changes.

The cylinder's edge cases are certified by its general Lean construction: zero
complexes, zero component maps and arbitrary identical vertices need no special
hypotheses. For the new geometric node, empty opens give zero rows; equal or
contained opens give split rows; zero coefficients give zero comparisons. No
coefficient arrow is assumed invertible. It is stronger than object-only models
precisely where the prescribed three morphisms must be retained.

Searches: LeanFinder returned only generic short-complex/cylinder lemmas;
Loogle gives mappingCone.map and map_eq_mapOfHomotopy, not this geometric
comparison. LeanSearch returned Internal Server Error. Repository grep found the
single-module version and the object-only core, neither of which supplies the
arbitrary-derived-coefficient geometric construction. Results are recorded in
the new node and sandbox searches.jsonl.

## New nodes

`new-single-complex-open-union-compatible-chain-data`, in
`dag/nodes/sec-picard-framework/`, states the strict chain-model step before
cylinder presentation. It contains no short exactness conclusion. Its three
compatibility equations are for alpha, beta and the functorial cone map rather
than components of a short exact row. The proven cylinder splitting and
transport combine these inputs into the unchanged parent statement.

## Forced adaptations

`Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESPresentation` is unclaimed in
the local claim snapshot. Against the corrected dependency, its original source
fails at line 103: `Application type mismatch: f has type X ⟶ S but is expected
to have type CochainComplex ?m.445 ℤ` in the old compatibility application.

Changed only its object-only proof import to CompatibleChainData and its proof
lines 98–105: obtain strict compatible models and apply the corrected theorem.
The initial `classical`, `dsimp only` and local a definition are unchanged. All
existing signature and visibility text is identical. The adaptation is necessary
because the original theorem application has no compatible-square data; the
adapted file compiles in the delivered set. deliver3.py repeats both original
baseline and original-against-overlay checks for independent review.



## Earlier second reading (a previous round; superseded)

1. **Interfaces and forced adaptation — pass.** Independently diffed every existing
   delivered module against the repository. The only changed public declaration
   is the compatibility theorem, explicitly recorded in
   `coord/changes/single-complex-union-compatibility.md` and its node's
   `statement_change`. Its old arbitrary-row statement is false: the split
   nonzero degree-zero row with identity comparison and zero row morphism violates
   the first equation. This repair is not a proof of that old assertion.
   The parent's declaration signature is byte-for-byte identical; the diff changes
   only its proof import and the necessary applications in lines 98–105. No
   existing definition or target is changed. Repository search confirms that
   the parent is the compatibility declaration's only external user.

2. **Proof and trust — pass.** Compiled the three-module set through lcompile.py
   after the import repair, without errors or warnings. Independently appended
   `#print axioms` in scratch copies of all three public declarations: the corrected
   compatibility theorem uses only propext, Classical.choice and Quot.sound;
   the geometric lemma and parent additionally use sorryAx. The delivery contains
   exactly one sorry, the named geometric theorem, and no forbidden declarations
   or attributes. Read the degreewise retraction/section equations, the identity
   cone contraction, both row-map squares, and the localized middle equation.
   All data are explicit constructions; no arbitrary existence witness is used
   to define an object. Scratch copies were removed before delivery.

3. **New statement and searches — pass as a decomposition.** The geometric lemma
   is the resolved comparison-diagram step, retaining its specified cone map;
   it asserts no short exact row, mono or epi. The generic cylinder proof supplies
   those conclusions, so this is a real reduction rather than a renamed parent.
   The new hole is true by the functorial resolved restriction construction and
   cone-preserving rectification in its docstring. Read Stacks 08HZ, 08HY, 0DJ9
   and 013N independently online and the existing HomotopySquareRectification,
   OpenUnionImageComplexExact, StandardSingleUnionSESChainData,
   RelativeMVSESPresentation and SingleComplexOpenUnionSESCore sources.
   Zero coefficients and empty opens give zero terms; U=V gives diagonal/difference
   split rows and duplicate component comparisons; V≤U gives the corresponding
   split row. Arbitrary coefficient maps need no invertibility. LeanFinder search
   for lifting derived Mayer–Vietoris restriction diagrams returned only site
   Mayer–Vietoris constructions. Loogle mapOfHomotopy search returned the generic
   cone-map API. Repository searches found no theorem with these arbitrary-derived
   inputs and all three prescribed comparisons. The existing standard-single
   result specializes the coefficients and derived instances; the object-only
   core deliberately uses zero maps. The remaining geometric hole cannot be
   closed by a short application of these declarations.

4. **Route and pruning — pass.** The cylinder theorem's sole public import is
   needed by its signature. The existing ConeDiagramSESPresentation theorem
   omits the middle-component equation, so its existential output cannot replace
   the explicit compatible construction. Removed the new geometric module's
   unused ShortExact import in favor of DerivedCategory.Basic, and removed its
   redundant explicit BinaryBiproducts import. All its remaining imports supply
   signature notions. Kept the parent's existing public imports, changing only
   the forced proof import. Checked the original proof_deps against the report's
   No longer needed list. SESObjects and SESCore have no remaining external
   importers after this adaptation; shared underlying modules are not claimed
   globally pruned. The unit sk-thm-picard-coherence has empty realized statement
   and step lists; no unit record or induction route is changed.

5. **DAG agreement — pass after repair.** Read all three delivered nodes and
   compared their routes with Lean. The parent's proof uses exactly the two
   listed nodes. The corrected cylinder proof has no project proof dependency.
   The new node contains its source, complete construction plan, searches,
   provenance, chapter/unit and Lean record; its proof_deps describe the remaining
   planned geometric proof. Replaced the normalized one-line signatures in the
   compatibility and new geometric node records by the verbatim multiline Lean
   signatures, without changing their mathematical statements.

Second reading changed only the new module's redundant imports, verbatim DAG
signature records and this report. No proof rewrite was needed. Accounting:
zero original assertions proved unchanged; one false interface replaced by a
fully proved corrected theorem; one named geometric hole added. This is an
interface repair and decomposition, not a net-positive proof claim. The parent
continues to depend on the remaining hole.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESPresentation
Original against changed dependencies failed:
```
/tmp/forced-adaptation-rsurmwwb/lean/Sheaf/AlgebraicGeometry/SingleComplexOpenUnionSESPresentation.lean:103:56: error: Application type mismatch: The argument
  f
has type
  X ⟶ S
but is expected to have type
  CochainComplex ?m.445 ℤ
in the application
  singleComplexOpenComparison_union_ses_compatibility f

(with the modules compiled into /tmp/forced-adaptation-rsurmwwb/.lbuild) [6.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by J2

1. **Visible interfaces — pass.** Independently diffed both existing delivered
   modules against this repository. The compatibility signature correction is
   explicitly declared in the change record and node's statement_change. The old
   assertion really permits arbitrary a and m: identity comparisons on a nonzero
   split row and m=0 contradict its first equation. The parent's entire theorem
   signature is byte-identical, checked by extracting the text through `:= by`.
   Its changes are confined to the necessary proof import and applications.
   Repository search finds this parent as the only external user. No target or
   existing definition changes.

2. **Proof and trust — pass.** Independently compiled all three modules with
   lcompile.py, without errors or warnings. Scratch copies with #print axioms
   show only propext, Classical.choice and Quot.sound for the corrected cylinder
   theorem; the geometric theorem and parent additionally depend on sorryAx.
   There is exactly one sorry token in the delivered Lean, in the named geometric
   theorem. No forbidden declaration or attribute occurs. Read the degreewise
   splitting, identity-cone contraction, both row-map squares and middle-component
   projection equation. The construction defines actual maps, not data selected
   from an unproved existence theorem.

3. **Remaining statement — pass as decomposition.** Read the new theorem and
   complete construction docstring, and independently read Stacks 08HZ, 08HY,
   0DJ9, 013N and 013O online. Relative restriction rows and the resolved
   base-change mate give the specified diagram; retaining its homotopy before
   rectification is essential to the overlap equation. The existing proved
   homotopy_square_cone_rectification transports exactly that cone map, but does
   not construct the geometric diagram. The new lemma has no short-exactness,
   mono or epi conclusion; the explicit cylinder proof supplies this separate
   algebraic part. Empty opens and zero coefficients give zero diagrams; repeated
   or contained opens give split restriction rows. Arbitrary coefficient arrows
   require no invertibility. An independent LeanFinder query about lifting derived
   restriction triangles returned generic cone/triangle maps; Loogle's
   mappingCone.mapOfHomotopy query returned the generic homotopy-square API.
   Repository searches for compatible cones and union chain data found only the
   standard-single specialization and the object-only core, neither supplying
   these arbitrary-derived inputs. This hole cannot be closed by a short existing
   theorem application. It is a genuine reduction, not an unchanged conclusion
   under a second name.

4. **Route and pruning — pass.** Checked the old dependencies and the report's
   No longer needed list. ConeDiagramSESPresentation omits the required middle
   equation; its existential output alone cannot replace the proved construction.
   The compatibility module's only public import supplies its signature. The new
   module's imports supply the geometric signature and cone API. The parent's
   existing public imports are preserved; its changed proof import is forced.
   SESObjects and SESCore have no other external importers in this checkout.
   Shared geometric dependencies are not claimed globally pruned. The unit
   sk-thm-picard-coherence has empty realized statement and step lists; its route
   and every unit record remain unchanged.

5. **Nodes — pass.** Read all three node records. Independently checked each
   lean.statement against its verbatim multiline Lean signature. The parent uses
   exactly the compatible-chain node and the cylinder node. The cylinder has no
   project proof dependency. The new node's planned dependencies match its
   resolved-diagram construction, and its source, searches, provenance, blueprint
   ancestor/via chain, chapter, unit and Lean record are present. B7's unavailable
   search verdict and B9's ancestor and seven intervening nodes are retained.

This second reading changed only the report, adding the independent checks above.
No Lean or DAG repair was needed. Accounting remains an interface repair and
one-for-one decomposition: zero original assertions proved unchanged, one false
interface replaced by a completely proved corrected cylinder theorem, and one
named geometric hole added. The parent remains dependent on that hole.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESPresentation
Original against changed dependencies failed:
```
/tmp/forced-adaptation-o06wqlvw/lean/Sheaf/AlgebraicGeometry/SingleComplexOpenUnionSESPresentation.lean:103:56: error: Application type mismatch: The argument
  f
has type
  X ⟶ S
but is expected to have type
  CochainComplex ?m.445 ℤ
in the application
  singleComplexOpenComparison_union_ses_compatibility f

(with the modules compiled into /tmp/forced-adaptation-o06wqlvw/.lbuild) [6.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
