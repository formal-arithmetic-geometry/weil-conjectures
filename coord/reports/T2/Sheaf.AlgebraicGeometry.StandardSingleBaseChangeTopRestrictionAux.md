## What changed

Closed `AlgebraicGeometry.standardSingleBaseChange_topRestriction_compatibility`
without changing its signature. The proof constructs the two pullback lifts and
proves that they are inverse, obtains the coefficient comparison over the top
open, constructs the target isomorphism from the invertible apex unit and pinned
image composition comparison, applies source/apex mate transport, and cancels
the target isomorphism. The canonical source comparison is exactly the existing
`standardSingleBaseChange_topRestriction_sourceIso`.

Added two proof-only imports to the item:
`Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceTransport` and
`Sheaf.AlgebraicGeometry.OpenSingleCoefficientTransport`.
The former proves a general transport identity for arbitrary coefficient maps
and commuting squares, using the existing horizontal mate-pasting theorem and
locally proved coefficient naturality. The latter isolates the coefficient identity in the old
node's documented proof, with no base-change map or direct image in its statement.
Its full proof uses the existing single-map composition and isomorphic-pullback
counit APIs.
All four existing public declarations and public imports are preserved.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.standardSingleBaseChange_topRestriction_compatibility`
(node `lem-pc-standard-single-base-change-top-restriction-compatibility`).
No textual `sorry` remains in any delivered Lean module.

Also proved: `AlgebraicGeometry.derivedBaseChange_source_transport`
(node `lem-pc-derived-base-change-source-transport`), including its private
adjunction mate-unit helper. It has no direct `sorry`.

Also proved:
`AlgebraicGeometry.exists_openSingle_coefficient_transport`
(node `lem-pc-open-single-coefficient-transport`). This is the strictly lower
single-complex coefficient square for an arbitrary open and an isomorphic apex.
It has a complete Lean construction and coefficient-composition proof.
The public coefficient theorem is proved, including open-single normalization,
single-map naturality, the normalized composition equation, and invertibility
along the apex isomorphism. One original hole is closed; no new holes remain. The base-change mate calculation
and pullback-isomorphism assembly are complete Lean proofs.

## No longer needed

Removed exploratory proof imports DerivedBaseChangeNaturality (source import
cycle) and PinnedPullbackCompositionShifts (only the counit definition is used).
Neither exploratory import is needed by the delivered proofs. The following
old direct proof dependencies move into the helper proofs:

- `def-pc-derived-base-change-map` (source-transport helper);
- `def-pc-tensor-pullback-composition-iso` (coefficient helper);
- `lem-pc-ringed-spaces-derived-pullback-composition` (coefficient helper);
- `lem-sc-picard-termwise-single-map-composition` (coefficient helper).

These are removed from the item node's direct `proof_deps`, but remain used
transitively. None of their modules is pruned from the import closure.

None of the item's three public imports was removed: each supplies names used by
its unchanged statements or source construction. No existing node or module is
claimed pruned. The old composition and tensor-comparison dependencies remain
needed transitively through the proved coefficient lemma. The new coefficient module
imports PicardTermwiseSingleMapComposition directly; it does not import
StandardSingleBaseChangeMap or the item.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The full coefficient proof initially exceeded
the compiler time limit through repeated reduction of module-category aliases.
Keeping the chosen pullback and tensor comparisons abstract, locally reducing
Scheme.Modules, and identifying its HasDerivedCategory instance with the supplied
sheaf-module instance makes the complete module compile under the existing limit. A generic identity-map
cancellation helper avoids checking the same large scheme types repeatedly.
The 60-second compile limit was preserved and no file was split for timing. The first dry run detected an import cycle
through DerivedBaseChangeNaturality and DerivedBaseChangeMayerVietorisMaps back
to this item. Removed that proof import and proved coefficient naturality
locally from pinned adjunction identities. No existing module was adapted. The old compatibility node's proof was one long
prose step, without an API for its coefficient square. The new coefficient node
states precisely that step, independent of all base-change mates. The mate step
is proved from the already proved DerivedBaseChangeHorizontalMate and
a locally proved naturality identity; it does not require another unproved mate
coherence statement. The unit record sk-thm-picard-coherence has empty realized
statement/step lists; its route is preserved.

Searches: LeanFinder found the abstract mate composition identities; Loogle
found homEquiv_naturality_left and unit_mateEquiv. LeanSearch returned an Internal
Server Error, recorded as unavailable without an absence verdict. Grep of the
project, Mathlib Adjunction/Mates and derived exact functors found the existing
horizontal-pasting and coefficient-naturality APIs used in the proof. The
existing SourceIso theorem returns unspecified source/target isomorphisms and
does not identify its source isomorphism with the required canonical sourceIso.
SingleOpenTensorCoefficientCoherence requires different explicit normalization
hypotheses and does not provide the open-single normalization needed here.

Edge cases checked in the new coefficient statement and its construction:
empty schemes and opens, top opens, zero modules, identity k, and arbitrary
(non-flat) r and r'. Only pullback along the isomorphism k is inverted. No
comparison along the base morphism g or arbitrary r is inverted.

## New nodes

`lem-pc-derived-base-change-source-transport`, in
`lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeSourceTransport.lean`, is proved.
It separates adjunction mate pasting from the single-module coefficient theory.
The coefficient proof imports OpenPinnedSingleTensorRestrictionFactors,
IsomorphismPullbackCounit and PinnedPullbackCounitShifts only for its proof.
Its proof uses the existing horizontal mate theorem and coefficient naturality,
plus explicitly proved mate-unit cancellation, coefficient naturality and
functor naturality.

`lem-pc-open-single-coefficient-transport`, in
`lean/Sheaf/AlgebraicGeometry/OpenSingleCoefficientTransport.lean`, is
proved. It concerns only the single-module coefficient square and
constructs its isomorphism from tensor pullback composition, restriction, and
the isomorphic-apex counit. Its conclusion is needed as a hypothesis of the
proved general transport theorem. The isomorphism is explicitly constructed in its proof.

The original compatibility node's proof, proof_deps and proof_origin now follow
the delivered argument. No statements, definitions or target signatures changed;
no change record or forced adaptation is required.

## Second reading by T2

1. **Interfaces: pass.** Compared the delivered item against the repository with
   `diff -u`. The only changes are two plain proof imports and replacement of
   the compatibility theorem's `by sorry`. All four old signatures, the complete
   sourceIso definition, existing proof bodies, visibility, and public imports
   are byte for byte unchanged. Read the landed canonical-source change record:
   the hypothesis `e = standardSingleBaseChange_topRestriction_sourceIso p M`
   is retained and used by `subst e`; arbitrary source automorphisms are not
   substituted for the prescribed comparison. Neither helper module exists in
   the repository. No forced adaptations or interface change record is needed.

2. **Proofs and axioms: pass.** Compiled all three files in import order through
   `lcompile.py --all`: source transport 32.2 s, coefficients 57.5 s, item 13.9 s,
   without warnings or errors. A separate scratch module printed axioms for
   all six public declarations (the four original declarations and both new
   lemmas). Every list is exactly `propext`, `Classical.choice`, `Quot.sound`;
   none includes `sorryAx`. Scanned every delivered Lean file for forbidden
   declarations and textual holes: none. The coefficient isomorphism is the
   explicit `asIso q_k` followed by `single.mapIso b`; the item constructs both
   pullback lifts and F, and eliminates the proved coefficient existence inside
   its theorem proof. No definition obtains arbitrary data from a holed theorem.
   The private derived-category instance is the supplied `dc X` itself.

3. **New statements: pass.** The two added public theorems are fully proved,
   rather than pending split-off statements. In source transport, j and k are
   arbitrary morphisms and a,q,q',d arbitrary coefficient maps; the four path
   equations and the coefficient square suffice. After eliminating hs, the
   mate-unit helper cancels the j triangle, the coefficient equation cancels c,
   and the existing horizontal-mate theorem supplies the composition step.
   In coefficient transport, only k is required to be an isomorphism. The
   private normalization proof identifies the actual open-single comparison a;
   q-composition is applied to (k,r) and (r',U.ι), and q-naturality supplies rho.
   No comparison for arbitrary r, r', or the eventual g is inverted. Checked
   identity k, the top and empty open, empty schemes and zero modules: the same
   inverses and naturality equations apply, with no nonemptiness or flatness
   premise. `#check` confirms the coefficient theorem retains only dc from its
   section, not the auxiliary tensor-additivity variable.

   Repeated searches with different wording using msearch LeanFinder
   (`left derived functor comparison exact restriction single complex naturality`)
   and Loogle (`HomologicalComplex.singleMapHomologicalComplex`), then rg of
   Sheaf, WeilConjectures and pinned Mathlib. The online Loogle single-naturality
   candidates are absent from the pinned Additive.lean, whose degree-zero and
   off-zero lemmas are precisely those used by the local proof. Read
   DerivedBaseChangeSourceIso: its conclusion leaves the source isomorphism
   existential, so it cannot identify the required sourceIso. Read
   SingleOpenTensorCoefficientCoherence: it requires separate normalization
   hypotheses and does not prove open_single_factor. Read the already proved
   DerivedBaseChangeHorizontalMate, IsomorphismPullbackCounit, and
   OpenPinnedSingleTensorRestrictionFactors statements against their uses.
   DerivedBaseChangeNaturality and OpenUnit reach the item through their public
   Mayer--Vietoris import, so importing their naturality helpers would cycle;
   the local elementary mate calculations are justified here.

4. **Route and pruning: pass after report correction.** Followed the proof from
   the item downward: construct k, obtain its coefficient square, assemble F
   with the invertible apex unit, apply proved source transport to the exact
   a used by sourceIso, and cancel F.inv. This preserves the canonical-source
   clause and uses no unproved compatibility replacement. Every new plain
   import supplies a proof constant. Each public helper import supplies names
   appearing in its public statement; notably PicardTermwiseSingleMapComposition
   defines picardTermwiseSingleMap as well as its composition theorem. The
   original three public imports are preserved. Expanded `No longer needed`
   to list all four removed direct DAG dependencies and where they remain used
   transitively. No existing module is pruned. Read
   dag/units/sk-thm-picard-coherence.json: its realized statement and step lists
   are empty, and the delivery changes neither its statement nor its route.

5. **DAG and sources: pass after metadata correction.** Compared the old and
   delivered compatibility JSON: only proof, proof_deps and proof_origin change.
   Checked the union of each node's step uses against proof_deps; all three
   agree. Checked each dependency's recorded Lean module/declaration against
   the actual constants used, including horizontal_mate, single-map composition,
   open tensor restriction factors and isomorphic counit. Each new node has its
   own module, matching verbatim declaration text, source, proof steps, search
   records, created/blueprint/chapter/unit and lean record. The coefficient
   node's proof explicitly records its inherited dc section hypothesis.
   Read Stacks [06YJ](https://stacks.math.columbia.edu/tag/06YJ),
   [08HY](https://stacks.math.columbia.edu/tag/08HY),
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S), and
   [0D5T](https://stacks.math.columbia.edu/tag/0D5T): the new statements are the
   detailed coefficient and mate calculations from the item's documented proof,
   based on derived functor construction, the adjoint definition of base change,
   and composition. They are not claimed to be literal restatements of a Stacks
   lemma. Set the failed LeanSearch entries' verdict explicitly to `unavailable`,
   consistent with the logged Internal Server Error, rather than claiming absence.

Changes by this reader: corrected the direct-dependency accounting in the report,
marked both unavailable LeanSearch records explicitly, and added this independent
reading. No Lean proof, definition, statement, or import required repair.
One original hole is closed, zero holes are added, and zero holes are split off.
