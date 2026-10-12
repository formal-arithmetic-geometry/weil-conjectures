## What changed

Proved `AlgebraicGeometry.etaleFpqcAgreementOpens_compatible` without changing its
signature, universes, visibility, or hypotheses. Its proof now extends the given
ordinary étale agreement criteria to arbitrary scheme maps, compares the canonical
equality predicates on the double overlap, and tests the two inverse-image opens'
own inclusions to prove both containments.

Added three statement modules, each with its own node:

- `EtaleSectionsEqualOpenArbitraryCriterion`: fully proved. It identifies an arbitrary
  prescribed ordinary agreement open with the canonical open of Tag 09XM. The
  private ordinary/canonical restriction comparison follows the already proved
  calculation in `EtaleSectionsEqualOpenEtaleCriterion`, using the existing
  inverse-image restriction theorem; it does not assume a new comparison axiom.
- `EtaleFpqcAgreementSectionsOverlap`: fully proved from the matching-section
  propagation statement. Its private unit identity is proved directly from the
  chosen composition-unit equation and naturality. Its private restriction
  identity is proved by unit naturality and pullback projection calculations.
  The two unit images of `t` are identified explicitly, including equality
  transport and injectivity of the transport and composition components.
- `EtaleFpqcMatchingSectionsPullback`: the sole remaining hole, the formal
  propagation of a given matching equality to an arbitrary commuting cone.
  This statement involves no agreement opens, étale object `V`, or test section
  `t`. It is strictly the matching-section part of the overlap argument.

The item's two new imports are proof-only imports. No existing definition or
statement changes, and no forced adaptations, are required. Updated the item's
proof route and supplied node records for the three new modules.

Repair of the returned delivery: removed the duplicate private theorem
`canonicalSection_eq_iff_arbitrary` entirely. Generalized the local restriction
comparison `canonicalSection_etale_eq_iff` to accept an explicit structural map
`w` and its commutativity proof, so its equality elimination handles both uses
directly. The duplicate is not renamed or restated elsewhere. The existing
library helper is private and cannot be reused through an ordinary import.
Public signatures and proof imports stay unchanged. The existing second-reading
section below records the previous version; the repaired proof requires a fresh
second reading.

Recompiled all four delivered modules in import order with `lcompile.py --all`: no
errors or warnings (approximately 4, 5, 16, and 4 seconds). Independently reran
`tools/import_prune_check.py` on the repaired criterion against an empty old file;
it exited zero without findings. Checked the original theorem signature byte for
byte and all Lean line widths. The only delivered sorry remains the named matching
section propagation theorem. The final validation command is
`deliver3.py A3 Sheaf.AlgebraicGeometry.EtaleFpqcAgreementOpenCompatibility --no-push`;
the dry run printed OK, compilation and preflight passed, and nothing was pushed.
The tool reported that its appended axiom probe for the unchanged overlap module
timed out after 60 seconds; the merge reruns this probe. Ordinary compilation of
that module succeeded in about 16 seconds. This repair does not claim a fresh
completed axiom probe for the overlap module; the earlier second reading below
contains the previous explicit axiom checks.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.etaleFpqcAgreementOpens_compatible`
(node `lem-weil-pbc-etale-fpqc-agreement-open-compatibility`).

Also completely proved the new public declarations:

- `AlgebraicGeometry.etaleSections_equal_open_arbitrary_criterion`
  (node `lem-weil-pbc-etale-sections-equal-open-arbitrary-criterion`).
- `AlgebraicGeometry.etaleFpqcAgreementSections_overlap_eq_iff`
  (node `lem-weil-pbc-etale-fpqc-agreement-sections-overlap`).

Added exactly one hole:
`AlgebraicGeometry.etaleFpqcMatchingSections_pullback`
(node `lem-weil-pbc-etale-fpqc-matching-sections-pullback`). Its proof is exactly
`by sorry`, in its own public statement module, with a source and detailed proof
in words. There are no other sorries in the delivered files and none in any
private helper or definition.

This is a decomposition: one existing hole closed and one strictly smaller hole
added, hence net zero holes closed before the ledger computes the full closure.
It is not a claim that the theorem is free of all transitive sorry dependencies.
The remaining propagation calculation can start with the compiled scratch
`Composition.lean` in the item's scratchpad: its `secTo_comp` identity was proved
from the composition units, but is not imported or delivered because the final
proof does not use it. Its private-only-module and unnecessary-simpa warnings
are confined to that scratch file.

## No longer needed

Removed the duplicate private theorem `canonicalSection_eq_iff_arbitrary`;
its role is subsumed by the generalized restriction comparison, rather than
another transport theorem.

No original import was removed: the public composition-unit import is still
required by the unchanged statement and by the overlap calculation.

The planned direct dependency
`lem-weil-pbc-etale-sections-equal-open-etale-criterion`, module
`Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion`, is not needed by
this proof and is absent from its imports and updated proof dependencies. Its
existential statement gives some ordinary agreement open, whereas this argument
needs the arbitrary-map criterion for the prescribed open. The latter interface
is proved in the new generic module. This is pruning of this proof route; no
claim is made that other targets cease to use the old module.

The canonical agreement-open and inverse-image restriction dependencies remain
needed transitively through the new generic criterion. Fibre products remain
needed throughout, and composition units remain needed both in signatures and
in the proved comparison identities. No other planned dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified that renaming `canonicalSection_eq_iff` to
`canonicalSection_eq_iff_arbitrary` retained a duplicate statement and did not
repair the first rejection. This repair deletes the duplicate declaration and
combines its transport with the substantive restriction comparison using
explicit `w` and `hw` binders. The library theorem is private, so importing its
module would not expose it; no existing library interface is changed to make
it accessible. No statement was found false and no unit route was bypassed.
The DAG plan is
mathematically sound, but its existing ordinary agreement-open interface did
not expose the universal extension for an already prescribed open. The new
criterion supplies and proves this interface. The double-overlap plan also hid
the section-level propagation of hcompat through another arbitrary inverse
image; that strictly smaller calculation is now stated explicitly as the one
remaining item. The unit-image comparison and ordinary-restriction comparison
are proved rather than being included in that hole.

Read the source proof of `lemma-where-sections-are-equal` (Tag 09XM) and
`lemma-describe-pullback` (Tag 09XN), including the paragraph beginning Let V,
from the available Stacks source copy. The repository's literature checkout
omits the tex file locally. Searches used LeanFinder, Loogle, LeanSearch, and
Mathlib/library grep; LeanSearch returned Internal Server Error, recorded as
unavailable rather than a negative search result. Blueprint searches for
agreement open, sections agree, and pullback sections found no duplicate.

Checked the new statements on empty test schemes, an empty index type, identical
sections, repeated indices, and identity pullbacks. There is no covering,
nonemptiness, affineness, or injectivity-of-unit hypothesis. Only isomorphism
components and equality transports are used injectively. All helper definitions
are concrete constructions; no arbitrary witness is extracted from an unproved
existence theorem.

## New nodes

`lem-weil-pbc-etale-sections-equal-open-arbitrary-criterion` records the proved
ordinary-to-arbitrary criterion, sourced to Tags 09XM and 03S2, with dependencies
on the existing canonical agreement-open and inverse-image restriction results.

`lem-weil-pbc-etale-fpqc-agreement-sections-overlap` records the proved comparison
of the two canonical equality predicates on every test map into a double overlap.
Its dependencies are the chosen composition units, fibre products, and the new
matching-section propagation statement.

`lem-weil-pbc-etale-fpqc-matching-sections-pullback` records the sole new sorry:
propagation of matching global sections to a commuting cone. Its source is the
because-the-sections-agree sentence of Tag 09XN, with composition-unit algebra
from Sites Tags 03CB and 03CC. Its proof dependencies are the existing
composition-unit theorem and fibre-product universal property. Its conclusion
is a section equality with the exact specified transport, not an equality of
agreement opens or a repackaging of the original theorem. There is no change
record because no existing interface changed.

## Earlier second reading (a previous round; superseded)

1. **Existing interfaces: pass.** Read the four delivered modules and diffed
   `EtaleFpqcAgreementOpenCompatibility.lean` against the repository version.
   Only two plain imports and the body following the original `:= by` changed.
   The entire original theorem signature and docstring, universes, visibility,
   `hcompat`, `hE`, and conclusion are byte for byte unchanged. There are no
   existing definitions changed or forced adaptations. Each new public signature
   occurs verbatim in its node's `lean.statement`.

2. **Proof and trust: pass with the reported hole.** Independently compiled all
   four files with `lcompile.py --all`: no errors or warnings, approximately
   4, 5, 17, and 4 seconds in import order. A scratch copy with explicit
   `#print axioms` checks gives only `propext`, `Classical.choice`, and `Quot.sound`
   for `etaleSections_equal_open_arbitrary_criterion`. The compatibility theorem,
   overlap equivalence, and matching-section theorem additionally use `sorryAx`,
   as expected from the one reported split. The first scratch probe could not
   name the matching theorem through the overlap module's proof-only import;
   adding its explicit import in the scratch copy made all four probes succeed.
   The delivered sources contain exactly one `sorry`, the named public theorem
   `etaleFpqcMatchingSections_pullback`; no forbidden trust escape or holed
   definition occurs. `unitSec`, `delta`, `secTo`, `glob`, and `canonicalSection`
   are explicit constructions. The chosen composition family is determined by
   the fixed-sheaf uniqueness clause of the existing composition-unit theorem;
   no arbitrary data is selected from unproved mere existence.

3. **Intermediate statements: pass.** Read the local Stacks source
   `etale-cohomology.tex`, labels `lemma-where-sections-are-equal` and
   `lemma-describe-pullback`, especially its Let V paragraph, and the composition
   of sites lemma and definition in `sites.tex`. The sole open statement concerns
   global sections and a commuting cone, without E, V, t, or any agreement-open
   conclusion, so is strictly a part of the original argument. Its proof applies
   canonical global restriction along `(a,b):Z -> T_j times_S T_k` to hcompat;
   unit naturality in sheaves and site objects, the existing associativity clause,
   and the two pullback projection equations give the displayed transported
   equality. These are available clauses of the cited theorem, not additional
   hypotheses. Checked empty I (vacuous), empty Z (unique sections), repeated
   indices (hcompat remains the premise), identical sections, and identity maps.
   The arbitrary criterion tests the inclusions of E and the unique canonical W;
   the overlap proof uses injectivity only of isomorphism components and equality
   transport. No cover or injective unit is assumed. Independently searched
   LeanFinder for propagation on a fibre-product cone and `rg` in lean/Sheaf,
   lean/WeilConjectures, and the upstream WeilConjectures checkout. Hits concerned
   topological sheaf gluing or the existing existential agreement criterion,
   not these statements. Loogle confirmed the functor composition lemma already
   used by the proof. No existing public statement replaces the open cone lemma.
   The scratch composition lemma handles one leg of its calculation but not
   the sheaf-morphism naturality and triple-composition transport needed to
   close the remaining theorem; no speculative replacement was delivered.

4. **Route and pruning: pass.** Read from the original theorem downwards:
   `htest` is just the presheaf composition law applied to hE; `hall` composes
   the two arbitrary criteria with the overlap equivalence; applying hall to
   each inverse-image open's own inclusion gives the two containments. In the
   overlap proof, `secTo_unit` uses the actual composition-unit formula and
   naturality; `secTo_restrict` uses unit naturality and pullback extensionality;
   `reduce` reflects equality through a composition isomorphism; `hpq` and `hw`
   give exactly the maps and transport required by the open lemma. Public imports
   supply the names occurring in statements, and the target's two additions are
   proof-only. Of the old proof dependencies, the ordinary existential étale
   criterion is unused and reported pruned; the canonical agreement-open and
   inverse-image restriction results remain used by the new arbitrary criterion;
   fibre products and composition units remain used by the overlap calculation.
   No original import is removed and no globally unreachable module is claimed.
   Read `dag/units/sk-thm-iff.json`: its realized statement and step remain
   `lemma-weil-pbc-property-iff-acyclicity`. This below-unit calculation replaces
   none of that unit's realized route.

5. **Nodes: pass.** Checked all four node statements against the actual Lean
   signatures, each proof step against its cited statement, and `proof_deps`
   against the union of step uses. The original node changes only `proof`,
   `proof_deps`, and `proof_origin`. Its three steps match htest/hall/containments.
   The new criterion cites the canonical open and restriction comparison; the
   overlap node cites composition units, fibre products, and cone propagation;
   the sole open node cites composition units and fibre products. New nodes have
   source-backed full proofs in words, search records, creation data, blueprint
   ancestry, the original chapter/unit, and exact Lean records. No statement or
   change record is missing.

Changed during this second reading: appended this independent review and recorded
explicit axiom checks; no delivered Lean proof, signature, import, or node needed
repair. The delivery remains a decomposition, one original hole closed and one
smaller hole added, not a net-positive hole count or a sorry-free target.

## Second reading by A3

1. **Existing interfaces: pass.** I compared the delivered compatibility module
   with the repository version. The theorem signature, hypotheses, visibility,
   universes, and conclusion are unchanged; only proof imports and the proof body
   differ. The three added modules introduce new declarations whose signatures
   match their node records exactly.

2. **Proof and trust: pass.** Each delivered module compiles individually with
   `lcompile.py`; the overlap module completes within the 60-second limit. The
   only `sorry` is the named public matching-section propagation theorem, and it
   is exactly the whole proof of that theorem. No definition contains `sorry`,
   and no forbidden axiom or escape mechanism occurs.

3. **Intermediate statements: pass.** The arbitrary-map criterion and overlap
   equivalence are strictly smaller than the original compatibility theorem and
   are required by its proof. The remaining matching-section statement removes
   the agreement-open and test-section data and states only the cone propagation
   calculation. Their edge cases and transport directions are consistent with
   the stated sources.

4. **Route and pruning: pass.** The proof uses the arbitrary criterion, overlap
   comparison, fibre products, and composition units as recorded in the DAG. The
   unused ordinary existential criterion was removed from the route and imports;
   no unit step was bypassed.

5. **Nodes: pass.** The item node and all three new nodes have proof dependencies
   matching the declarations actually used, source-backed proof descriptions,
   and exact Lean records. The unit and chapter fields are retained, and the
   sole split node is documented with its remaining hole.

I found no further defect and made no Lean changes during this second reading.
