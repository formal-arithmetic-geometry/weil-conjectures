## What changed

Replaced the sole hole in
`CategoryTheory.rightDerived_injectiveComplex_boundary` by inverse shifted
naturality of the derived unit, followed by the canonical endpoint comparisons.
The two definitions and every existing signature and visibility stay unchanged.
A private proved helper `CategoryTheory.inverse_shifted_naturality` proves the
needed cancellation of the isomorphic endpoint components of any shift-compatible
natural transformation.

Added `Sheaf.CategoryTheory.Abelian.InjectiveSESBoundaryLift` with
`CategoryTheory.injective_ses_homotopy_boundary_lift`. This constructs a common
homotopy representative of both SES boundaries from the actual degreewise
splittings, identifies each localized boundary using the existing proved
`DerivedCategory.triangleOfSESδ_eq_degreewiseSplit`, and checks the mapped
connecting map by degree components. The original module imports this helper
only for its proof. Updated the parent node and recorded the helper's node.

## Proved and sorry left

Closed: `CategoryTheory.rightDerived_injectiveComplex_boundary`
(node `lem-sc-p1-right-derived-injective-boundary`), the one original hole.

New proved theorem: `CategoryTheory.injective_ses_homotopy_boundary_lift`
(node `lem-sc-p1-injective-ses-homotopy-boundary-lift`).
The private inverse-naturality helper is proved as well.
Both modules compiled through `lcompile.py` without errors or warnings.
All three original declaration signatures and visibilities were compared with
the source and are identical.
No holes remain in either delivered module; no holes were added.
The split boundary comparison used by the new theorem already has a complete
proof in the library. This delivery is a proof, not a decomposition into holes.

## No longer needed

No original import is removed: both public imports are needed by the definitions
and statement. No original dependency is globally pruned. The old direct proof dependencies
`lem-weil-pbc-degreewise-split-connecting-morphism`,
`lem-sc-p1-split-ses-boundary-comparison`, and
`lem-weil-pbc-complex-ses-triangle` move to the new helper's proof dependencies;
all remain in the transitive proof closure. The parent theorem
uses the degreewise splitting and split-SES comparison through the new helper;
the new node retains those dependencies. The existing derived-unit and canonical
SES route is preserved. No additional resolution, augmentation, Ext, or
single-object comparison module is imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The row splitting needs the
injectivity of the first complex only; injectivity of the middle and third
complex is unnecessary for the homotopy lift. The original theorem's three
injectivity hypotheses are unchanged, and its endpoint hypotheses are used for
inverting the derived-unit components.

The local `literature/stacks-project/derived.tex` is absent on this machine.
Read the official online Stacks pages for Tags 014Q, 0152, and 015B instead:
https://stacks.math.columbia.edu/tag/014Q,
https://stacks.math.columbia.edu/tag/0152,
https://stacks.math.columbia.edu/tag/015B.
The Lean argument uses the existing split-boundary comparison for the cone sign,
and explicitly proves the additive image and shift transport calculations.
Zero rows and any common lower bound require no exception; the helper has no
nonzero or fixed-bound hypothesis. No arbitrary witness is chosen from an
unproved existence statement: the splittings and connecting map are constructed
from proved Mathlib data.

LeanFinder returned the splitting map lemmas; Loogle found the canonical SES
boundary lemmas, whose ambient functor-map lemma requires exactness and does
not apply here. Source grep found the connecting-map degree formula. LeanSearch
returned Internal Server Error, recorded as unavailable.
Blueprint searches for "degreewise split", "connecting morphism", and "0152"
found no duplicate of the helper (the sole connecting-morphism result concerns
Kummer residues). The ancestor script cannot trace `created.item` when it is a
module name, so the new node follows the existing parent's recorded ancestor
`thm-sc-p1-duality` and its horseshoe comparison chain. The unit's route is kept.

## New nodes

`lem-sc-p1-injective-ses-homotopy-boundary-lift` in
`dag/nodes/sec-picard-framework/` records the proved simultaneous source/image
boundary lift. Its Lean module is
`Sheaf.CategoryTheory.Abelian.InjectiveSESBoundaryLift`. This is strictly the
boundary-identification part of the parent argument; it mentions neither a right
derived functor nor its unit and assumes injectivity only in the first complex.
There are no change records because no existing public interface is changed.

## Second reading by A4

1. Compared the parent module with the repository using diff. Both existing
   definitions (including their bodies), all three declaration signatures,
   universe parameters, hypotheses, and public visibility are byte-for-byte
   unchanged. Only the theorem proof, a private proved helper, a proof-only
   import, and an elaboration option are added. No statement change or change
   record is needed. No open change record names these declarations.
2. Read both complete proofs and the existing split-SES comparison. Compiled
   both delivered modules locally and printed axioms for both definitions,
   both public theorems, and the private inverse-naturality helper in scratch
   copies. Only propext, Classical.choice, and Quot.sound occur. There is no
   sorry, axiom, unsafe, opaque, implemented_by, or extern in either delivery.
   The degreewise splittings come from Mathlib's proved splittingOfInjective;
   the homotopy witness is explicitly constructed from their connecting map.
   No data is chosen from an unproved existence statement. Verdict: sound.
3. No statement is split off with sorry. The new proved boundary-lift theorem
   is strictly the source/image boundary identification part of the argument,
   without a derived functor, unit, or enough-injectives hypothesis. Checked
   zero rows (connecting components vanish), identity functors (both equations
   coincide), and arbitrary lower bounds (the shifts and additive image preserve
   boundedness). Its proof docstring and complete node match the construction.
   Independent LeanFinder, Loogle, and grep searches with new wording found
   shift naturality, mapping-cone functoriality, and splittingOfInjective, but
   no existing simultaneous bounded-below lift. The exact-functor boundary-map
   theorem has a stronger exactness hypothesis and cannot replace this result.
   Repository searches found the already-used split-SES comparison and no
   duplicate lift. Verdict: true, needed, and not a restatement of the parent.
4. The parent proceeds from a concrete boundary lift to inverse shifted-unit
   naturality and canonical comparison cancellation. It uses the existing
   proved split-SES comparison through the helper; no new cone lemma is needed.
   The small private cancellation helper works with endpoint isomorphisms only,
   so the natural-isomorphism lemmas map_naturality_1/2 do not replace it without
   stronger hypotheses. Read the unit record and original ancestor chain:
   its realized fields are unchanged, and the horseshoe/duality route is kept.
   The report now explicitly lists all old direct dependencies moved to the
   helper. None is pruned from the transitive closure. Verdict: route preserved.
5. Compared the parent node's proof and proof_deps with the actual parent proof;
   read every old dependency's Lean/mathlib record and the complete new node.
   Their steps, dependency unions, proof origins, module paths, source tags,
   ancestor chain, and the new verbatim Lean statement agree with the code.
   The new node has the required created, blueprint, searches, status, chapter,
   unit, and lean fields. Verdict: metadata agrees.

Changed the new helper's import of
`Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit` from public import
to plain import: it is used only in its proof. Expanded `## No longer needed`
to name the three dependencies moved from the parent to the helper. No correct
proof was rewritten, no hole was added, and no existing interface was changed.
