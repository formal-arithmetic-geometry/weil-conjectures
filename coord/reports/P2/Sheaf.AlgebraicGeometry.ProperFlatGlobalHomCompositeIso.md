## What changed

Replaced the proof of AlgebraicGeometry.properFlatGlobalHomComposite_isIso without
changing its signature, visibility, or docstring. The main proof establishes the
mate counit equation from Mathlib conjugateEquiv_counit, counit naturality and triangle
identities. It then applies the mixed counit-square transport, transposes with the
scalar-extension adjunction, uses scalar-square naturality, and cancels the final
invertible global Hom adjunction map. The resulting factorization is scalar extension
of the first global Hom adjunction, affine RHom base change out of Rf_*M, and Hom of
beta_M inverse. It never assumes that the right-adjoint base-change mate is invertible.

Added four modules: MixedHomDirectImageComparison, MixedGlobalHomAdjunctionIso,
MixedGlobalHomBaseChangeCounitTransport, ProperFlatImageGlobalHomBaseChangeIso.
The first two are proved from existing declarations, using the fixed canonical
mixed tensorator, normalized mixed Leray, qcqsSheafRHomAdjunction and
 dqCoherator_isIso_derivedGlobalSections. The last two isolate exactly the remaining
steps. Each has a source, proof in words, and matching node. The comparison chosen
in mixedHomDirectImageComparison is uniquely determined: evaluating its mate equation
on the identity of Rf_*RHom(L,M) determines the component via inverse adjunction and
tensor-Hom bijections. Its existence theorem is proved, with no new sorry.

The original node's proof, proof_deps and proof_origin now describe the Lean assembly.
Its statement and all existing Lean signatures remain unchanged. The unit record
sk-thm-picard-duality has empty realized bindings; no unit statement or step is bypassed.
The source route in Tag 0AA8 is retained, including proper-support perfect direct image
and perfect RHom base change inside the affine-image obligation. No other existing
module was adapted and no change record is necessary for the proof-only import changes.

All five modules compile via lcompile.py --all. The main file took 38.8 seconds,
within the single-file limit. There are no compiler errors or warnings.

## Proved and sorry left

Closed the one original local hole:
AlgebraicGeometry.properFlatGlobalHomComposite_isIso
(node lem-sc-proper-flat-global-hom-composite-isIso).

Added two holes, both strictly parts of the original argument:

- AlgebraicGeometry.mixedGlobalHom_baseChange_counit_transport
  (lem-sc-mixed-global-hom-base-change-counit-transport): compatibility of canonical
  Hom comparisons for an arbitrary commuting square of morphisms; no properness,
  flatness, perfectness, or right-adjoint base-change map occurs.
- AlgebraicGeometry.properFlatImage_globalHomBaseChange_isIso
  (lem-sc-proper-flat-image-global-hom-base-change-isIso): affine scalar extension
  of global Hom out of Rf_*M; no right adjoints or mate occurs.

Also proved AlgebraicGeometry.exists_mixedHomDirectImageComparison and
AlgebraicGeometry.mixedGlobalHomAdjunctionMap_isIso with no local holes.
There are no other sorries in the delivered Lean files. This is a decomposition
of the original theorem into two obligations, not a claim of an axiom-clean proof
of the target or positive net hole closure. Existing dependencies may still use sorry.

## No longer needed

Removed the item's direct proof imports of
Sheaf.AlgebraicGeometry.FlatPrecomposePus,
Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage, and
Sheaf.Algebra.Homology.BaseChangeRHomPerfect. The last two remain mathematically
needed and occur in the proof plan of the affine-image obligation; they are not
claimed pruned from the targets. The second reader restored these two plain proof imports in
ProperFlatImageGlobalHomBaseChangeIso, matching its still-open DAG proof plan.
They remain reachable; neither is claimed pruned from the targets.

The tied-universe route through lem-sc-flat-precompose-pus / FlatPrecomposePus,
lem-sc-global-hom-base-change-counit-transport / GlobalHomBaseChangeCounitTransport,
and lem-sc-global-hom-base-change-exchange / GlobalHomBaseChangeExchange is no longer
needed on this branch. Their role is replaced by the independent-universe transport
obligation and the proved mate equation. This does not assert that no other target
branch uses those modules. The global Hom adjunction node and its module remain needed
as the source of proved generic categorical helpers; they are not pruned.

All existing public imports of the item were retained, because its signature uses them.
No unused new proof import remains. The generic private internalHomMate_exists,
tensorAdjunctionCore and schemeHomTensorHom_naturality are accessed through import all;
no existing declaration's visibility was changed.

## Where the brief, the DAG or earlier work was wrong

The earlier blocked attempts accurately reported missing compiled artifacts and later
missing tracked source imports. On this retry the item, its node and the mixed dependency
sources are present. The previous scratch reduction has been copied into the delivery
only after checking the restored node, sources, signatures and compilation.

FlatPrecomposePus and GlobalHomAdjunctionIso use a common module/sheaf localization
universe, whereas the item has independent w and wA. Their concrete global comparisons
therefore do not specialize to this statement. The generic categorical helpers in
GlobalHomAdjunctionIso do specialize, and are used to prove the two mixed comparison
helpers. The remaining compatibility is isolated without adding a universe equality.

ProperSupportPerfectDirectImage requires chosen localizations on the open sites of
all schemes. The item provides open-site data only for X. ProperFlatDerivedDirectImagePerfect
also explicitly requires Y-open data. The affine-image obligation's natural-language
proof computes in standard localizations, then transports to the supplied derived
categories; it does not strengthen the original theorem with Y-open hypotheses.

Read Stacks Tags 0AA8 and 0B6I online, especially the right-hand-side computation and
final diagrams of 0AA8. Searched Mathlib with leanfinder, loogle, leansearch and grep;
leansearch reported Internal Server Error. The successful services return only generic
adjunction facts, including conjugateEquiv_counit, used in the main proof. Repository
search found no exact mixed-universe theorem. Blueprint searches for global Hom and
0AA8 found no imported blueprint statement matching the new interfaces.

Edge cases checked mathematically: the transport identity assumes only beta_M
invertible, and works for zero objects and identity arrows; no inverse of beta_N is
used. The affine-image result holds for M = 0, empty schemes, arbitrary K and nonflat g:
a bounded finite-projective source makes RHom base change invertible for every ring map.
The mixed adjunction result uses qcqs hypotheses exactly where the coherator is applied.
No false or weakened statement was substituted.

## New nodes

lem-sc-mixed-hom-direct-image-comparison records the proved fixed-data specialization
of the existing generic evaluation-mate construction. Its mate equation determines
the comparison uniquely. Module MixedHomDirectImageComparison.

lem-sc-mixed-global-hom-adjunction-isIso records the proved canonical counit-induced
global Hom map with independent localization universes. The argument uses the existing
sheaf-Hom/coherator theorem, global-sections detection and normalized mixed Leray.
Module MixedGlobalHomAdjunctionIso.

lem-sc-mixed-global-hom-base-change-counit-transport records the remaining comparison
compatibility for arbitrary derived morphisms. Its proof expands evaluation mates,
identifies tensor and Leray composition equations, uses the supplied counit square,
and cancels beta_M contravariantly. Module MixedGlobalHomBaseChangeCounitTransport.

lem-sc-proper-flat-image-global-hom-base-change-isIso records the remaining affine-image
comparison: proper-support perfect direct image, finite-projective RHom base change,
and identification with the canonical mixed comparison. This contains no adjoints a,a'
and is strictly smaller than the parent. Module ProperFlatImageGlobalHomBaseChangeIso.

All four nodes lie in dag/nodes/sec-picard-framework, inherit the parent's unit and
blueprint ancestor, and carry exact Lean signatures and the three search kinds.
No change record or forced adaptation was added.

## Second reading by P2

1. Compared every delivered module with the repository. Only the original item
exists there; its complete theorem signature is byte for byte unchanged, including
universes, hypotheses, conclusion and visibility. Its existing public imports and
docstring are unchanged. The other four modules and nodes are new. No existing
definition or statement changes and no change record is required. Verdict: pass.

2. Independently compiled all five modules in import order through lcompile.py.
Read the mate counit proof, the transpose/factorization proof and both proved
comparison helpers. The mate proof uses conjugateEquiv_counit, counit naturality
and the left triangle, and never inverts the right-adjoint base-change map.
The two local sorries are exactly the named obligations reported above; none is
in a definition. Scratch copies with #print axioms for the five public theorems
and all three new definitions compiled: only propext, Classical.choice,
Quot.sound and sorryAx from open dependencies occur. No forbidden declaration
keyword occurs. The internal Hom comparison is determined componentwise by
A = Rf_*RHom(L,M), alpha = identity in the mate equation and injectivity of the
tensor-Hom equivalence; its existence theorem is proved. Verdict: pass as a
decomposition, not as an axiom-clean theorem or positive net closure.

3. Read Stacks https://stacks.math.columbia.edu/tag/0AA8 and
https://stacks.math.columbia.edu/tag/0B6I. The affine-image obligation is the
right-hand-side perfect RHom computation; transport is the compatibility
calculation and does not assume the mate invertible. Both are strict parts of
the parent, with proof docstrings and matching nodes. Checked identity squares,
zero M, empty schemes and nonflat g: identity squares reduce to naturality,
zero/empty cases give zero maps, and finite projective source terms permit
arbitrary scalar extension. No boundedness of K is needed. Repeated leanfinder
with "perfect complex derived pushforward scalar extension commutes internal Hom",
loogle with "homEquiv_naturality_right", and grep with
"baseChange.*Hom|Hom.*baseChange|RHom.*[Pp]erfect"; results were generic Ext/adjunction
or unrelated base-change lemmas. Repository search found the tied-universe
exchange/transport and proper-flat perfect pushforward requiring Y-open data;
neither directly proves the mixed-universe obligations. No quick closure was
found. Verdict: pass.

4. Checked the route from the target through the proved global Hom adjunction,
affine-image comparison and counit square. The Mathlib mate identity is used
directly. All four old proof_deps are accounted for above: global Hom adjunction
remains as a provider of generic helpers, proper-support/perfect-RHom dependencies
remain under the new obligation, and the tied-universe flat-precomposition route
is replaced. The unit sk-thm-picard-duality has empty realized bindings; no unit
statement or step is replaced. The Stacks 0AA8 argument is retained. Verdict:
pass after restoring the affine-image module's two proof-plan imports.

5. Checked all five node signatures against Lean, sources, proof_origin,
creation records, chapter/unit and blueprint ancestry. Each proof_deps is the
union of its proof steps' uses. Only proof, proof_deps and proof_origin differ
on the existing node. Both holes have matching nodes; definitions introduce
no hidden holes. Verdict: pass.

Second-reading changes: restored plain proof imports
Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage and
Sheaf.Algebra.Homology.BaseChangeRHomPerfect in
ProperFlatImageGlobalHomBaseChangeIso; corrected the pruning report and appended
this independent review. No proof or statement needed repair. The ordinary
compile took 39.9 seconds for the main file; the scratch axiom compile took 41.3
seconds, both within the single-file limit.
