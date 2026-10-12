## What changed

Reduced the single sorry in `Sheaf.AlgebraicGeometry.FiniteUnramifiedOnePointClosed` to one strictly smaller, general geometric step: spreading a closed immersion of a finite fibre to a neighbourhood. The target declaration and all its binders are unchanged.

The two proved private helpers in the item show that stalks of an unramified scheme over a field are fields, and that the canonical `asFiberHom` is an isomorphism for a unique unramified fibre point. These use the existing, proved maximal-ideal mapping theorem in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`, Mathlib base-change stability, and the preimmersion properties of fibre maps. Mathlib's separability instance and `IsPurelyInseparable.surjective_algebraMap_of_isSeparable` prove the residue-field map surjective. Cancelling `asFiberHom` from the canonical factorization makes the fibre map a closed immersion. Applying the new general spreading theorem finishes the item.

Added the proof-only imports `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` and `Sheaf.AlgebraicGeometry.FiniteClosedImmersionNearFibre`. The latter publicly imports Mathlib's fibre definitions because its statement uses the fibre morphism. All public imports and public signatures of the item are unchanged. Updated the item node and proof docstring to reflect the actual proof. No definition, existing statement, or target statement was changed; no change record is needed.

Both delivered modules compile through `lcompile.py --all`. The local proof reduction is complete; the remaining sorry is the whole proof of the new public theorem. Searches found no existing neighbourhood-spreading statement. LeanSearch was unavailable (HTTP internal-server error); this is recorded as unavailable, with successful LeanFinder, Loogle, and source searches also recorded.

## Proved and sorry left

`AlgebraicGeometry.finite_unramified_one_point_closed` has no direct sorry: its proof combines the proved fibre identification, the existing residue-field facts, and the one pending spreading theorem. Its node is `lem-weil-pbc-finite-unramified-one-point-closed`. The private helpers `isField_stalk_of_unramified_over_field` and `isIso_asFiberHom_of_unique_unramified` are fully proved.

Exactly one sorry remains in the delivery: `AlgebraicGeometry.exists_isClosedImmersion_restrict_of_fiber`, in `Sheaf.AlgebraicGeometry.FiniteClosedImmersionNearFibre`, node `lem-weil-pbc-finite-closed-immersion-near-fibre`. It assumes only finiteness and a closed-immersive fibre, with no unramifiedness, unique point, or pure-inseparability hypothesis. It is steps 5–7 of the original proof, not a renaming or repackaging of the item. Its docstring and node give the full Nakayama/cokernel-support/localization proof.

## No longer needed

Removed the two proof imports `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen` and `Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`. Their nodes `lem-weil-pbc-unramified-base-change-open` and `lem-weil-pbc-unramified-algebra-over-field-product` are unnecessary for this proof: Mathlib base-change instances and the unramified stalk facts replace them.

The new route also does not use `lem-weil-pbc-fibre-ring-localization-quotient`, `lem-weil-pbc-prime-residue-field-algebra`, or `lem-weil-pbc-fibre-ring-residue-field-iso`; these Mathlib-leaf nodes are pruned from the item's route. No other modules are introduced for those steps.

For completeness, these old direct proof dependencies move into the spreading node, so remain transitively needed: `def-weil-affine-spectrum`, `def-weil-finitely-generated-module`, `def-weil-pbc-localization-at-prime`, `lem-weil-pbc-closed-immersion-affine-cover-criterion`, `lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-finite-module-support-annihilator`, `lem-weil-pbc-nakayama-local-generators`, `lem-weil-pbc-principal-localization-open-immersion`, `lem-weil-pbc-spec-residue-field-identification`.

The remaining original algebraic tools are retained where actually needed: affine spectrum, finite morphisms, Spec residue-field identification, affine fibre products, localization at a prime, finite modules, Nakayama, support/annihilator, principal-localization open immersions, and the affine closed-immersion criterion are dependencies of the new spreading node. They are not claimed globally unnecessary. The residue-field, purely-inseparable, separable, unramified, and closed-immersion definitions remain used by the item itself. No unit realization or chapter route is bypassed.

## Where the brief, the DAG or earlier work was wrong

There is no mathematical error in the original seven-step plan. Its product-of-fields computation is unnecessary: the existing formal-unramified stalk maximal-ideal theorem gives field stalks directly, and the canonical fibre map supplies the residue-field identification. The new spreading statement is exactly the last part of Stacks 04DG's proof, with the cokernel argument made explicit. Edge cases were checked: an empty fibre is allowed in the spreading statement and yields the same cokernel vanishing; no reducedness or finite-presentation hypothesis is required. In the item the chosen `x` ensures the fibre is nonempty. Both statements preserve their universe and allow arbitrary non-Noetherian bases.

The Stacks source files are not present in this clone; the original recorded proof was checked against the official Stacks Tag 04DG page. The public theorem's docstring was updated because the brief requires its recorded proof and DAG to agree with the proof written.

## New nodes

`lem-weil-pbc-finite-closed-immersion-near-fibre`, in `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-closed-immersion-near-fibre.json`, is realized by `AlgebraicGeometry.exists_isClosedImmersion_restrict_of_fiber` in `lean/Sheaf/AlgebraicGeometry/FiniteClosedImmersionNearFibre.lean`. It inherits the item's chapter/unit and records the nearest blueprint ancestor. It generalizes the Nakayama and spreading-out part of the existing 04DG proof. Blueprint/DAG searches found no equivalent existing node. There are no change records.

## Second reading by K2

1. Compared the complete item module with the repository version using `diff`. The existing theorem signature, from `theorem` through the text before `:= by`, is byte for byte unchanged. Its public imports remain unchanged; both added imports are proof-only. There are no changed definitions or undeclared statement changes. Verdict: pass.

2. Independently compiled both modules in import order with `lcompile.py --all`: no errors or warnings. Read both proofs and scanned the delivered sources: the only sorry is the whole proof of the named public spreading theorem, and no prohibited declarations or hollow definitions occur. Compiled a scratch copy with `#print axioms`: both private helpers use only `propext`, `Classical.choice`, and `Quot.sound`; the item and spreading theorem additionally use `sorryAx`, precisely for the reported pending lemma. The item's proof is a reduction, not an axiom-free completed theorem. Verdict: pass as a partial proof delivery.

3. Checked the split-off statement and its complete docstring proof against the final Nakayama/localization steps of https://stacks.math.columbia.edu/tag/04DG. A finite cokernel suffices over arbitrary non-Noetherian rings; no finite presentation or reducedness assumption is needed. Empty fibres give zero after residue-field tensoring and are covered by the same argument; closed immersions and the identity map give immediate sanity cases. The lemma omits all the item's unramifiedness, uniqueness and pure-inseparability assumptions and represents only the spreading part of the argument. New LeanFinder and Loogle queries using surjective residue fibres and cokernels returned the affine surjectivity criterion and finite-plus-mono criterion, not the desired neighbourhood theorem. Source searches in Mathlib, upstream and lean/Sheaf found no duplicate. Formalizing the general geometric spreading step is not a small repair. Verdict: pass; one genuine smaller obligation remains.

4. Read the proof from its conclusion upward. The proved upstream maximal-ideal mapping theorem and existing fibre/preimmersion machinery directly replace the unramified product-of-fields route; the residue extension is handled by the existing separable/purely-inseparable theorem. Both new imports are used, and both imports of pending old lemmas were removed. Compared all old and new proof dependencies and made the report explicit about those moved to the spreading node. Read `dag/units/sk-thm-p1.json`, including every `realized` entry: neither this item nor any pruned node realizes a unit statement or step, and this reduction changes only work below the unit level. The referenced literature `_section.md` is absent from this clone; the unit record contains its statement and steps. Verdict: pass.

5. Compared the two node records with the Lean declarations and proofs. The item's existing statement and statement dependencies are unchanged; its proof-dependency list is exactly the union of the new steps' uses. The new node records the precise signature, source, complete proof, creation metadata, blueprint ancestry, chapter/unit, and searches. Its proof dependencies are exactly the union of its steps' uses. The proof origins distinguish the implemented fibre reduction from the pending Stacks spreading argument. Verdict: pass.

Second reading changed only this report: added the review and explicitly enumerated the old direct dependencies retained through the new spreading node. No Lean proof, signature, import or node needed repair.
