1. Files written

- `dag/nodes/sec-picard-framework/lem-sc-finite-sheafhom-affine-adjoint.json`: statement, split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-finite-sheafhom-affine.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-derived-adjunction-from-underived.json`: statement, Mathlib leaf `CategoryTheory.Adjunction.derived`.
- `citations.json`: verbatim quotes for every cited node at every proof step.

2. Attachments

None. No project declaration tagged `lem-sc-finite-sheafhom-affine-adjoint` exists in `WeilConjectures/`, and the source declaration is not present without `sorry`.

3. WANTED:

None. The Stacks source used for the split is available in the local review copy at `/home/ubuntu/c1-stacks-review/duality.tex`; the project literature index identifies the same Tags 0AX2 and 0AX3.

4. What was wrong or incomplete

The imported item had an empty proof despite stating a derived adjunction and its counit. The source proof has two nontrivial ingredients: the underived affine sheaf-Hom adjunction (Tag 0AX2, `lemma-compute-sheafhom-affine`) and passage to derived functors (Tag 0AX2, `lemma-sheafhom-affine-adjoint`). I created the first as a project-specific unsplit node because no DAG node or Mathlib declaration gives the sheaf-Hom formula. The second is stated by Mathlib's general `CategoryTheory.Adjunction.derived` (Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:144), so it is a Mathlib leaf. The final step records that the derived counit is induced by the underived evaluation counit, as stated in the source's affine calculation and Tag 0AX3 remark.

5. What I could not finish

Nothing. The item is fully split and all cited statements are quoted verbatim in `citations.json`.

## Not duplicates

lem-sc-finite-sheafhom-affine vs lem-sc-finite-twisted-inverse-bounded-below: the new node states the underived affine sheaf-Hom restriction adjunction and its section formula, while the existing node states bounded-below cohomological behavior of the twisted inverse image.
lem-sc-finite-sheafhom-affine vs lem-sc-finite-pushforward-derived-hom-qcoherent: the new node states the underived adjunction and evaluation counit, while the existing node states quasi-coherence and boundedness of a derived internal Hom under finite pushforward.
lem-sc-finite-sheafhom-affine vs lem-sc-finite-duality-derived-hom: the new node is the underived affine calculation used as an input, while the existing node is the full finite Grothendieck-duality comparison identifying a different derived object with derived Hom.

## Review by F1

I read the item, its ancestor `lem-sc-finite-duality`, the related derived-Hom item, and the Stacks proof around Tags 0AX2 and 0AX3. I checked that the affine hypothesis supplies the sectionwise ring/module situation used by `lemma-compute-sheafhom-affine`, and that the item dependencies define the derived category and derived internal Hom. Step 1 cites the new underived node, whose statement explicitly gives the right adjunction, affine section formula, and unit evaluation. Step 2 cites that node and the derived-adjunction leaf; the Mathlib declaration is the general construction of an adjunction from absolute left/right derived functors. Step 3 cites both statements and is the direct compatibility of the derived counit with the underived evaluation map at 1. I searched the whole DAG and blueprint for duplicates and searched the project source for the blueprint tag; no exact declaration or existing node was found. I also checked the small cases conceptually: for f the identity, the sheaf-Hom is the identity and evaluation at 1 is the identity counit; the derived statement then reduces to the identity adjunction.

## Second reading by F1

- Item statement: checked against Tags 0AX2 and 0AX3, especially `lemma-sheafhom-affine-adjoint`; repaired the source orientation to `f : Y -> X`, the schemes hypothesis, and the `O_X`/`A=f_*O_Y` module categories.
- Step 1: checked against `lemma-compute-sheafhom-affine` (Tag 0AX2) and the underived node; the affine restriction/sheaf-Hom adjunction is cited with its section calculation.
- Step 2: checked against `lemma-sheafhom-affine-adjoint` (Tag 0AX2) and `Derived Categories, lemma-derived-adjoint-functors`; derived internal Hom is the right derived extension and the direction now matches the item.
- Step 3: checked against the affine section calculation and the derived-adjunction construction; expanded the module-level evaluation argument and marked the step non-elementary.
- `lem-sc-finite-sheafhom-affine`: checked against Tag 0AX2 hypothesis by hypothesis, including affine opens and the `Hom_R(S,F(U))` formula; no duplicate found in the DAG or Mathlib.
- `lem-sc-derived-adjunction-from-underived`: checked against the cited Mathlib declaration and its derived-category hypotheses; recorded semantic and source searches.
- Changes: corrected the item orientation and module base, replaced the unsupported elementary counit assertion with an explicit affine calculation plus derived natural-transformation argument, and updated the matching citation quote.
