Files written:

- `dag/nodes/sec-picard-framework/lem-sc-sheaf-ext-coherent.json`: repaired item with affine-local proof; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-rhom-qcoherent.json`: statement-only Stacks 0A6A/08DL input; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-ext-noetherian-finite.json`: statement-only Algebra `lemma-ext-noetherian` input; no Mathlib match.

Attachments: none.

WANTED: none.

The returned split was wrong because `lem-sc-derived-internal-hom-coherent` merely restated the item after unfolding sheaf Ext. I deleted it. The proof now follows the requested affine route and does not use that node.

## Not duplicates

lem-sc-affine-rhom-qcoherent vs lem-sc-coherent-affine-free-resolution (00LP): the existing node supplies a finite-free resolution, while this node identifies affine sheaf RHom cohomology with the associated Ext sheaf.

lem-sc-affine-rhom-qcoherent vs lem-weil-pbc-finite-free-resolution-noetherian (00LP): the existing node is the resolution existence statement, while this node is the derived sheaf-to-module comparison.

lem-sc-affine-rhom-qcoherent vs lem-weil-pbc-minimal-finite-free-resolution-local (00LP): the existing node is a minimal local resolution, while this node computes affine RHom cohomology.

lem-sc-affine-rhom-qcoherent vs lem-sc-ext-locally-free-second-naturality (06XR): the existing node concerns naturality for locally free Ext, while this node gives the affine derived-Hom identification.

lem-sc-affine-rhom-qcoherent vs def-sc-ext-sheaf (06XR): the existing node defines sheaf Ext, while this node computes it on an affine from module Ext.

lem-sc-affine-rhom-qcoherent vs lem-sc-derived-hom-projective-resolution (06XR): the existing node computes derived Hom via projective resolutions, while this node states the resulting affine sheaf comparison.

lem-sc-affine-rhom-qcoherent vs lem-weil-pbc-ext-via-injective-resolution (06XR): the existing node computes Ext via injective resolutions, while this node identifies affine sheaf RHom cohomology with module Ext.

lem-sc-affine-rhom-qcoherent vs lem-sc-rhom-cohomology-ext-ring (0A64): the existing node identifies ring RHom cohomology with Ext, while this node includes the affine scheme and associated sheaf.

lem-sc-affine-rhom-qcoherent vs lem-sc-ext-stalk-localization (0A64): the existing node is a stalk localization theorem, while this node is the affine global associated-sheaf calculation.

lem-sc-affine-rhom-qcoherent vs lem-sc-derived-internal-hom-restrict-open: the existing node only states that derived internal Hom commutes with restriction to an open; the new node states the affine computation of its cohomology as the associated sheaf of module Ext for finite modules.

lem-sc-ext-noetherian-finite vs lem-sc-derived-internal-hom-restrict-open: the new node is a finiteness theorem for module Ext over a Noetherian ring, while the existing node is a sheaf restriction isomorphism.

## Review by K1

I read the item source context in Stacks `perfect.tex`, including Tags 0A6A and 08DL, the affine coherent-module criterion in Tag 01XZ, and Algebra `lemma-ext-noetherian`. I also read the existing `def-weil-pbc-sheaf-ext` definition. Step 1 uses the locally Noetherian affine cover and the coherent-module affine presentation; the hypotheses supply Noetherian A and finite M,N. Step 2 cites the new affine RHom node verbatim, including its equality with the associated sheaf of module Ext. Step 3 cites the new finite-Ext node verbatim, then uses the existing sheaf Ext definition to identify the local cohomology sheaf with the asserted sheaf Ext and the existing coherent definition for the conclusion. I checked the small cases q=0 and the zero module case: they reduce respectively to Hom and the zero coherent sheaf. The obsolete derived-internal-Hom restatement and all citations to it were removed.

## Second reading by K1

- Item statement: checked against Stacks Tag 0D0C; locally Noetherian, coherent inputs, all integer degrees, and coherent SheafExt conclusion agree.
- Step 1: checked against Tag 01XZ and the definitions of locally Noetherian and coherent; the affine finite-module presentation and Noetherian ring hypothesis are cited.
- Step 2: checked against Tags 08DL, 00LP, 0A64, and 06XR; the earlier 0A6A citation was incorrect because 0A6A is base-change RHom, so the source and argument were repaired.
- Step 3: checked against Algebra `lemma-ext-noetherian`, Tag 01XZ, and the SheafExt definition; finite module Ext gives a coherent associated sheaf on every affine.
- `lem-sc-affine-rhom-qcoherent`: statement is self-contained, TeX-complete, and tested at q = 0 and zero modules; searched LeanFinder, Loogle, and grep with no Mathlib match.
- `lem-sc-ext-noetherian-finite`: statement is self-contained and tested for q = 0 and zero modules; searched LeanFinder, Loogle, and grep with no Mathlib match.

Changes: corrected the RHom source tags, removed an invalid coherent-definition citation from finite module statements, added the missing coherent dependency to Step 1, repaired TeX and citation quotes, and recorded the source correction.
