Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-sheaf-hom-is-sheaf.json` — statement split, 2 new dependencies.
- `citations.json` — verbatim statement quotes for every cited step.

Attachments: none.

WANTED: none.

## Not duplicates

lem-pur-sheaf-hom-cover-gluing vs lem-pur-sheaf-hom-is-sheaf: the new node treats one fixed covering family and only the local gluing assertion; the item quantifies over all objects and additionally asserts the presheaf structure, sheaf structure, localized sections, and Γ(O)-linear global correspondence.
lem-pur-sheaf-hom-cover-gluing vs def-pur-sheaf-hom: the new node is a standalone fixed-cover gluing theorem, while the definition node packages the full internal-Hom presheaf and its global-sections theorem (and cannot be cited here because it depends on the item).

The prior attachment was insufficient because `SheafOfModules.homObjSectionsEquiv` is an unstructured equivalence and does not state Γ(O)-linearity. No child node is needed: the existing definition node states the sheaf and global-sections bijection, while Γ(O)-linearity follows by the pointwise scalar formula in the existing Hom-module definition.

## Review by C1

I read the item source in `literature/stacks-project/sites-modules.tex`: Section 04TT defines the localized Hom presheaf and its O-action, Lemma 03EM supplies the sheaf gluing assertion, the internal-hom restriction lemma gives compatibility under relocalization, and Section 03DD supplies the global-sections module structure. The definitions cited in steps 1 and 3 were opened and checked: `def-pur-sheaf-hom` states exactly the presheaf and restriction rule, `def-pur-sheaf-modules-hom-module` states the Γ(C,O)-module action on Hom, and `def-pur-localized-ringed-site` states restriction and relocalization.

Step 1 uses only those two definition statements and is a direct pointwise construction. Step 2 cites the existing `def-pur-sheaf-hom` statement, which explicitly says the presheaf is a sheaf of O-modules. Step 3 uses only the localization/relocalization statement; identifying sections over the final object is the one-line definition of global sections. Step 4 constructs the inverse restriction/gluing maps directly from compatible families and morphisms of sheaves, then applies the pointwise scalar formula in `def-pur-sheaf-modules-hom-module`; this proves linearity without introducing a child restatement.

I searched the whole DAG and blueprint for internal-Hom sheaf, `04TT`, `03EM`, and global-sections linearity. The source Lean file was also read: `PresheafOfModules.isSheaf_homObj` proves only a sheaf property for the internal-hom object, while `SheafOfModules.homObjSectionsEquiv` is an ordinary `Equiv`; neither proves the required global scalar linearity. The item’s recorded Mathlib searches returned only Type-valued `CategoryTheory.sheafHom`/`Presheaf.IsSheaf.hom`, no O-linear module theorem; LeanSearch was unavailable and recorded as such. Small checks: on a one-object site the construction reduces to the ordinary module Hom with scalar multiplication; on the empty site both section families and morphisms are singleton, so the bijection and linearity are trivial.

## Second reading by C1

- Step 1 checked against Stacks 04TT and `def-pur-localized-ringed-site`/`def-pur-sheaf-modules-hom-module`; verdict: elementary pointwise construction and correct citations.
- Step 2 checked against Stacks 03EM and `lem-pur-sheaf-hom-cover-gluing`; verdict: fixed-cover gluing gives exactly existence and uniqueness, with O-linearity local.
- Step 3 checked against the restriction lemma and `def-pur-localized-ringed-site`; verdict: final object and relocalization give the localized-sections identification.
- Step 4 checked against Stacks 04TT/03DD and the two cited node statements; verdict: compatible-family inverse and pointwise scalar linearity are explicit.
- `lem-pur-sheaf-hom-cover-gluing` checked B1-B7 against 03EM/04TQ, its definitions, blueprint metadata, and recorded searches; verdict: valid smaller unsplit dependency, with no duplicate or exact Mathlib match.
- `lem-pur-sheaf-hom-is-sheaf` checked hypothesis by hypothesis against 04TT, 03EM, and the restriction lemma; verdict: statement matches all four clauses, including one-object and empty-site cases.

Changes: corrected the item node’s `created.item` metadata; added this second-reading record. No mathematical statement or proof step required repair.
