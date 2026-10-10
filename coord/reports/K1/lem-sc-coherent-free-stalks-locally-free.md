Files written:

- `dag/nodes/sec-picard-framework/lem-sc-coherent-free-stalks-locally-free.json`: statement node split into three proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-affine-finite-module-free-locus.json`: new unsplit statement node; Mathlib searches found only affine ingredients, no exact match.
- `citations.json`: verbatim citations for every non-elementary dependency in the proof steps.

Attachments: none.

WANTED: none.

The item had no Lean declaration tagged with its id and no sorry-free declaration in the source stating the sheaf theorem. I searched the whole DAG and blueprint for Tag 0GWM, the free-locus criterion, and the relevant key words; the existing coherence characterization `pqf-lem-coherent-ft-locnoeth` was reused rather than duplicated. The new node is strictly smaller: it is the affine module statement used to pass from free stalks to principal-open free localizations. The item keeps the source's hypotheses (locally Noetherian scheme and coherent module) and conclusion (finite locally free).

## Review by K1

I read the item's imported source at Stacks Tag 0GWM and the blueprint paragraph under `lem-sc-riemann-roch`, and checked the existing `pqf-lem-coherent-ft-locnoeth` statement before citing it. Step 1 uses exactly that node's equivalence (coherent implies quasi-coherent of finite type) and `pqf-def-locnoeth` for Noetherian affine opens; the affine restriction is then a finite module. Step 2 uses the new node's explicit hypothesis and conclusion: every prime localization is finite free, so finitely many principal opens cover the affine and the localized modules are finite free. Step 3 is elementary unpacking of the definition of finite local freeness and the fact that affine opens cover a scheme.

For the new node I searched the entire DAG and blueprint before writing it. Its source is Tag 0GWM, with Tag 01XZ supplying the finite-presentation passage on Noetherian affines. LeanSearch returned a service error; LeanFinder found `Module.FinitePresentation.exists_free_localizedModule_powers`, `Module.mem_freeLocus`, and `Module.freeLocus_eq_univ_iff`; Loogle found only generic `Module.FinitePresentation` declarations; and a direct Mathlib grep found the same affine ingredients but no sheaf theorem. I recorded these searches in the node and tested the statement on $M=A^r$ (all localizations free) and $M=0$ (rank zero), while a non-free ideal at a singular point correctly fails the hypothesis. I corrected the imported item by adding the missing affine criterion dependency, explicit uses, proof origin, blueprint metadata, and verbatim citation entries.

What remains unfinished is only the independent maintainer review; no mathematical dependency was left uncited in the split.
