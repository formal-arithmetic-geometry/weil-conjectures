## What changed

`AlgebraicGeometry.coherentFormalModule_kernel` is reduced to the stabilized-image construction and proved factorization. The item proves the zero composite, monicity from eventual component-kernel vanishing, and uniqueness by cancellation. Its existing signature is unchanged.

Repair of the current return: removed the three duplicate private theorems `multiplication_naturality`, `idealModuleProduct_comp_zero_iff`, and `idealModuleProduct_quotient_comp_zero_iff` from `CoherentFormalModuleKernelFactorization`. That module already publicly imports `CoherentFormalModule` for its statements; it now also uses a proof-only `import all Sheaf.AlgebraicGeometry.CoherentFormalModule` to access the existing private quotient-annihilation theorem. The `formalDescent` proof applies that existing theorem. No existing module is adapted and no visibility or statement changes. All three sandbox modules compile with `lcompile.py --all`.

## Proved and sorry left

Closed the item's one original hole: `AlgebraicGeometry.coherentFormalModule_kernel`. Also proved: `AlgebraicGeometry.coherentFormalModule_kernel_factorization` and `AlgebraicGeometry.formalTransition_epi`.

Added one strictly simpler construction hole: `AlgebraicGeometry.coherentFormalModule_kernel_construction`, node `lem-weil-pbc-formal-kernel-construction`. This is a decomposition: one original hole closed and one lower hole added, with zero net reduction. This construction theorem is the only `sorry` left in the delivery.

## No longer needed

Removed the factorization module's proof import `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`; the proof now reuses the existing quotient-annihilation theorem instead of rebuilding its monoidal argument. Removed the three duplicate private helper declarations named above. The earlier duplicate transition-epimorphy helper in the item remains removed; the item uses `formalTransition_epi` from the factorization module.

Removed the redundant `public import Mathlib.CategoryTheory.Abelian.Basic` from both new modules; their statement dependencies already expose it through `CoherentFormalModule`.

The original item no longer directly uses these old `proof_deps`: `lem-weil-pbc-adic-completion-noetherian`, `lem-weil-pbc-affine-tilde-gamma-adjunction`, `lem-weil-pbc-artin-rees`, `lem-weil-pbc-coherent-formal-modules-affine`, `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`, `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`, `lem-weil-pbc-quasi-coherent-module-cokernel-image`, `lem-weil-pbc-quasi-coherent-module-kernel`, and `pqf-def-locnoeth`. They remain needed indirectly for the construction or the underlying scheme/module notions. No original DAG dependency node or module is pruned: the construction module retains the affine and Artin–Rees dependencies, and the factorization module still needs the formal-module definition and ideal-power factorization theorem. No new node is needed for this repair.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified three lemmas already proved word for word in `CoherentFormalModule`. The previous reading missed these private declarations. Ordinary imports do not expose them; Lean's proof-only `import all` makes the existing quotient-annihilation lemma available without changing its visibility. The repaired proof reuses it, and the two other duplicates are unnecessary.

The original plan bundled the affine Artin–Rees construction and categorical universal property. The existing split retains the construction and unit route while proving factorization and uniqueness directly. The factorization node's proof now records reuse of the existing private lemma.

## New nodes

`lem-weil-pbc-formal-kernel-construction`: stabilized images, coherent quotients, inclusion equations, and eventual component-kernel vanishing, from claims (a)--(c) of Stacks Lemma 087X. Its named construction theorem remains `sorry`.

`lem-weil-pbc-formal-kernel-factorization`: existence of factorization through the constructed system, from claim (d) of Stacks Lemma 087X; fully proved in `CoherentFormalModuleKernelFactorization.lean`. No additional nodes or change records were added by this repair.

## Second reading by M2

1. Compared every delivered module with the repository: the two helper modules are new, and the existing `coherentFormalModule_kernel` signature is byte-for-byte identical. No existing definition, visibility, or target changed; no change record or forced adaptation is needed. The existing node changes only its stage-3-owned proof fields.

2. Compiled all three files in import order using `lcompile.py --all`, without errors or warnings. Scanned for forbidden declarations and hollow definitions: none. The sole explicit `sorry` is the named `coherentFormalModule_kernel_construction`. Checked `#print axioms` in a scratch copy for the original theorem, construction, factorization, transition epimorphy, and private monicity helper; only the allowed standard axioms and the reported `sorryAx` from open statements occur. Local choices in the factorization proof select proved factorizations inside a theorem; no definition selects an arbitrary witness from an unproved existence assertion.

3. Read both new statements and the full construction docstring against [Stacks Lemma 087X](https://stacks.math.columbia.edu/tag/087X). The construction omits the universal property and adds precisely the Artin–Rees vanishing needed to prove monicity; the proved factorization theorem omits uniqueness and does not assume componentwise injectivity. These are proper parts of the argument, not a restatement under another name. Checked the indexing `op n = level n+1`: stabilized images have sections L/(L ∩ I^(m+1)M), and their shifted quotient is L/I^(n+1)L. The kernel at n+c is killed on transition to n by the same bound. Zero morphisms and identity morphisms allow c=0; I=0 gives constant systems, I=O_X forces zero terms, and the empty scheme causes no exception. The inclusion (x) ⊂ k[[x]] shows why componentwise injectivity must not be assumed and why a positive shift can be necessary. Independent searches with LeanFinder (uniform eventual kernel vanishing), Loogle (`kernel.ι, Epi`), the grep service, and `rg` over both library roots found generic kernel/completion tools, not this construction. Read the existing private ideal-product quotient lemma: the repaired proof reuses it through proof-only `import all` and introduces no duplicate. The remaining affine construction is substantial and was not closed in this reading.

4. Followed the proof top down: construction, zero composite by image and quotient cancellation, factorization by successive quotient descent, and uniqueness by eventual kernel vanishing and cancellation. No shorter existing formal-system theorem was found. Retained the planned imports for the open construction and removed two redundant public Mathlib imports from the new modules. Listed all nine replaced direct dependencies above; each remains needed indirectly, so no original module is claimed pruned. Read `dag/units/sk-thm-p1.json`, including `realized`: this kernel lemma lies below the unit's stated steps, and the affine/Artin–Rees route is retained; the unit record needs no change.

5. Checked the three node records against Lean, including exact normalized theorem signatures, the union of every proof step's `uses`, sources, proof origins, and required new-node fields. The construction node retains the old mathematical dependencies, the factorization node records the existing ideal-power theorem and private quotient lemma, and the original node records the two new parts plus the formal-module tool. Verdict: consistent.

Second-reading changes: removed redundant `public import Mathlib.CategoryTheory.Abelian.Basic` from the construction and factorization modules, normalized extra blank lines, and completed the pruning and independent-review report. No proof or statement required repair. One original hole is closed and one construction hole added: this remains a decomposition with zero net hole reduction.
