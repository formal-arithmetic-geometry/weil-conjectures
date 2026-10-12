## What changed

Proved `CochainComplex.isKInjective_homComplex_of_isKFlat` in
`Sheaf.Algebra.Homology.KInjectiveHomComplex` with its original signature.
The proof uses K-flatness, the existing `homComplex_tensorTotal_iso`, the
proved global-cochain comparison, and Mathlib's `IsKInjective.eq_δ_of_cocycle`
and `Cochain.equivHomotopy`. It transports a cocycle through the tensor-Hom
isomorphism, obtains a degree-minus-one primitive, and transports it back.
The new proof import is `Sheaf.Algebra.Homology.HomComplexGlobalCochains`.
The node's proof and dependencies now describe this explicit argument.

Added the fully proved theorem `CategoryTheory.homComplex_global_cochains`
in that new module, with private proved factor-equivalence helpers.
It constructs the comparison using the product universal property,
`SheafOfModules.unitHomEquiv`, and `SheafOfModules.homObjSectionsEquiv`,
and checks the differential using the specified projection formula and
`Int.negOnePow_succ`. Its only proof import is `HomComplexProjections`.
No existing definition, signature, or public import was changed.

## Proved and sorry left

Closed the sole original hole:
`CochainComplex.isKInjective_homComplex_of_isKFlat`
(node `lem-pur-hom-kflat-into-kinjective`).
Added no holes. The new theorem `CategoryTheory.homComplex_global_cochains`
(node `lem-pur-hom-complex-global-cochains`) is fully proved.
No `sorry` remains in either delivered module.
The proof still depends on the existing unproved
`CategoryTheory.homComplex_tensorTotal_iso`
(node `lem-sc-derived-hom-tensor-total`), as intended by stage 3.
This delivery closes one hole and adds zero; it is not a decomposition.

## No longer needed

None of the original imports or planned dependency nodes is pruned.
All four original proof dependencies remain used. The naturality clause of
the tensor-Hom existence theorem is not needed, but its isomorphism is needed,
so its module remains. The localized Hom-complex comparison modules are not
imported: the direct global comparison needs no restriction functor, local
K-injectivity, or derived-category comparison.

## Where the brief, the DAG or earlier work was wrong

The DAG's third step called the global-sections/cohomology bridge elementary,
but the existing Hom-complex declaration provides only the sheaf-complex
projections and differential, not that bridge. This delivery proves the bridge
explicitly rather than assuming it or leaving another hole.
The literal local Stacks TeX file is absent on this machine; the corresponding
primary source was read at
[Stacks Section 0A8X](https://stacks.math.columbia.edu/tag/0A8X),
[global Equation 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z), and
[Lemma 0A96](https://stacks.math.columbia.edu/tag/0A96).
The global equation is the project server (0A8Z); equation the project server (0A8Y) concerns
sections over an object U. The delivered docstrings cite the global equation.
The unit `sk-def-sf-operations` has no realized statement or proof steps, and
its six-operation route is unchanged. `HomComplexProjections` is used as a
proved generic tool from another unit, solely to expose the product specification.

## New nodes

`lem-pur-hom-complex-global-cochains` records the fully proved global-cochain
comparison in `Sheaf.Algebra.Homology.HomComplexGlobalCochains`.
The statement applies to arbitrary complexes, with no acyclicity, K-flatness,
K-injectivity, boundedness or terminal-site-object hypothesis. It is strictly
the cochain-comparison step of the argument. Zero complexes give zero factors;
zero differentials give zero on both sides; unbounded families are products,
so no finite-support assumption is introduced. LeanFinder and local grep found
only the external Hom construction and factor equivalences; LeanSearch returned
an Internal Server Error, recorded as unavailable. No change record is required.

## Second reading by X2

1. **Interface preservation — pass.** Compared the delivered KInjectiveHomComplex
   module with the repository using diff: the full existing theorem signature is
   byte-for-byte unchanged, with the same site universes, commutative coefficient
   sheaf, arbitrary integer-indexed complexes, K-flat hypothesis and K-injective
   instance. No definition or existing public import changed. The new import is
   proof-only. HomComplexGlobalCochains is a new module; its public imports are
   needed by its statement, while HomComplexProjections is proof-only. No change
   record or forced adaptation is needed.
2. **Proof and trust — pass.** Independently compiled both delivered modules in
   import order with lcompile.py (9.6 and 9.5 seconds), without errors or warnings.
   Searched the Lean files for holes and forbidden declarations: none. Scratch
   copies with #print axioms show only propext, Classical.choice and Quot.sound
   for factorEquiv, factorEquiv_comp and homComplex_global_cochains. The original
   theorem additionally has sorryAx, from the already-open tensor-Hom theorem;
   this is explicitly retained, not a newly introduced hole. The new factor
   equivalence is concrete; its inverse uses the product universal property of
   the proved homComplex_projections_exists, not an arbitrary witness of an
   unproved existence statement. The main proof eliminates the existential
   tensor-Hom theorem inside a theorem proof and introduces no data definition.
3. **New statement and edge cases — pass.** No statements were split off with
   sorry. The new, fully proved theorem is exactly the global-cochain comparison
   step, strictly smaller than K-injectivity and valid for arbitrary A and B.
   Read the product lift, both inverse laws and the signed differential check.
   Negative degrees use Int.negOnePow_succ; unbounded degrees use products with
   no finite-support restriction. Zero complexes have zero cochains, and zero
   differentials kill both differential terms. No terminal site object is used:
   unitHomEquiv represents global sections on a general site. Independent
   LeanFinder search for morphisms from the unit sheaf to product internal Hom
   complexes found unitHomEquiv and external single-complex/cochain results,
   but no such comparison. Independent msearch grep and local rg found no
   usable duplicate. HomComplexSectionsCochains is localized at U, remains
   open, and imports RhomIntoKInjectiveLocal, which depends on this item; it
   cannot replace the comparison here. Checked the primary Stacks sources
   [0A8Z](https://stacks.math.columbia.edu/tag/0A8Z) and
   [0A96](https://stacks.math.columbia.edu/tag/0A96): the global comparison and
   tensor-Hom argument match the recorded route.
4. **Route and pruning — pass.** Read from the K-injectivity constructor down:
   K-flatness gives acyclicity of T, the existing tensor-Hom isomorphism carries
   the degree-zero cocycle, Mathlib eq_δ_of_cocycle gives its primitive, and
   equivHomotopy gives the required null homotopy after transport back. The
   comparison uses existing factor equivalences and product projections; no
   shorter existing global comparison was found. All original four dependency
   nodes remain used, so No longer needed is complete (none). Read the unit
   sk-def-sf-operations: realized.statement and realized.steps are empty and
   steps is empty; this supporting argument changes no six-operation route.
5. **Nodes and Lean — pass.** Diff of the existing node changes only proof,
   proof_deps and proof_origin. Their union records exactly K-flatness, Hom
   complex, K-injectivity, tensor-Hom and the new comparison. The new node has
   the required statement dependencies, source, proof steps, searches, origin,
   creation, blueprint provenance, chapter/unit and Lean record. Its verbatim
   Lean statement and differential clause match the module. The helper
   calculations and global comparison are proved; no missing hole node exists.

Second-reading changes: appended this independent review and recorded the
additional searches; no Lean proof, interface, import or DAG repair was needed.
