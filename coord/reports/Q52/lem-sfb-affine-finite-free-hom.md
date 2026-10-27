## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-finite-free-hom.json`: split into seven explicit steps, reusing existing Mathlib leaves and definitions. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statements for all 25 step citations.

## Attachments

None. Searched the project Lean sources for the item id, relative Hom, Weil restriction and finite-free Hom constructions. The finite-free internal-Hom results are about module sheaves, not morphisms between affine schemes, and the Hilbert representability declarations state other functors.

## WANTED

None. The item's source, Stacks `more-morphisms.tex`, Tag 05Y6 (`lemma-hom-from-finite-free-into-affine`), is present and was read including its proof. Its preceding `equation-hom-functor` defines the functor being represented.

## What needed correction

The item had no proof. Its statement is correct, including arbitrary C and rank zero, and was preserved. The source proof says “Some details omitted”; the split supplies both inverse maps, naturality, and reduction to affine tests by open gluing rather than asserting that affine tests suffice without explanation. Instead of assuming a finite presentation of C, step 1 chooses variables for every element of C and all relations in the evaluation kernel.

The current blueprint unit and direct-image proof were read under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. The inherited prerequisite chain points through the older detailed direct-image argument, while the current blueprint's paragraph (3) uses compactification. This split only proves its assigned generic affine prerequisite; it does not change the unit route or any ancestor. `blueprint.from.node` is already null in the live item and `blueprint.from.place` already contains its full supporting chain; both are retained. Whole-blueprint searches for “hom-from-finite-free”, “relative morphisms”, “finite free affine”, “affine duality”, “finite free”, and “polynomial”, together with DAG searches, found no alternate blueprint node stating this item. `same_as` remains empty.

## Unfinished work

None for this one-level split. No Lean files were written and no compiler, Lake or build tool was run.

## Not duplicates

No new node was created. Existing `lem-weil-pbc-free-module-base-change-free`, `lem-weil-pbc-fibre-product-affine-spectra`, and `lem-weil-pbc-scheme-morphism-gluing` provide the substantive auxiliary results. The polynomial, algebra quotient, affine spectrum and tensor universal-property nodes supply exactly the other operations used. Thus no new coefficient lemma, algebra-presentation lemma, or sheaf-on-affines lemma is needed: their short special arguments are written directly in the steps.

## Review by Q52

I read Stacks Tag 05Y6 in `more-morphisms.tex`, from the definition of the relative morphism functor through the last paragraph of its proof. I also read Tag 01I4 (`lemma-fibre-product-affine-schemes`) in `schemes.tex` for the affine tensor formula, the scheme-gluing section, and every cited DAG statement. The source's universal map has a target base-changed over the base; composing with the target projection is exactly the item’s map to Y over T. The outer S-structure is retained by composing the representing scheme's T-structure with T to S, then taking a disjoint union of the fibrewise bijections over all a:U to T.

Step 1 uses the free-module definition to fix the given basis, the polynomial universal property to define evaluation, and the quotient definition for its surjection and kernel. The presentation is proved explicitly by the inverse on cosets; no first-isomorphism or finite-generation theorem is hidden. Step 2 uses the actual tensor-algebra universal-property statement, not just the module tensor definition, to give a commutative algebra as evaluation target. The base-change-basis node explicitly gives the basis 1 tensor e_j for arbitrary P; this supplies the unique coefficients. Affine spectrum supplies M and its structural map. All rings here are commutative and unital, as the cited statements require.

Step 3 uses polynomial uniqueness, the tensor algebra map and the same base-changed basis for arbitrary A. It writes the vanishing criterion coefficient by coefficient; it uses no flatness of A. The generator criterion for J is justified by finite sums of ideal generators. Step 4 spells out quotient descent as a well-defined formula on cosets, and obtains the inverse from unique coefficients. Its cited quotient node says the quotient map is surjective with exactly the given ideal as kernel, which is precisely what the coset argument needs. Natural transformation compatibility is checked with the formula t(alpha_ij), not left as an unstated comparison lemma.

Step 5 uses the affine fibre-product node's exact projection-compatible isomorphism and the affine-spectrum node's bijection on morphisms. The tensor pushout statement gives the uniqueness of the map induced by t on the first tensor factor. The universal map is then pulled back using the fibre-product definition, so naturality is available before any gluing. Step 6 uses the morphism-gluing node, whose statement expressly supplies both existence and uniqueness on arbitrary open covers. On overlaps I take an affine open refinement; I never assume an intersection of affine opens is affine or that U is separated. The same gluing uniqueness compares both maps into T and maps from U times_T Z into Y. Base change of an open cover is a cover: these are the inverse-image opens under its projection, and fibre products with the opens are those restrictions by their universal property. This elementary observation is written in the step.

Step 7 identifies S-morphisms with T-morphisms separately for each composite a. The fibre-product definition gives the stated restriction maps. For rank zero, the free-module definition makes B zero, the polynomial ring has no a-variables, and J has no generators, so D=R. The fibre product is empty on affine charts by the cited tensor formula and hence empty globally; the unique map out of the empty scheme yields F(U)=Mor_S(U,T). This agrees with M=T. For m=1 and B=R the equations recover C, as expected for Hom_T(T,Y). With C=R there are no effective restrictions and D=R, so the functor is terminal over T. With C=0 and positive rank over a nonzero base, the relation 1 is imposed coefficientwise and the solution locus correctly excludes any chart where B remains nonzero. Infinite I and K cause no infinite sums: each polynomial and each ideal expression has finite support, and only the fixed finite basis is summed.

I checked delivery-errors B–E: the statement is unchanged and self-contained, all non-elementary inputs already have nodes, each citation was read for the exact claim taken from it, and no clause is moved to a new node. None of the seven steps exceeds 2000 characters. All cited statements are Mathlib leaves or definitions, so no off-unit theorem or route replacement needs a tool-use declaration. The recorded searches were genuinely run with msearch.py; the item’s earlier searches were retained, and the new searches and their hits were read. AffineSpace.homOverEquiv (AffineSpace.lean:153) represents tuples of sections, tensorModelOfHasCoeffsHom (Presentation/Core.lean:152) descends a given algebra presentation along its coefficients, and LocalRepresentability.isRepresentable (Sites/Representability.lean:210) requires a pre-existing open atlas; none states this finite-free relative Hom theorem. No service failure was recorded as absence. The report and citations describe my own source and statement review, with the maintainer's independent review still required.
