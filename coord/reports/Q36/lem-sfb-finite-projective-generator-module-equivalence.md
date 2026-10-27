# Worker report: lem-sfb-finite-projective-generator-module-equivalence

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-projective-generator-module-equivalence.json`: item split into seven proof steps; statement unchanged; no exact Mathlib match for the item.
- `citations.json`: ten step-to-node citations, each checked against the verbatim statement in the shared repository.
- `searches.jsonl`: actual searches made with the required msearch command; the item retains its inherited search records and adds this worker's searches.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. The existing general results suffice: `lem-sp-exact-functor-preserves-homology`, `lem-trf-vector-space-quotient-dimension`, and `lem-trf-fully-faithful-ess-surj-equivalence`. In particular, no node restates fullness or essential surjectivity, and no separate node is made for a matrix calculation or a finite-presentation construction that takes three lines from the cited finite-dimensional-subspace result.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for finite/projective-generator, projectiveGenerator, projective_generator and Morita terminology. The project has no declaration stating this item. A derived-category unit discussion mentioning a finite projective generator and the unrelated Brauer-group Morita comment are not attachments.

## WANTED

None. Milne's book is present locally and its printed p.177 (PDF p.189) was read in full, together with the surrounding reconstruction discussion on pp.176–178. Stacks and the relevant Mathlib source files are available.

## Corrections and scope

The item was statement-only in the live repository and the sandbox had only dispatcher markers, so there was no earlier split to dry-run or overwrite. Retained the complete statement, source, inherited provenance chain, original searches, chapter and unit. No released repair note exists for this item. The latest blueprint's unit and direct-image proof (3) were read; this item is a remote prerequisite deep in that route, not the key statement of the unit, so no unit realization is changed. Its inherited `blueprint.from.node = null` comes from the imported ancestor chain and was not replaced by an invented blueprint id. Its `from.place` is already explicit and retained; `same_as` is empty after whole-blueprint searches.

Milne's text says that every categorical object has a finite presentation immediately after constructing the essential-image objects. Essential surjectivity alone would not justify that sentence for a categorical object before fullness is known. Step 6 supplies the needed independent argument: choose an epimorphism q from a finite sum of P; write q as the cokernel of d using abelianity; cover the domain of d by another finite sum and cancel that epimorphism in the cokernel universal property. There is no circular use of the equivalence.

No statement dispute. Milne's extra compatibility with a separately specified fibre functor is outside this item's statement; the present hypotheses state exactly the projective-generator data his proof uses.

## Mathlib and duplicate searches

Ran LeanFinder, Loogle, LeanSearch and source grep using msearch; read the actual returned hits. Repeated the search for the item with the alternative formulation “The Hom functor from a projective generator with finite dimensional endomorphism algebra is fully faithful and essentially surjective onto finite dimensional right modules”. Read `CategoryTheory/Abelian/Yoneda.lean:38–65`: its fullness theorem needs each X to be an epimorphic image of P itself, and does not prove finite-dimensional essential surjectivity. Read `RingTheory/Morita/Basic.lean:14–35,54–60`: the projective-generator characterization is explicitly TODO; the matrix result concerns a different setting. The Freyd–Mitchell hits embed in modules over another ring; the Grothendieck-category adjunction hits assume colimits absent here. None is an exact or one-line match for this item.

For finite presentations, read `Algebra/Module/FinitePresentation.lean:84–124` and the returned declarations `Module.FinitePresentation.exists_fin'` and `Module.finitePresentation_of_finite`. A chain through Noetherianity and restriction of scalars is unnecessary: Step 4 constructs the maps and identifies their images explicitly using the existing subspace-finiteness node. The searches for exact functors and the equivalence criterion returned precisely the generic results already in the DAG; no duplicate nodes were created.

Whole-DAG searches used both titles and statements for projective generators, finite-dimensional algebra/module presentations, cokernels, finite biproducts, and the full-faithful/essentially-surjective criterion, including the exact candidate Mathlib declaration names. Whole-blueprint searches with `tools/blueprint_refs.py search` included “projective generator”, “finite dimensional algebra”, “finite presentation”, “fully faithful”, and “equivalence criterion”; no blueprint node states the item. Existing general tools are cited rather than recreated.

## Not duplicates

No new nodes. The finite-dimensional subspace argument is an application of `lem-trf-vector-space-quotient-dimension`; the categorical finish is `lem-trf-fully-faithful-ess-surj-equivalence`; exactness uses `lem-sp-exact-functor-preserves-homology`.

## Review by Q36

I read Milne Lemma 9.35 on printed p.177, the full statements of all five cited DAG nodes, Stacks homology.tex `lemma-exact-functor` (Tag 010N), and categories.tex `lemma-construct-quasi-inverse` and `lemma-equivalence-categories` (Tag 02C3). I also read the finite-dimensional submodule and quotient instances at Mathlib `LinearAlgebra/FiniteDimensional/Defs.lean:132–139`, and `CategoryTheory/Equivalence.lean:606–649`. The proof keeps Milne's finite-presentation route, with its unspecified presentation and diagram expanded into actual maps and universal properties.

Step 1 uses `def-sp-abelian` only for finite biproducts and zero objects; associativity and bilinearity give the right action, and the stated detection hypothesis applied to f−g gives faithfulness. Step 2 again uses precisely the finite biproduct structure supplied by that definition. The inverse formulas with injections, projections and the standard free-module generators verify both the module identification and the Hom bijection. This is the elementary matrix calculation, not a theorem about Yoneda implicitly taken from its proof. In particular composition rs = r after s matches h·r = h after r, so the right-module convention is consistent even for noncommutative endomorphism algebras.

Step 3 uses clause (a) of `lem-sp-exact-functor-preserves-homology`, whose statement explicitly grants preservation of epimorphisms and cokernels for an additive short-exact-preserving functor. The functor to which it is applied is the underlying-vector-space F, not a functor into a module category whose abelianity has been assumed without justification. Vector-space kernels and quotients verify abelianity directly, and all the other hypotheses are in the item's assumptions. Step 5 and Step 6 cite that same clause for the same preservation statements; they do not take additional information from the cited node's proof.

Step 4 cites `def-weil-finite-dimensional-subspace` for finite spanning sets and the sentence in `lem-trf-vector-space-quotient-dimension` that says a subspace of a finite-dimensional space is finite-dimensional. The ambient finite-dimensionality of R^n is proved with coordinate copies of a finite spanning family of R, using the item's finite Hom assumption. Scalar multiples of generators are right multiplications by scalar multiples of the unit, so the k-spanning sets generate as right modules. The map with kernel generators as columns has image exactly ker(p), proving the presentation rather than assuming a commutative-ring theorem for a noncommutative algebra. The rest is a two-map construction from those cited facts and definitions; making it a node would be the elementary-node defect in the brief.

Step 5 constructs the matrix lift through the already proved finite-power Hom formula, takes an actual cokernel using `def-sp-abelian`, and applies the preservation clause just checked. The resulting quotient isomorphism is defined on representatives and is R-linear since both quotient maps are. This proves essential surjectivity in the item's proof, not in a new node restating the clause. Step 6 uses exactly the normal-epimorphism clause of `def-sp-abelian` to choose d. Cancellation of the chosen epi t proves that q remains a cokernel after replacing d by dt. Then faithfulness annihilates bu and the universal property constructs f. Surjectivity of H(q), already obtained from the exact-functor node, proves H(f)=alpha. The proof does not assume fullness to form the presentation and never assumes a chosen cokernel description of the kernel inclusion without proof.

Step 7 uses the full statement of `lem-trf-fully-faithful-ess-surj-equivalence`, after both hypotheses have been proved. A common containing universe meets that node's size convention. Its conclusion provides the functor and natural isomorphisms; the inverse on Hom is k-linear because it inverts a k-linear bijection, and conjugation by the chosen isomorphisms is k-linear. Thus ordinary categorical equivalence is upgraded to exactly the k-linear equivalence asserted here without a hidden reconstruction theorem.

Checked B1–B10: no new nodes, all objects in the retained statement are introduced, no proof is hidden in a new statement, searches were actually run and recorded, and no unsupported attachment is claimed. Checked C1–C8: the only non-elementary results invoked are the three existing general tools just described, every step's use has a verbatim statement quotation, and off-unit generic uses are declared in `split_report.tool_uses`; no other node's proof is used. Checked D1–D5: the item's steps carry both fullness and essential surjectivity, no clause is moved wholesale into a new node, and the categorical finite-presentation construction is independent of the desired equivalence. Checked E1–E6: no commutativity of R, arbitrary colimits in C, injective resolution, or pre-existing fibre-functor representability is used.

Small cases checked: P=0 forces the category to have only zero objects up to isomorphism by the finite-epimorphism hypothesis. The zero ring has only the zero unital module, since v=v·1=v·0=0. Empty spanning families, m=0 and n=0 are covered by the biproduct and empty-sum formulas. For C = finite-dimensional vector spaces with P=k, the functor and matrices reduce to the usual identity equivalence; with P=k^d the formulas use right matrix-algebra modules and the same composition orientation. No non-elementary step is longer than 2000 characters (in fact every step is below 900), and none conceals an additional “standard” comparison lemma.

## Unfinished work

None in the stage-1 split. Server dry-run and delivery results are recorded below after execution.
