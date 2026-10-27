## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-arbitrary-polynomial-dual-properties.json`: existing statement, now split in six steps; no Mathlib match. The mathematical statement is unchanged; references for perfect complexes, projective modules and module K-flatness were added.
- `citations.json`: all 23 step/node pairs, with the complete cited statements copied verbatim.
- No new DAG nodes and no new Mathlib leaves. `searches.jsonl` records six actual item searches; the item's four inherited searches remain intact.

## Attachments

None. Searches by the exact blueprint tag and by semidualizing, homothety, polynomial dual and relative-dualizing terminology in `lean/WeilConjectures/` found no declaration proving this item. General reverse-characteristic-polynomial homotheties are unrelated. No Lean file was written and no compiler was run.

## WANTED

None. The needed source texts are present locally.

## Findings and changes

The source describes this node as an agent extension of Stacks 0BZW, not that lemma verbatim. I read `dualizing.tex`, lemma-relative-dualizing-algebraic, especially the perfect polynomial dual and double-Hom calculation in (1)(b),(c). Its Noetherian hypothesis prevents simply applying it to this item. Instead, the proof uses existing arbitrary-ring polynomial pseudo-coherence, the quantitative polynomial Tor bound, the ring perfectness criterion, and pseudo-coherence reflection through a flat finitely presented quotient. No Noetherian theorem is applied to an arbitrary ring.

I read the chapter and unit records, the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md`, and the inherited provenance. This is a prerequisite for the existing relative-dualizing route below that unit, not a change to its direct-image/alteration route. No chapter or unit file was changed. `blueprint_refs.py ancestor` returns None because the inherited creation chain ends without an imported blueprint node. Its already populated `from.place` and null `from.node` are retained and explained in `split_report.blueprint`.

Whole-DAG searches by polynomial perfectness, relative perfection, pseudo-coherence, coinduction, duality and homothety found all the required lemmas. Blueprint searches for `polynomial dual`, `dual perfect`, `pseudo-coherent finite tor`, and the broader `polynomial` search yielded no blueprint node stating this item. The actual msearch calls used LeanFinder twice (second phrasing emphasizes canonical perfect duality and coinduction), Loogle, LeanSearch, a whole-Mathlib grep and an Algebra/Homology grep. Hits concern smooth/etale algebras, ordinary reflexive modules and general derived-category structure; none states the item. In particular Module.evalEquiv is underived and requires reflexivity of a module, and FGModuleCat.exactPairing concerns finite-dimensional vector spaces, so neither proves this arbitrary-ring derived assertion.

The split explicitly tracks the map: the scalar action becomes canonical bidual evaluation, via the precomposition action and evaluation at 1. It does not infer that a specified map is invertible merely from the existence of some isomorphism of its endpoints. The signs and shifts are taken from the existing scalar-normalized adjunction statement.

## Unfinished work

None for this one-level split. Its existing prerequisites remain independent DAG items as appropriate; their proofs are not claimed finished here. Delivery validation is performed by the required server dry run and delivery command.

## Not duplicates

No new nodes were created. In particular I reused lem-sfb-flat-fp-polynomial-pseudocoherent and lem-sfb-flat-fp-quotient-pseudocoherent, rather than creating further instances of Tags 067J and 0E1T. The Noetherian lem-trf-flat-polynomial-quotient-perfect is insufficient for the arbitrary-base item, so the proof instead assembles its conclusion from existing arbitrary-ring inputs. The general scalar-normalized adjunction already states the needed map compatibility, so no new scalar/biduality lemma is needed.

## Review by N6

I checked the split against delivery-errors B through E with the source and each cited node's statement open. The statement introduces all rings, the fixed surjection, the shift, the coinduction action and relative perfection; the newly added references supply its previously implicit perfect/projective/K-flat notions. There are no new nodes needing statement-only or duplicate-tag checks. All six steps are shorter than 2000 characters. I also checked that the transitive statement/proof dependencies of every substantive cited lemma do not return to this item.

Step 1 uses exactly the arbitrary-ring conclusion of lem-sfb-flat-fp-polynomial-pseudocoherent for the given presentation, not the Noetherian perfect-quotient node. The quantitative conclusion of lem-trf-base-flat-polynomial-tor-bound assumes only that A is R-flat and gives Tor_j^P(A,N)=0 for j>n for every N. I checked this against more-algebra.tex Tag 068X and the imported lemma's explicit all-module statement. The Tor definition, projective split-free definition, bounded-above-flat K-flatness statement, and K-flat tensor model justify the conversion to cochain amplitude [-n,0], including vanishing in positive degrees. This avoids hiding a comparison of ordinary Tor and derived tensor.

Step 2 invokes lem-pc-ring-pseudo-coherent-finite-tor-perfect, whose statement really is about an arbitrary ring and returns a bounded finite-projective complex. I read more-algebra.tex lemma-perfect (0658), implication (2) to (1). Its two inputs are supplied in step 1; there is no coherence or Noetherian hypothesis to import.

Step 3 uses the symmetric monoidal statement on the one-object site, so the braided-structure qualification in lem-trf-perfect-complex-derived-biduality is satisfied, with the permitted ordinary module localization universe. I read more-algebra.tex lemma-dual-perfect-complex (07VI), including the signed bounded finite-projective dual model, and sites-cohomology.tex lemma-symmetric-monoidal-derived (0FPT). The cited coinduction-adjunction node explicitly identifies the underlying P-object with RHom_P(A,P); hence restriction of the prescribed C is exactly K-dual shifted by n. The equivalent finite-projective characterization is stated in lem-pc-pseudo-coherent-bounded-finite-free-model; I read the supporting more-algebra.tex lemma-pseudo-coherent and did not silently equate finite projectives with finite frees.

Step 4 uses lem-sfb-flat-fp-quotient-pseudocoherent. Its statement is the equivalence of pseudo-coherence over the quotient and over the intermediate ring, exactly the reflection needed here. I read more-algebra.tex lemma-more-relative-pseudo-coherent-is-moot (0E1T), (4) implies (1). Both base maps are flat and finitely presented: this is assumed for A and written out from the monomial basis and empty relation set for P. The map P to A is surjective by hypothesis. Thus no finite-map or Noetherian replacement is being assumed.

Step 5 uses only the split-free meaning of projectivity, the monomial basis of P, and the two cited K-flat/tensor-model statements. I checked the arbitrary-ring restriction argument explicitly: a P-free module is R-free, and a P-projective summand remains an R-summand; tensor preserves the split equations. A bounded representative therefore consists of R-flat modules and is K-flat over R. Tensoring with any degree-zero Q leaves the same finite degree interval. This is the argument in dualizing.tex 0BZW (1)(b), applied to the actual model after step 3, so its validity does not require the source's Noetherian bounded-cohomology assertion. Together with step 4 it gives exactly the item's definition of R-perfectness.

Step 6 cites lem-trf-algebraic-shriek-derived-hom-adjunction. I opened its statement and verified that it includes the full isomorphism of derived objects and the scalar-action-to-canonical-bidual compatibility, not only an adjunction of external Hom sets. I read dualizing.tex Tags 0A70 and 0A71 and the displayed double-Hom calculation of 0BZW (1)(c). The two shifts cancel as prescribed there; (a h)(1)=h(a) identifies the actual morphism. Canonical perfect biduality, already justified in step 3, applies to the perfect A-object of D(P) from step 2. The conservativity conclusion is explicitly in lem-trf-derived-coinduction-adjunction, so restriction reflects invertibility without any flatness assumption on P to A. All of these general tools are declared in split_report.tool_uses with their purpose; the unit's geometric route is unchanged.

I tested the edge cases. If A=0 then its module category is zero, C=0, the zero complex is perfect and R-perfect, and the unique map 0 to RHom_0(0,0)=0 is an isomorphism. If R=0 then also A=P=0. For n=0 a flat finitely presented quotient is pseudo-coherent and P-flat, so the criterion yields a projective degree-zero quotient and the proof still applies. In the identity presentation R=P=A, n=0, C=A and the scalar map is the unit identification. For P=A=R[x_1,...,x_n] the shift is C=P[n], the Tor window is correspondingly shifted and the endomorphism shifts cancel; no erroneous claim of degree-zero C is made. None of these cases needs nonempty spectra, positive dimension, nonzero rings, regularity or Noetherianity.
