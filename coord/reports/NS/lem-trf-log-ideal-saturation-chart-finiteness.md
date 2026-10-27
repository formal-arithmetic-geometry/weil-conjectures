## Files written

- dag/nodes/sec-trace-formula/lem-trf-log-ideal-saturation-chart-finiteness.json: statement, split into seven steps; not a Mathlib leaf. The statement is unchanged. Added definition dependencies for the Cartesian universal property, finiteness, and general strict-etale chart presentation.
- citations.json: one verbatim statement quotation for each step/node citation.
- No new DAG nodes and no new Mathlib leaves. Two existing Mathlib leaves, lem-weil-pbc-spec-finite-ring-map-finite and lem-weil-pbc-finite-local-on-target, supply affine finiteness and target locality.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, saturation/chart combinations and log-blowup terminology. No declaration states the item. In particular ordinary coordinate-cover saturation is unrelated to log-monoid saturation.

## Literature wanted

None for this split. The ILO book and the Stacks source used here are available locally.

## Findings and changes

The imported item was statement-only. Its statement is correct with its assumed exact overlaps and distinguished generators. The proof now establishes the full chart preimages before using affine-cover locality; finiteness of a map from a source chart alone would not suffice. It also proves the spanning assertion for every finite translate cover, rather than merely saying a finite module survives tensor base change.

I read ILO Expose VIII 3.1.17, 3.1.19--3.1.21 (printed p. 101), the proof of 3.2.9 (p. 104), and 3.3.5--3.3.9 (pp. 107--108). Only the finite-morphism sentence of 3.2.9 is used: the normalization assertion is neither needed nor applied to a monoid with torsion. The existing finite-saturation node already explicitly allows torsion in the group completion.

I read the latest blueprint's sk-i-curve-zero unit and lem-trf-local-term-locality proof, through literature/blueprint/latest (main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345). This item belongs to its already recorded nearby-duality/alteration/log-regular modification ancestry. No unit or chapter route was changed. The ancestor command returned lem-trf-local-term-locality. Whole-blueprint searches for saturation, finite morphism, finite affine, 01WI, log blow and generator chart found no blueprint statement equal to this item. Whole-DAG searches for saturation, chart lifting, finite-local, 01WI, 01WH and the expected Mathlib names found the existing nodes used below. No new node was necessary.

The existing Mathlib finiteness leaves were checked in Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:37--52,73--76 and Morphisms/Basic.lean:558--577. HasAffineProperty specializes to IsFinite with its actual finite-ring affine property; this is exactly the definition used by the DAG, without a comparison theorem. Logged msearch.py searches found this general finiteness interface and no log-chart comparison. The item searches also found MonoidAlgebra.moduleFinite (Finiteness/Finsupp.lean:192), whose hypothesis is a finite monoid, and finiteType_of_fg, whose conclusion is algebra finite type: neither proves module finiteness of a saturation extension. Every new query is in searches.jsonl; the item's inherited search records are preserved.

## Unfinished work

None at this level. The cited unsplit chart-lifting and atlas-gluing lemmas remain separate existing items; no proof of them is asserted here. No Lean source was changed and no compiler, Lake or local DAG/preflight check was run.

## Review by NS

I checked the source with the item and each cited statement open. The seven steps use the following precise interfaces.

1. lem-trf-fine-monoid-finite-saturation says that a finitely generated integral monoid has a finitely generated saturated monoid, the same group completion, and a finite translate cover, without torsion-freeness. Here Q_e is finitely generated from the chosen generators of P and the finite E. It embeds in G by construction and contains P, so its group completion is G. The argument for that identification is given, not silently assumed. The source is ILO VIII 3.1.17 and the finiteness sentence of 3.2.9. Fine/fs of the associated charts follows from the definitions.

2. lem-trf-log-ideal-chart-lifting-criterion explicitly allows any fine test log scheme, with no Noetherian assumption. Apply its fine lift with T=X_e^s, which is fine by Step 1, and the given principal generator e. Its statement supplies the unique lift, the actual difference chart map, and agreement on common localizations including log maps. The resulting sheaf gluing is written out. We do not cite the proof or universal property of the parent coherent construction, which depends on this item and would be circular.

3. The same lifting node explicitly says that on a simultaneous-generator locus the difference is a unit and the lifts factor through the principal opens. This is exactly what is needed on X_f^epsilon. The unit in the log stalk has invertible structural image, so the point lies in D(z^{e-f}), the assumed exact intersection. The other implication is the item's own generator hypothesis. This avoids inferring a scheme factorization from unsupported set containment.

4. This step is elementary from the assumed exact pairwise intersections and the explicit chart ring map. The inverse image of D(z^{e-f}) is the same basic open. Union over the source cover proves the entire preimage equality, including the open subscheme structure. def-pc-fibre-product actually states the universal property used for the Cartesian square; its quotation includes that property. No claim that the comparison is strict is made or needed.

5. This step is elementary tensor expansion. def-weil-pbc-module-tensor-product explicitly states generation by pure tensors, and the monoid-algebra basis is part of the chart notation. For every q=f+p, the displayed equality a tensor z^q=(a tensor z^p)(1 tensor z^f) proves generation by the specified monomials. No flatness or injectivity is assumed and no unquoted tensor-exactness theorem is used.

6. lem-weil-pbc-spec-finite-ring-map-finite says precisely that Spec of a finite commutative-ring map is finite. lem-weil-pbc-finite-local-on-target, Stacks Tag 01WI, label lemma-finite-local, says precisely that an affine target cover with affine finite-module full preimages suffices. These hypotheses hold by Steps 1,4,5. The statement of def-weil-finite-integral-morphism, Tag 01WH, label definition-integral, gives the every-affine-open conclusion. These are existing Mathlib leaves, exempt from off-unit route restrictions; no new tool-use declaration is needed.

7. lem-trf-log-ideal-affine-atlas-gluing has an explicit arbitrary-ring-base-change clause giving charts, overlaps, ideals and pulled-back log structures. That clause is actually in its statement. The comparison ring maps fix the same monomials in either order, so the chart maps and the log inclusions agree after base change; the argument specifies this on generators. Strict etale restriction is covered by the general notion recorded in def-trf-log-ideal-chart-presentation, without imposing local Noetherianity or saturation on the base P. The same F_e still works, so the finite-module argument applies over each affine piece and the exact principal-open squares persist. This follows the strict-chart route of ILO VIII 3.3.5--3.3.9.

I tested the potential exceptional cases: E={e}, when Q_e=P and the assertion is finite saturation of one affine chart; P already a group, when every chart and comparison is the identity and generators differ by units; a group completion with finite torsion, where Step 1 explicitly uses the torsion-compatible result; a nonnormal/nonnodal arbitrary coefficient ring, since normalization and regularity are unused; A=0 and empty tensor charts, where the zero module is still generated by the proposed finite list; and alpha(e)=0 or a zero divisor, since the proof cancels only in integral log monoids and never divides by alpha(e) in a ring. For P=N^2 and E={(1,0),(0,1)}, the locus calculation is the two familiar monomial ratio opens, with signs e-f checked on the f-chart. Base change with nonflat A to A' still preserves the explicit spanning equation.

Against delivery-errors B--E: no new nodes, so no hidden sketches, duplicates or clauses renamed as lemmas; all existing dependencies were read for their actual statements; every non-elementary input is cited; all proof dependencies are exactly the step-uses union; no citation goes upward to this item's parent; the two elementary steps give their actual calculations. Each non-elementary step is under 2000 characters (the longest is under 1000), and none conceals a separate comparison lemma. I corrected the preliminary approach by using the already existing finite-local node instead of creating another Mathlib leaf. There is no statement dispute or source correction.

## Validation

The first server dry run passed preflight at 9d8a43c191d. All searches from this session have also been appended to the item with the literal logged tool and query, actual hit names, and their item-level verdict; inherited records are retained. A final dry run is required for this updated record before push.
