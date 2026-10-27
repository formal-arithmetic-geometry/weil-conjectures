# Q37 stage-1 delivery: lem-sfb-proper-support-tensor-perfect

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-support-tensor-perfect.json: item split; statement unchanged; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-flat-proper-model.json: statement-only etale-local Noetherian model for the input data; not in Mathlib.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-noetherian-tensor-perfect.json: statement-only Noetherian algebraic-space tensor direct-image theorem; not in Mathlib.
- citations.json: verbatim statement quotations for every citation in all four proof steps.

## Attachments

None. Searched the project Lean by blueprint tag and the perfect/proper-support/tensor/direct-image notions. The scheme theorem AlgebraicGeometry.Scheme.noetherian_perfect_directImage does not state the algebraic-space result. No Lean was written, compiled or built.

## Literature

No WANTED entries. Read spaces-perfect.tex Tag 0A1P, including its full Noetherian-approximation argument, 0A1K's precise base-change isomorphism, 0DKJ and 08IS, 09RJ and its inverse-system situation, and 08JL. Read spaces-limits.tex 08K0 and 08K2 with Situation descent-property; checked the existing statements of 07SK and 07V7. Read spaces-cohomology.tex 07UB's coherent/finitely-presented equivalence. Read sites-cohomology.tex 08G5 and 08H6, and spaces-properties.tex 03M1. Read the current latest blueprint direct-images proof (3), the recorded unit and chapter, and the inherited route. This is a supporting coherent-structure-module result on that route; no SGA source or change of six-functor route is involved.

## Corrections and scope

The item was statement-only. Its existing searches are retained. All new searches were run through msearch.py; searches.jsonl and the saved output files retain the actual results. Both semantic searches were rephrased. Returned hits concern scheme morphisms, module flatness, ring perfection, or abstract bounded derived categories, and none supplies either space theorem. Loogle's perfect-field results are about fields, not perfect complexes. No Mathlib leaf is asserted.

The split does not replace the item with another theorem saying the same thing. The model lemma concludes only existence of input data and comparison isomorphisms, not perfectness or even a comparison of direct images. The second lemma is the strictly smaller Noetherian case and allows a locally finite-type quasi-separated morphism rather than requiring f proper. The item uses base change twice to connect these inputs. The existing scheme-only approximation and perfect-direct-image nodes cannot be applied to an algebraic-space source.

## Review by Q37

I checked B--E against the source and all cited statements. The new nodes introduce their own rings, spaces, complexes and conventions, have no proof or proof dependencies, and retain the inherited blueprint ancestry, whose ancestor command prints None. Their from.place records the precise supporting Stacks argument; the chapter and unit are inherited. The module and geometric conventions are written out, and the base-change coefficient complex is ordinary termwise pullback, never silently derived. Neither new result is elementary: spreading out a perfect complex and its proper-support coefficients requires the limit theorems, and 0DKJ requires the coherent finite-Tor direct-image theorem.

Step 1 uses the existing space quasi-coherent kernel/cokernel/colimit statement, not a scheme closure theorem. Its statement explicitly supplies kernels, cokernels and images with no Noetherian hypothesis. A summand of a finite free module is the kernel of 1-e; then cohomology is the kernel modulo image. The exact restriction statement in lem-sfb-ringed-site-restriction-kflat applies to module sheaves on every small ringed slice. The quasi-coherence definition is local on precisely these sites. This proves the extra quasi-coherence clause and supplies D_QCoh for every base-change application, without creating a new node for a few-line argument.

Step 2 cites the new model statement for exactly its etale cover, input models and their derived E/ordinary G identifications. I checked 0A1P's proof: after descent of the space and finitely many terms and differentials, the finitely many d-squared equations stabilize; 08K0 makes the finitely presented coefficients relatively flat, 08K2 makes their scheme theoretic supports proper, and 09RJ descends the perfect object. Each bounded complex has finitely many terms, so a common later stage suffices. This is the argument intended for the statement-only model node, not an assertion of a proof inside that node. The Noetherian rings can be finitely generated integer subrings of an affine chart ring. Approximation is absolute over Spec Z: an S-structure on the models is neither needed nor claimed. The 07UB equivalence ensures coherent coefficients on the locally Noetherian source. The Noetherian tensor statement is precisely 0DKJ, with B Noetherian, f locally finite type and quasi-separated, and E perfect; all these hypotheses hold for the finitely presented model. The item makes no improper assumption that X itself is a scheme.

Step 3 quotes the entire statement of lem-sfb-space-flat-complex-base-change, including its canonical derived isomorphism, its D_QCoh hypothesis and ordinary G pullback. The original f and the model f are finitely presented and hence qcqs. The original coefficients are bounded and relatively flat, and the model supplies those properties at the Noetherian stage and on the etale chart. Step 1 gives quasi-coherence of both E and the model E. Applying the statement separately to the etale chart and to the ring-model base change yields the displayed derived-category comparison. This is not an appeal to an unspecified cohomology-group identification.

Step 4 uses the full ringed-topos strict-perfect pullback statement: its finite-free splitting, K-flatness and derived comparison supply exactly the bounded model after arbitrary, possibly nonflat, pullback. Its hypotheses are a bounded strict-perfect model with specified splittings; such models are what the item's definition of perfectness supplies locally. It is applied locally and the inverse-image covering is a covering by the definition of a morphism of topoi. For the final etale cover, def-trf-algebraic-space explicitly says pullback is restriction on the localized etale sites. Composing coverings proves local perfectness by the definition, and Step 1 gives quasi-coherence. I corrected the pullback tag in the step source to 08H6 after checking the tag table.

I tested empty spaces, the zero complex, a one-term coefficient complex and arbitrary shifts of E. Empty/zero input allows empty/zero models and gives zero, hence perfect, direct image; no nonempty-support or rank assumption is present. Varying local amplitude on a non-quasi-compact Y causes no problem: models and bounds are chartwise, and no global bound on Y is concluded. An affine chart makes its finitely presented source qcqs, as needed by the limit theorems; the source need not be proper. Nonflat ring-model base change is legitimate because E is derived-pulled back and G is relatively flat over the base. The comparison source explicitly uses ordinary pulled-back G, addressing that important small case. No proof step is longer than 2000 characters, and none hides a further independent identification. Generic ringed-site citations outside the inherited unit are declared in split_report.tool_uses.

## Not duplicates

lem-sfb-space-perfect-flat-proper-model vs lem-sfb-proper-support-tensor-perfect: the new node concludes only descent of input data and no direct-image property; the item proves perfectness using that descent, the Noetherian theorem and base change.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-fp-module-limit-category: the existing statement descends individual finitely presented modules and morphisms; the new one simultaneously descends a space, a perfect derived object, a complex and its relative flatness and proper support.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-fp-space-limit-category: the existing statement descends finitely presented spaces and their morphisms, with no perfect objects or coefficient data.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-fp-space-qcqs-base-limit-descent: the existing statement descends spaces and morphisms over qcqs scheme bases, with no perfect objects or coefficient data.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-eventually-flat: the existing statement concerns flatness of a morphism, not relative flatness and proper support of coefficient modules or descent of a perfect object.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-invertible-limit-descent: the existing statement descends a line module only, not a general perfect object with relative coefficients and geometric models.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-coherent-abelian: the existing statement concerns closure of coherent modules under kernels, cokernels and extensions; it gives no descent theorem.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-qcoh-groupoid-equivalence: the existing statement identifies quasi-coherent descent data on an atlas, not Noetherian models of perfect objects with relatively flat proper-support coefficients.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-coherent-derived-internal-hom: internal Hom coherence is not a model/descent theorem.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-proper-coherent-higher-images: higher direct-image coherence is not an existence theorem for Noetherian input models.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-noetherian-coherent-support: coherence and support on a locally Noetherian space do not descend a space, complex or perfect object to a Noetherian base.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-space-coherent-kernel-cokernel-extension: coherent closure on a fixed space supplies no Noetherian model.
lem-sfb-space-perfect-flat-proper-model vs lem-sfb-proper-space-coherent-derived-image: bounded coherent direct image is not descent of perfect and relatively flat input data.
lem-sfb-space-perfect-flat-proper-model vs lem-pc-proper-support-local-noetherian-model: that statement is only for schemes and includes a direct-image comparison; this statement covers algebraic spaces and descends the input data only.
lem-sfb-space-perfect-flat-proper-model vs lem-pc-noetherian-approximation-data: that statement descends scheme input; this one allows nonrepresentable algebraic-space input.
lem-sfb-space-noetherian-tensor-perfect vs lem-pc-noetherian-perfect-direct-image: the existing theorem has schemes as its source and base, whereas the new theorem covers algebraic spaces.

## Unfinished work

None in this stage-1 split. The two new statements intentionally remain unsplit for later workers. Independent maintainer review remains the delivery protocol.
