## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-flat-multiplicative-deformation.json — item, statement, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-type-etale-splitting.json — new statement-only prerequisite, unsplit; no Mathlib match. This is Conrad Proposition B.3.4, not a nilpotent deformation theorem.
- citations.json — verbatim statements for every use in all eight proof steps.

One new node, zero Mathlib leaves. The search outputs and exact queries are retained in searches.jsonl, search-plan.json, and the *.search.txt files. Only the DAG files and report are delivered.

## Attachments

None. Searched lean/WeilConjectures for the item id, diagonaliz/diagonalis, and multiplicative-type terminology. The only unrelated diagonalization hit was FiniteCoproductConstantBaseChangeSquare.lean:65. There is no project declaration stating the full item, nor one stating the new general étale splitting prerequisite. No compiler was run and no Lean file was written.

## Wanted literature

WANTED: Brian Conrad, Reductive group schemes (2014), Appendix B.2–B.3, especially Remark B.2.4, Theorem B.3.2(2), and Proposition B.3.4, for lem-sfb-nilpotent-flat-multiplicative-deformation and lem-sfb-multiplicative-type-etale-splitting; local archive literature/conrad-reductive-group-schemes.pdf. Read the primary online PDF at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed pp.283–292. No SGA source was used. No Stacks tag states the new multiplicative-type splitting theorem; its actual source is specified rather than assigning a fictitious tag.

## What needed correction

The item's statement is true and is retained verbatim. Both the general multiplicative-type assertion and the stronger marked split assertion are proved. No smoothness or invertibility assumption was introduced.

There is a gap in the abbreviated source proof at printed p.289 if its direct invocation of Corollary B.2.6 is read as allowing a nonsmooth target: that corollary explicitly assumes a smooth target. In particular D_R(Z/pZ) = mu_p is not smooth in characteristic p, so applying that corollary directly with target D_R(N) does not justify the torsion case. I expanded the degree-two obstruction argument character by character, with unit-valued characters, and used the existing regular two-cocycle lemma over R/J. Uniqueness follows from a written primitive-coefficient calculation. This repairs the inference without changing the theorem or its obstruction-theoretic route.

The original proof was empty. The marked square-zero construction is now in Steps 1–5, the finite nilpotent induction is Step 6, and the fppf-local conclusion is Steps 7–8. Kernel and cokernel arguments are written explicitly; no generic flat-isomorphism lemma has been added just to encapsulate those few lines.

The latest blueprint files read are literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, snapshot main-20261024 per COMMITS.txt. This item is a structural prerequisite far below direct-images proof (3), not a key unit node. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor reports None for the existing created.item chain. I retain that inherited provenance and put the exact supporting source place in the new node rather than inventing an ancestor. No chapter/unit route was changed, and no unit realization record was edited.

## Unfinished work

The new étale splitting theorem is intentionally statement-only and awaits its own stage-1 split. Its source is Proposition B.3.4; affine sources follow by refining its étale cover by affine opens. A direct subsequent proof may descend the character sheaf / constant discrete automorphism torsor of the fppf form; it need not use the present nilpotent deformation item. This avoids making the dependency back into a cycle. The source's alternative deformation-based proof must not be copied into that future node without checking its dependencies.

## Not duplicates

lem-sfb-multiplicative-type-etale-splitting vs lem-sfb-torus-etale-trivialization: the existing theorem assumes a relative torus and has finite free character groups; the new theorem allows arbitrary finitely generated character groups, including p-torsion over characteristic p, and hence non-smooth diagonalizable groups.

lem-sfb-multiplicative-type-etale-splitting vs lem-sfb-smooth-connected-multiplicative-torus: the existing result identifies smooth connected multiplicative-type groups as tori and does not supply étale splitting of general nonsmooth groups.

lem-sfb-multiplicative-type-etale-splitting vs lem-sfb-multiplicative-character-antiduality: the existing character antiequivalence is over a field and describes Galois descent; the new locality assertion is over every scheme, with no field, local, reduced, or Noetherian restriction.

lem-sfb-multiplicative-type-etale-splitting vs lem-sfb-relative-diagonalizable-character-duality: that theorem concerns already split groups and maps between them, not étale-local splitting of an fppf form.

lem-sfb-multiplicative-type-etale-splitting vs lem-sfb-nilpotent-flat-multiplicative-deformation: the new lemma assumes an fppf form on its original base and refines its splitting topology; it makes no claim about deformations over another ring or lifting a marked isomorphism. The item's deformation argument remains explicitly in Steps 1–6.

The whole DAG was searched by diagonalizable/multiplicative terminology, the places B.3.4 and B.2.4, and Hochschild/cocycle terminology. The whole imported blueprint was searched with tools/blueprint_refs.py for diagonalizable, multiplicative type, nilpotent, Laurent and splitting terminology. No blueprint node states the general étale splitting theorem. B.3.4 hits were inspected and the torus-only cases distinguished above. The existing regular two-cocycle node was reused instead of introducing a vanishing lemma. Flat tensor exactness, flat last-term tensor injectivity, affine tensor pushouts and affine étale lifting were all reused.

## Review by Q109

I read Conrad's square-zero paragraph in Theorem B.3.2(2), printed p.289, together with Remark B.2.4, Proposition B.2.5 and Corollary B.2.6, printed pp.285–287, and Proposition B.3.4, pp.291–292. The latter agrees with the sole new node: fppf-local forms of finite-type diagonalizable groups are étale-locally diagonalizable. It has no smoothness, locality, noetherianity or torsion-order hypothesis. Refining the resulting domains by affine opens gives the new node's affine cover. I read the statements of all nodes used below, not merely their titles or their proofs. The exact full statements are copied into citations.json so that their hypotheses remain visible.

In Step 1, lem-weil-pbc-flat-tensor-exact really preserves the exact sequence beginning with J -> R when tensoring with C and its tensor powers. This gives the needed J-linear coefficient identifications without any finite-generation assumption on J. The affine spectrum statement gives contravariance and full faithfulness; lem-weil-pbc-algebra-tensor-pushout-universal-property identifies products of affine schemes through the tensor pushout. Unit lifting is the explicit geometric-series calculation for a square-zero error; no formal smoothness theorem is hidden in it. Characters here are morphisms to the group of units, represented by R[t,t^{-1}].

In Step 2, lem-sfb-diagonalizable-regular-two-cocycle states exactly the regular 2-cocycle-to-coboundary assertion for a diagonalizable group over an arbitrary commutative ring and an arbitrary coefficient module. I apply it over R_0, with its finitely generated group N and coefficient module J with trivial coaction, not over R with an unproved diagonalization of G. The coproduct calculation verifies the cocycle condition on the universal triple, and the replacement by (1+b)v has the displayed sign. Thus the proof is equality of scheme morphisms rather than equality only on field-valued points. The counit and inverse are checked after correcting multiplication.

In Step 3, def-sfb-ring-diagonalizable-group gives precisely the basis and diagonal coproduct used in the primitive calculation. Off-diagonal and diagonal coefficient comparisons force x=0 even for J with torsion. This is a finite coefficient check, not an invocation of an unrecorded H^1-vanishing theorem. In Step 4 the same definition gives the product rule, coproduct, counit and inverse on R[N]; uniqueness of each character enforces every relation in N, including torsion relations. The affine spectrum statement then gives the map in the correct direction G -> D_R(N), with exactly the prescribed a_0 as reduction.

In Step 5, lem-weil-pbc-tensor-right-exact supplies surjectivity modulo J for the cokernel, and lem-weil-pbc-flat-quotient-tensor-injective applies because the last module in 0 -> K -> R[N] -> C -> 0 is the given flat R-module C. It is not an assumption that the map phi is flat, nor an application of a module-flatness definition as if it were a tensor-exactness theorem. K=JK and Q=JQ imply zero by J^2=0, with no Nakayama finiteness hypothesis. I checked the local Stacks sources: 00DF, algebra-lemma-tensor-product-exact; 00HD, algebra-lemma-flat; 00HL, algebra-lemma-flat-tor-zero.

Step 6 explicitly inducts from k=1 to k=a along R/I^{k+1} -> R/I^k. The kernel is I^k/I^{k+1}, square zero because 2k >= k+1. The flatness and finite-presentation definitions cited here really provide the hypotheses used: the proof writes out tensor restriction to quotient modules and reduction of a polynomial presentation. Each lift preserves the preceding marking, so the final reduction is a_0, not merely some split identification.

In Step 7, the new lemma is used only on G_0, which is of multiplicative type by hypothesis. lem-weil-pbc-affine-etale-closed-immersion-lift assumes affine X and V and a closed immersion Z -> X; these hold for Spec R, the selected affine V_j, and Spec R/I -> Spec R. Its statement really gives an affine étale U_j with V_j as its entire base change. I read Stacks 09ZA, etale-cohomology-lemma-closed-of-affine-normal-scheme-with-alg-closed-function-field, proof's first paragraph: the generic affine étale lifting fact is exactly the one recorded in that existing node. Nilpotent ideals are contained in every prime, so the coverage argument is elementary. def-weil-etale-morphism explicitly includes flat and locally finitely presented, and def-pc-fppf-site requires precisely those properties and joint surjectivity. The affine étale lifting theorem is declared as an off-unit generic tool in split_report.tool_uses; it replaces no unit proof route.

Step 8 writes the coordinate algebra after base change, reduces the finite presentation, proves flatness on injections by tensor associativity, and checks nilpotence of the extended ideal. This verifies all hypotheses of the marked assertion already proved in Step 6. The fppf covering plus its individual isomorphisms is exactly the definition in the item's statement; no unjustified gluing of the markings is asserted.

I tested the zero ring and empty base, I=0/a=1, J=0, N=0, N=Z, and N=Z/pZ over F_p[epsilon]/(epsilon^2). The last case tests the crucial nonsmooth group mu_p. No division by p, group order, or 2 occurs: j_0=2j_0 implies j_0=0 by subtraction, including characteristic 2. The general étale splitting node includes an empty covering of the empty base and torsion groups in arbitrary characteristic. All new-node fields give a self-contained statement without proof or proof dependencies. All non-elementary facts in the item's proof are cited, while the module-isomorphism check and character uniqueness are short calculations and remain steps. No step exceeds 2000 characters. All recorded searches were actually run with msearch.py; the hits concern ordinary affine-diagonal morphism properties, étale algebras or square-zero algebras, not multiplicative-type group-scheme splitting. Two semantic phrasings were checked before recording absence. The original item statement and inherited metadata are unchanged.
