# Stage-1 report: lem-sfb-zero-verschiebung-primitive-generation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-zero-verschiebung-primitive-generation.json: item, statement preserved, split into nine proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-verschiebung-naturality-diagonalizable.json: statement-only input; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-commutative-no-diagonalizable-additive-filtration.json: statement-only input; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-length-two-witt-extension-verschiebung.json: statement-only input; Mathlib no match. Infinite Witt-vector shift formulas are relevant but do not identify canonical group-scheme Verschiebung on this finite represented extension.
- dag/nodes/sec-six-functors-basics/lem-sfb-additive-subgroup-commutative-extensions-witt.json: statement-only input; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-commutative-extension-pushout.json: statement-only input; Mathlib no match.
- citations.json: exact statement quotations for all step/node pairs.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag, Verschiebung, primitive Hopf generation, Witt extensions, and unipotent series. No matching project declaration was found. The item's inherited record has no Lean declaration to attach. Mathlib searches were run through msearch.py; their results and query text are recorded unchanged in each node. A first item grep mistakenly supplied Mathlib/RingTheory/HopfAlgebra where the command requires RingTheory/HopfAlgebra; the corrected query was run and returned zero hits. Neither that first empty result nor Loogle's unknown-identifier diagnostic was used to establish absence. The subsequent quoted-name Loogle query was successful and empty. Item searches inherited from Q65 are retained as history, with new Q12 searches available in searches.jsonl.

## WANTED

None. Milne, Algebraic Groups (iAG2017), is available locally and supplies the actual proof and all five new inputs. No SGA source was used. No Stacks tag states the group-scheme structure, Witt-extension classification, or canonical Verschiebung facts here; their sources are the precise Milne propositions, not invented Stacks references. The generic affine closed-immersion tool already cites Stacks Tag 01QO, lemma-closed-immersion in morphisms.tex; no duplicate of that tool is created.

## Findings and corrections

The imported statement is correct, including non-smooth and disconnected groups over an imperfect field; it is unchanged. The proof was empty. Milne 14.48 starts its induction after an implicit unipotence reduction. The split now makes that reduction explicit: after algebraic closure, diagonalizable subgroups have invertible Verschiebung, so vanishing rules them out; 16.13(a) and 14.21 then supply the additive-subgroup filtration. This avoids citing smooth classification results, which would not apply.

The Witt obstruction must be cancelled as a twisted morphism. It is not enough to claim that a coordinate has zero p-th power: the coordinate algebra can be nonreduced. The proof uses naturality, the explicit two-coordinate shift formula, and invertibility of field Frobenius over the algebraic closure. It concludes that h itself is zero, so the pushed-out extension splits. It also makes the scheme-theoretic kernel check on all algebra-valued points, before applying the existing group homomorphism factorization theorem.

Milne Section 11(j) uses a zero-based Witt index but 15.27 denotes its two-coordinate extension by W_2. The new node fixes its meaning by explicit coordinates and records this indexing distinction. The source of affine quotient representability is Proposition 5.18 (not a newly invented representability assertion).

blueprint_refs.py ancestor reports null for this inherited created-item chain. The existing null ancestor and complete via chain are retained, with the precise Milne prerequisite appended to the place fields. Searches of the current literature/blueprint/latest and the whole imported blueprint found no equivalent algebraic-group statement. This item is an auxiliary prerequisite, not the key statement of sk-thm-sf-ctf-stability, so no unit or chapter record is changed. Generic off-unit tools are declared in split_report.tool_uses.

## Not duplicates

lem-sfb-verschiebung-naturality-diagonalizable vs lem-sfb-affine-group-frobenius-verschiebung: the existing node constructs canonical V and states VF=[p]; it does not state naturality, scalar/product compatibility or invertibility on diagonalizable groups.
lem-sfb-commutative-no-diagonalizable-additive-filtration vs lem-sfb-unitriangular-coordinate-filtration: the existing node gives coordinate filtrations of a specified unitriangular matrix group; the new statement obtains a filtration of an arbitrary possibly non-smooth commutative group with no diagonalizable subgroup, including existence of the quotient groups.
lem-sfb-commutative-no-diagonalizable-additive-filtration vs lem-sfb-unipotent-central-additive-subgroup: the existing node assumes smoothness and connectedness and produces one additive subgroup; the new statement includes finite and infinitesimal factors and requires neither hypothesis.
lem-sfb-affine-commutative-extension-pushout vs lem-sfb-algebraic-group-homomorphism-factorization: factorization handles an existing group homomorphism and its kernel; it does not construct an affine quotient by an arbitrary normal subgroup or the represented extension pushout.
lem-sfb-additive-subgroup-commutative-extensions-witt vs lem-sfb-primitive-frobenius-module-duality: the latter reconstructs groups already embedded into vector groups; it neither classifies arbitrary commutative extensions nor supplies such an embedding for the middle group.
lem-sfb-length-two-witt-extension-verschiebung vs lem-sfb-affine-group-frobenius-verschiebung: the new node specifies a particular two-coordinate group and its extension maps and computes its canonical V; the existing node only constructs V for an arbitrary already given group.
All five vs lem-sfb-zero-verschiebung-primitive-generation: none asserts generation by primitives or the desired embedding for an arbitrary V-killed group. The induction, elimination of the Witt obstruction, simultaneous extension of coordinates, and scalar descent remain in the item's proof.

## Unfinished work

No unresolved proof step in the item. The five new statements are intentionally unsplit, as this is a one-level stage-1 delivery. No Lean was written and no compiler or Lake command was run.

## Review by Q12

I read the item source, Milne Definition 14.45 and Proposition 14.48 on printed pp.295-296. I also read Definition 11.39 and its naturality/product/base-change properties on pp.224-225, the Witt addition and shift formulas and exact sequence on pp.226-227, Proposition 14.21 on pp.284-285, Proposition 15.27 on p.316, Theorem 16.13 on p.328, and Chapter 5's affine quotient and homomorphism theorems. Each new statement is introduced independently with its field and group hypotheses and an explicit meaning for fppf exactness; each has an empty proof and proof dependency list. The new statement about Witt pullbacks is only invoked over a perfect field. I checked the proposed inputs against DAG statements, the whole blueprint search, project Lean and actual Mathlib hits before deciding to add them.

Step 1 uses only the coordinate Hopf statement and tensor universal property: the reduced coproduct kernel commutes with field extension by unique finite expansion in a field basis, written out here. Step 2 uses the naturality node's actual scalar-extension, subgroup and diagonalizable-isomorphism clauses and the algebraic-closure existence node. Step 3 uses the filtration node's actual chain and quotient maps and naturality's subgroup clause; it states the induction and base case explicitly. Step 4 uses the pushout node's represented quotient and short exact row, the Witt node's V_Ga=0 clause and the product/quotient clauses of naturality. No surjectivity on R-points is presumed.

Step 5 uses precisely the Witt-pullback node's isomorphism of extensions and equations tau a=hq', ai=j; naturality supplies V_W a^(p)=a V_E and the Witt node supplies V_W(x,y)=(0,x). Over K, X^p-c has a root for every c because K is algebraically closed; field Frobenius is injective, hence an automorphism. Therefore inverse scalar transport cancels a twist even for nonreduced group schemes. Epimorphicity of q' is part of the exact extension's hypotheses. Step 6 uses the h=0 pullback, j=ker tau, and bi=j phi to write the extending homomorphism explicitly. Step 7 uses the filtration's identification ker q=N and the previously constructed embedding on N; the factorization node explicitly supplies both a closed immersion and identification of its quotient factor with the represented fppf quotient B/ker u, so it does justify the conclusion when the kernel is 1. Step 8 uses the surjectivity clause of the affine-cover closed-immersion criterion and the actual additive coproduct in def-sc-gm-ga, together with the coordinate Hopf dictionary. Step 9 needs only tensor linearity; the basis retraction with ell(1)=1 is written out, so descent of generation is not a black box. The exact full statement of every cited node is copied to citations.json, ensuring that every requested clause really occurs there.

I tested the item on the trivial group (empty generators), Ga, alpha_p and alpha_(p^r) (the primitive coordinate survives nilpotents), constant Z/p (disconnected), and an imperfect-field form Y^p=X-tX^p inside Ga^2 (no perfection is available before extension). Mu_p is excluded because its Verschiebung is an isomorphism, despite [p]=0; replacing the hypothesis by exponent p without smoothness would fail. The Witt extension itself has nonzero Verschiebung and therefore is not incorrectly declared split; its pullback along h=0 is split, while a nonzero h, including one supported on an infinitesimal subgroup, is detected by the twisted-morphism argument. At p=2 the displayed Witt cocycle is XY and the same shift argument applies. The five inputs include the trivial subgroup and zero-coordinate cases. All proof steps are below 2000 characters (largest 926); none hides a further source lemma under 'standard', and no step applies a definition as if it were an unproved classification theorem. I checked the B-E return checklist against these statements and corrections: no hollow construction, no smoothness assumption added, no item clause merely renamed as a new node, and no dependency on the item from a new node.

## Validation

The server dry run passed preflight, check_dag.py and review_split.py on commit 04e4d271542. A final source-label check corrected this report’s Stacks label to morphisms-lemma-closed-immersion (Tag 01QO). The final dry run is repeated after that report correction and after appending the actual Q12 item search records.
