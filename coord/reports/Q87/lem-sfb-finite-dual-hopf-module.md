# Stage-1 report: lem-sfb-finite-dual-hopf-module

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-dual-hopf-module.json`: statement, split; no Mathlib match for the full dual Hopf-module construction. The statement and its statement dependencies are unchanged.
- `citations.json`: one literal statement quote for each node used by each of the six steps.
- No new nodes; zero new Mathlib leaves. `searches.jsonl` contains the searches actually run in this sandbox. The initial sandbox had no item, report, or previous search log. Local helper `write_split.py` only writes these sandbox artifacts.

## Attachments

None. I searched the project Lean by the exact blueprint tag, the id, HopfModule, finite dual, antipode and coaction. The project has Hopf-algebra constructions for general linear groups and quotient ideals, but no declaration states this item. Its imported search records have been preserved.

## Wanted literature

WANTED: Siqi Clover Zheng, *Frobenius Algebra Structure in Hopf Algebras and Cohomology Ring with Poincare Duality*, 17 October 2020, Proposition 4.12(2), printed p.8, for lem-sfb-finite-dual-hopf-module. Intended path: literature/zheng-frobenius-algebra-hopf-2020.pdf. I read the primary PDF online at https://math.uchicago.edu/~may/REU2020/REUPapers/Zheng,Siqi.pdf; it is not in local literature/.

WANTED: Rolf Farnsteiner, *Hopf Modules and Integrals: The Space of Integrals*, 26 April 2006, printed p.1, for lem-sfb-finite-dual-hopf-module. Intended path: literature/farnsteiner-hopf-modules-integrals-space-2006.pdf. I read https://www.math.uni-bielefeld.de/~sek/select/HopfMod2.pdf, whose formulas independently agree. No document was downloaded or added to the shared repository.

## Audit and corrections

The original statement is mathematically correct with its explicit left-left diagonal compatibility and commutative-algebra hypothesis. The cited sources leave the verification of the dual Hopf-module structure to the reader. The split supplies this verification; proof_origin is agent, because the two reference PDFs are absent locally and the detailed argument is supplied here.

The main potential gap was the identity for comultiplication of the antipode. The Hopf axioms in the statement do not list it. Step 5 derives it from the existing convolution-algebra leaf, rather than citing a source or a Hopf definition as if it asserted the identity. This takes a short inverse-uniqueness computation in an associative algebra. The final step writes the full cancellation with three coproduct indices, so it does not silently assume cocommutativity or invertibility of the antipode.

The latest blueprint unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-image proof were read, as were the chapter and DAG unit records. The inherited provenance explains the finite-Hopf algebra prerequisite far below the alteration/algebraic-group quotient route. `blueprint_refs.py ancestor` prints None, and this existing `from.node` and `via` data have been retained; the Hopf and antipode blueprint searches locate no statement of the item (the general linear/additive group definition is unrelated). No unit realization fields need changing: this item is not the unit's key statement.

## Search results

All additional Mathlib searches used the required msearch.py command and their exact tool/query/subdirectory and returned records are appended to mathlib_searches. Two semantic phrasings were used. HopfAlgebra.ofAlgHom, the two antipode cancellation axioms and HopfAlgCat structure projections do not construct the dual coaction. Loogle `HopfAlgebra, Module.Dual` returns no hit; the HopfAlgebra directory grep for coaction/dual/HopfModule also returns no hit. Broader antipode searches find CategoryTheory.HopfObj.antipode_comul. I read Mathlib/CategoryTheory/Monoidal/Hopf_.lean:259-276: it gives the general anti-coalgebra identity, only one intermediate fact here, rather than the whole item. I also read HopfAlgebra/Basic.lean and Convolution.lean and the existing convolution node's referenced Coalgebra/Convolution.lean declarations. Instead of creating a special-case antipode node, step 5 gives its short derivation from the existing convolution algebra statement.

## Not duplicates

No new nodes were created. The existing lem-sfb-convolution-linear-map-algebra is reused. The finite-hopf-frobenius-form parent, Hopf-module kernel/coideal siblings, and rational representation/comodule dictionary state different results; none replaces this item's unique dual coaction and its action compatibility.

## Review by Q87

I read Zheng Proposition 4.12(2) and its definitions immediately above it, and Farnsteiner's displayed dual-action/convolution-coaction formulas on printed p.1. Evaluating the source convolution formula at x gives exactly the tensor-evaluation characterization in the item. The item's explicit diagonal formula is the convention used throughout this proof. No new node needs a separate source review.

For step 1, the statement already supplies S as a unital k-algebra map. Linearity and the action laws are checked pointwise; the commutativity hypothesis justifies the order of the two S-factors. No lemma about a general antipode being multiplicative is used.

For step 2, I opened def-weil-pbc-free-module: it gives unique finite coordinates. The coordinate functions are consequently linear and the identity g=sum_i g(e_i)e_i^* follows by evaluating on the chosen basis. I opened def-weil-pbc-module-tensor-product: it gives bilinearity, the universal property and generation by pure tensors. The reconstruction formula is checked on a pure tensor, then extended by linearity. It proves separation for every first factor V as well as existence and uniqueness of rho. This avoids importing an uncited tensor-Hom comparison theorem.

Steps 3 and 4 use the same tensor node for contraction and tensor maps, and use only the two Hopf coalgebra identities explicitly assumed in the statement. I checked both triple-tensor expressions in step 4 in their displayed order. Evaluation always acts on the final dual factor; hence the reconstruction from step 2 applies with V=H tensor H. No cocommutativity is substituted for coassociativity.

For step 5, I opened lem-sfb-convolution-linear-map-algebra and read its complete statement. It asserts the actual associative unital convolution algebra for any coalgebra C and any associative unital target algebra B, without cocommutativity. I take R=k, C=H, B=H tensor H. The hypothesis that B is an algebra is supplied by lem-weil-pbc-algebra-tensor-pushout-universal-property, whose statement explicitly gives componentwise multiplication and the two insertion algebra maps. The tensor node supplies the linear maps. Applying each algebra map u to the two assumed antipode identities verifies both inverse equations. The inverse of a product is the reverse product of inverses by associativity; uniqueness is written as p=p*(a*q)=(p*a)*q=q. Thus this is a short consequence of cited statements and assumptions, not a new hidden Hopf lemma. I checked the cited Mathlib leaf's declarations at Coalgebra/Convolution.lean:55-68,174-193,212.

For step 6, I reread the algebra-tensor node for componentwise products and the module-tensor node for contraction. Substitution into step 2 uses S(h_(2))x, not h_(2)x. Step 5 reverses its coproduct indices; the resulting expression has h_(1)S(h_(2)) outside f and S(h_(3)) inside. The displayed three-factor antipode cancellation then gives exactly the left-hand evaluation. All hypotheses used are present: H is commutative, the antipode is an algebra map, the coalgebra is coassociative and counital, and the basis is finite. Neither algebraic closedness, characteristic restrictions, reducedness, semisimplicity nor a bijective antipode is needed.

I checked small cases against the formulas. For H=k, rho(f)=1 tensor f and the action is ordinary scalar multiplication. For a group algebra of a finite abelian group, on a dual basis functional d_g one gets rho(d_g)=g tensor d_g, which verifies the coaction direction. For the commutative function algebra k^G of a finite group G (including nonabelian G), with b_t evaluation at t, rho(b_t)=sum_b delta_b tensor b_(tb); this tests the reversed coproduct identity without assuming cocommutativity. For the nonreduced algebra k[t]/(t^2) in characteristic 2, Delta(t)=t tensor 1+1 tensor t and S(t)=t, the dual basis f_0,f_1 has rho(f_0)=1 tensor f_0+t tensor f_1, rho(f_1)=1 tensor f_1, and t.f_1=f_0; the compatibility equation holds directly. Zero f and zero h make both sides zero. An empty basis cannot occur for a Hopf algebra over a field with unital counit to k; the coordinate argument nonetheless has no empty-sum defect.

Against delivery-errors B-E: every needed notion is inline or in the unchanged statement dependencies; no new nodes duplicate a clause or a source tag; the proof uses statements, not proofs of cited nodes; all uses are in proof_deps and have literal quotes in citations.json; and no claim of flatness or tensor exactness is used. All six steps are short explicit calculations (each under 1000 characters), with no long-step hidden lemma. The only nontrivial general algebra input is the existing convolution Mathlib leaf. No SGA source is used, and no Lean file, compiler, build tool, repository file or launcher file was written.

## Unfinished work

None in this one-level split. The local copies of the two external sources remain WANTED as explained above. Server dry run and delivery status are recorded by the delivery command.
