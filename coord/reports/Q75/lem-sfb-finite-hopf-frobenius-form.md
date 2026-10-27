# Stage-1 delivery: lem-sfb-finite-hopf-frobenius-form

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-hopf-frobenius-form.json: item, split; statement unchanged, four assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-dual-hopf-module.json: statement, unsplit; no Mathlib match for the explicitly specified action and coaction and their compatibility.
- dag/nodes/sec-six-functors-basics/lem-sfb-hopf-module-fundamental.json: statement, unsplit; no Mathlib match for the action isomorphism from the tensor product with coaction coinvariants.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-linear-injective-surjective.json: statement, Mathlib leaf; LinearMap.injective_iff_surjective_of_finrank_eq_finrank, Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean:197.
- citations.json: seven verbatim statement quotations, one per cited node per proof step.
- searches.jsonl: actual msearch.py records. prepare.py preserves the exact draft-generation data in this sandbox.

## Attachments

None. Searched all of lean/WeilConjectures/ for the item's blueprint id, FrobeniusAlgebra, HopfModule, Hopf module and Frobenius functional. No project declaration states the item or either Hopf-module input. A basis-dependent equivalence with a dual space does not state the required multiplication-functional formula.

## Wanted literature

WANTED: Siqi Clover Zheng, Frobenius Algebra Structure in Hopf Algebras and Cohomology Ring with Poincare Duality (17 October 2020), Proposition 4.12(2), Theorem 4.13, proof of Theorem 4.14 and Theorem 4.8, printed pp.8–10, for the item and lem-sfb-finite-dual-hopf-module. Expected local file literature/zheng-frobenius-algebra-hopf-2020.pdf. I read these places online at https://math.uchicago.edu/~may/REU2020/REUPapers/Zheng,Siqi.pdf . The item was already sourced to this absent local file; no download or repository change was made.

WANTED: Rolf Farnsteiner, Hopf Modules and Integrals: The Fundamental Theorem (5 April 2006), theorem printed p.2 and proof p.3, for lem-sfb-hopf-module-fundamental. Expected file literature/farnsteiner-hopf-modules-fundamental-2006.pdf. Read online at https://www.math.uni-bielefeld.de/~sek/select/HopfMod1.pdf .

WANTED: Rolf Farnsteiner, Hopf Modules and Integrals: The Space of Integrals (26 April 2006), displayed action and coaction on printed p.1 and theorem proof on p.2, for lem-sfb-finite-dual-hopf-module and comparison of the assembly argument. Expected file literature/farnsteiner-hopf-modules-integrals-2006.pdf. Read online at https://www.math.uni-bielefeld.de/~sek/select/HopfMod2.pdf .

## What was wrong or incomplete

The item had no proof, although its predecessor self-injectivity node already relied on it. Its statement is correct and has not changed. Its named literature file is absent. The online source gives enough detail to specify the dependencies, but the local-document convention requires proof_origin.by = agent, which I retained explicitly.

Zheng Definition 4.11 calls the coaction H-linear without clearly displaying the action on H tensor M; its next sentence discusses the free Hopf-module action (multiplication on the first factor). These are different actions: compatibility uses the diagonal coproduct action on H tensor M. The new statements write the precise diagonal formula, as Farnsteiner HopfMod1 p.2 does, so they cannot accidentally assert linearity for the first-factor-only action. The coaction in Proposition 4.12 is characterized by convolution. I rewrote it in the equivalent pointwise form (id tensor ev_x) rho(f) = sum f(x_1) x_2. This fixes the types and tensor order explicitly without changing the source's construction.

The current latest blueprint (main-20261024, commit ef6f9619fdbffa59e88528fb56483d76c70258c8) has no finite Hopf theorem. I read its sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md alongside the recorded chapter and unit. This remains a generic algebra prerequisite in the inherited chain, not a replacement of a unit step. The ancestor command returns None, inherited as null. No fabricated blueprint ancestor or unit realization is added.

## Unfinished work

The two Hopf-module inputs are deliberately statement-only nodes, to be split in subsequent stage-1 work. No Lean was written, no compiler or build tool was run. No other part of the item remains unstated or unjustified modulo those two explicit inputs and the cited Mathlib leaves.

## Not duplicates

lem-sfb-hopf-module-fundamental vs lem-sfb-relative-hopf-module-kernels: the latter constructs a quotient-coalgebra relative Hopf-module category, induced modules and kernels, not the isomorphism H tensor M^coH to an arbitrary Hopf module M.

lem-sfb-hopf-module-fundamental vs lem-sfb-relative-hopf-counit-criterion: the latter supplies conditions for a relative adjunction counit under a coideal retraction, not the unconditional ordinary Hopf-module theorem with the scalar base field.

lem-sfb-hopf-module-fundamental vs lem-sfb-coideal-canonical-tensor-isomorphism: that node compares H tensor_A X with (H/HA^+) tensor_k X, not H tensor_k M^coH with M.

lem-sfb-finite-dual-hopf-module vs lem-sfb-linear-dual-dimension-rank: the latter gives finite dimensions and ranks of dual linear maps, with no Hopf action or coaction.

lem-sfb-finite-dual-hopf-module vs lem-sfb-finite-hopf-frobenius-form: the new node only constructs compatible module/comodule data; it asserts no integral, no nonzero coinvariant and no nondegenerate pairing. The argument producing a functional and proving its pairing bijective is in the item.

lem-sfb-finite-linear-injective-surjective vs lem-trf-equal-dimension-linear-equivalence: the latter says some isomorphism exists between the two spaces. The new Mathlib leaf says a specified linear map is injective iff surjective. The existential assertion does not assert that property for the specified map.

Whole-DAG statement/match searches for Hopf module, coinvariant, Frobenius functional, equal finite dimensions, and the Mathlib declaration found no duplicate. blueprint_refs.py search was run for Hopf, Hopf module, Frobenius functional, linear dual and equal dimension. The Hopf hits det-d-geometry and sk-d-geometry concern affine algebraic groups, not these theorems; linear dual hits concern Weil representations/sheaf duality. No new node has a Stacks tag, because none of these Hopf-module statements is supplied by Stacks. No SGA source is used.

## New node arguments for later workers

The fundamental theorem follows Farnsteiner HopfMod1 p.3. For rho(m) = sum m_-1 tensor m_0 put P(m) = sum S(m_-1) dot m_0. Compatibility, coassociativity and the antipode cancellation identities give rho(P(m)) = 1 tensor P(m). The inverse to E is m mapped to sum m_-1 tensor P(m_0). Multiplying that tensor gives m by the counit identity. Applying the inverse to h dot c, with c coinvariant, gives h tensor c by the other antipode cancellation identity. This is a genuine general structural lemma, not a restatement of the Frobenius-functional item.

For the dual construction, a finite basis e_i with dual e_i^* gives rho(f) = sum_i ((f tensor id) Delta(e_i)) tensor e_i^*. This proves existence and the characterization proves uniqueness. Testing by evaluation shows the coassociativity and counit identities. To check compatibility, evaluation of the desired right side at x is sum h_1 f(S(h_3) x_1) S(h_2) x_2. In the commutative algebra, the first and third h factors cancel using the antipode identity in the iterated coproduct, leaving sum f(S(h) x_1) x_2, which is the evaluated left side. The action is unital and associative by the antipode identities (in the commutative case S is already an algebra map in our explicit hypothesis). All of this proof material stays in the report, not in the unsplit new node's statement or proof field.

## Review by Q75

I read delivery-errors B–E in both copies and compared them with the actual JSON statements and each of the four proof steps. The item follows the Hopf-module argument at Zheng pp.8–10, independently checked against Farnsteiner HopfMod1 pp.2–3 and HopfMod2 pp.1–2. The two new unsplit nodes contain only statements and definitions of their data, with every object and compatibility formula introduced; their source places are the ones just listed. The third node is an exact Mathlib specialization: I read the full declaration and proof at FiniteDimensional/Lemmas.lean:197–205, including both finite-dimensional hypotheses and equality of dimensions. I also read Dual/Lemmas.lean:507–517 to verify the existing dual-dimension leaf's clauses, and the complete statements of the tensor definition and the relative-Hopf candidate nodes before using or excluding them.

Step 1 takes the action and coaction identities from lem-sfb-finite-dual-hopf-module; its statement supplies all the fundamental theorem's hypotheses, over exactly the given field and commutative Hopf algebra. lem-sfb-hopf-module-fundamental supplies the actual map E(h tensor f)=h dot f and its bijectivity, not merely an unspecified vector-space equivalence. The tensor definition says pure tensors generate, so if C were zero the source of E would be zero; epsilon_H is a nonzero linear functional because epsilon_H(1)=1, so its target is nonzero. This deduction requires no unrecorded dimension theorem or basis-extension lemma.

Step 2 uses precisely the tensor universal property stated in def-weil-pbc-module-tensor-product. A nonzero functional lambda has an x_0 on which it is nonzero. On C, evaluation at x_0 divided by lambda(x_0) is a linear functional taking lambda to 1. The displayed bilinear map t(f)h consequently induces a left inverse to j. The only remaining operation is composition with the already proved injective E, and the formula for T is the previously cited action formula. This is a few-line elementary deduction, not a new node.

Step 3 writes out why S(h)=0 implies h=0 by T's injectivity, and then uses the exact Mathlib leaf on the linear map S:H to H. The item supplies a finite basis, which gives finite-dimensionality; its source and target are literally H so their dimensions agree. I do not assume antipode bijectivity as a separate uncited theorem. Step 4 checks that multiplication and lambda make Phi linear; surjectivity of S gives the chosen h, and commutativity gives lambda(ax)=lambda(xa). Vanishing of Phi(a) then implies vanishing of T(h), hence a=0. The existing lem-sfb-linear-dual-dimension-rank statement supplies both finite-dimensionality of H* and its dimension equality with H, exactly the hypotheses required to apply the new linear-map leaf to Phi. This proves the actual formula required by the item. citations.json records a verbatim piece of each cited node's statement, and all seven quotes were checked as substrings programmatically.

I tested the small cases rather than assuming a trace form works. For H=k the functional lambda=id works and the fundamental theorem reduces to k tensor M = M, including M=0. The zero algebra cannot satisfy epsilon_H(1)=1 over a field, so the choice of a nonzero coinvariant has no excluded valid case. For H=k^G, for a finite group G (including nonabelian G), lambda=sum_g ev_g gives a diagonal perfect product pairing. On the dual, rho(ev_g)=sum_t delta_t tensor ev_(gt) and delta_s dot ev_g is ev_g precisely when s=g^-1, zero otherwise; substituting checks diagonal compatibility even without cocommutativity. The coinvariant lambda is nonzero in characteristics dividing |G|, even though lambda(1) may be zero. For H=k[t]/(t^p) in characteristic p with primitive t, the coefficient of t^(p-1) is a coinvariant and its multiplication matrix is antidiagonal with ones. This includes p=2 and tests nonreduced algebras, so no separability, reducedness, characteristic-zero or normalized-integral hypothesis was smuggled in. For the linear-map leaf, V=W=0 also satisfies both sides; unequal dimensions are explicitly outside its hypothesis.

I corrected the potential action-on-tensor ambiguity before writing the nodes and kept the item's statement unchanged. I ruled out elementary and duplicate nodes: the tensor left inverse is an inline elementary step; the two Hopf-module lemmas are independent structural facts and neither states a clause of the item; the equal-dimension criterion is an actual Mathlib leaf. All non-elementary steps are shorter than 500 characters, and the whole assembly is under 3000 characters. New statements have no embedded proof sketches, proof lists or proof dependencies. All records preserve the inherited blueprint fields and full via chain. Every search recorded for a new node was actually run through msearch.py; all service responses here were available, and their hits were read before the verdicts were entered.
