# Q02 stage-1 report: lem-sfb-steinberg-weyl-restricted-freeness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-steinberg-weyl-restricted-freeness.json: item, statement unchanged, now split into six steps. No Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-restricted-pbw-top-pairing.json: new statement-only algebra lemma, unsplit; no Mathlib match. It states the truncated PBW basis, its character weights, and nondegeneracy of its top coefficient pairing. It has no module of sections in its statement.
- citations.json: one verbatim supporting statement excerpt for each node citation in each item step.
- searches.jsonl: unedited search-command log. prepare.py is sandbox-only preparation code, not a project file.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by Steinberg, Weyl module, restricted enveloping and PBW. The matches are Lang–Steinberg for semilinear Frobenius, not this representation theorem. There is no matching project declaration to attach.

## WANTED

WANTED: literature/mathieu-tilting-modules-2000.pdf, Theorem 1.2 and Corollary 1.3 (printed p.149), Lemma 2.3 (p.155), and Theorem 2.6(i) proof (pp.156–157), for the item and lem-sfb-restricted-pbw-top-pairing. Read the original paper online at https://www.imsc.res.in/~knr/vdk/mathieu.pdf; did not download or write the repository. The item retains an agent proof_origin because the document is absent locally. The source's scope is simple groups; the argument uses only Borel root coordinates and restricted PBW, and applies unchanged to a semisimple group with several factors (or directly to its whole positive root system).

## Audit of the starting item and route

The statement is correct with the specified sign convention. There is no STATEMENT-DISPUTED correction and no change to statement or stmt_deps. The original item had no proof. Its source deliberately places this result before Kempf vanishing and the Weyl dimension formula. Those downstream nodes depend back on the flag Frobenius pushforward, which itself cites this item, so they cannot supply the dimension comparison here. The split proves the kernel vanishes directly.

Read the chapter and unit records, the latest blueprint's sk-thm-sf-ctf-stability section/proof and direct-image route, and the inherited created-item chain. The existing blueprint.from.node is null; blueprint_refs.py ancestor prints None. Retained that null and the entire existing via chain, appended this item for the new node, and supplied the exact supporting PBW place. Blueprint searches for restricted enveloping, PBW, restricted Weyl, truncated PBW, top coefficient pairing, distribution, and the item's wording found no equivalent blueprint node. The route remains the existing representation-theoretic prerequisite of det-thm-sf-ctf-stability-direct-images proof (3), with no unit/chapter edit.

## Mathlib and duplicate searches

Ran all searches through the required msearch.py command. For the new node, two LeanFinder phrasings asked for restricted PBW and the perfect top-coefficient pairing; Loogle UniversalEnvelopingAlgebra, LeanSearch restricted PBW/top pairing, and grep restricted|PBW|Frobenius under Algebra/Lie were also run. A broader grep for RestrictedEnveloping|restrictedEnveloping|Poincar|Birkhoff|FrobeniusAlgebra returned mostly dynamics matches, so that broad query is not taken as evidence of absence; the focused Lie search and source read are the relevant check. Read Mathlib/Algebra/Lie/UniversalEnveloping.lean around lines 40–100: its quotient imposes the bracket relation only and has no p-operation or truncated PBW theorem. Returned Lie chain and root-pairing theorems concern ordinary Lie weights, mostly characteristic zero. Subspace.dualPairing_nondegenerate concerns the evaluation pairing, not the multiplication/top-coefficient pairing on this quotient.

For the item, two LeanFinder phrasings asked for Steinberg Weyl freeness and for the regular first-Frobenius-kernel module; LeanSearch, Loogle RestrictedEnveloping and grep Steinberg|steinberg|restricted.envelop were also run. Rep.diagonalOneIsoLeftRegular concerns the diagonal representation of an abstract monoid, and the other regular representation hits are abstract finite-group representation identities. None identifies the specified section dual or its differentiated rational action. Actual query texts and returned names are copied from searches.jsonl into the applicable mathlib_searches; none of the services was unavailable.

Searched the whole DAG for restricted enveloping, PBW, Corollary 1.3, Theorem 1.2, lowest-weight/distribution generation, and Frobenius forms, and searched project Lean for the same concepts. Reused both existing distribution nodes rather than creating restricted Weyl cyclicity as a new node. The following are the nearest overlapping existing statements.

## Not duplicates

lem-sfb-restricted-pbw-top-pairing vs lem-sfb-unipotent-restricted-enveloping-augmentation: the existing node gives dimension and nilpotent augmentation plus the differentiated action, but no PBW basis, weight spaces or multiplication pairing. The new node supplies those missing algebraic facts for a general reductive Borel, and does not assert augmentation nilpotence.
lem-sfb-restricted-pbw-top-pairing vs lem-sfb-kostant-integral-pbw: the existing node is the integral divided-power basis in an ordinary enveloping algebra of a split semisimple rational Lie algebra; the new node is the finite restricted quotient of a positive-characteristic nilpotent radical and its pairing.
lem-sfb-restricted-pbw-top-pairing vs lem-sfb-rational-pbw: the existing node concerns ordinary enveloping algebras over Q, not the p-relations or the finite top pairing.
lem-sfb-restricted-pbw-top-pairing vs lem-sfb-finite-hopf-frobenius-form: the existing node assumes a commutative Hopf algebra and gives some Frobenius functional. The radical's enveloping algebra is generally noncommutative; moreover the proof requires the specific top-weight functional, not an unspecified functional.
lem-sfb-restricted-pbw-top-pairing vs lem-sfb-induced-dual-lowest-distribution-generator: the existing node supplies a cyclic section dual over the full distribution algebra and the root rank-one annihilation relations, not a basis or pairing on the restricted algebra.
lem-sfb-restricted-pbw-top-pairing vs lem-sfb-borel-simple-root-distribution-calculus: the existing node supplies generators and adjoint multiplication identities in the distribution algebra, not the restricted PBW basis or the top pairing.
lem-sfb-restricted-pbw-top-pairing vs lem-sfb-restricted-induced-infinitesimal-invariants: the existing node computes Lie invariants of restricted induced modules, not an algebra pairing; it cannot establish the annihilator argument by itself.
lem-sfb-restricted-pbw-top-pairing vs lem-sfb-steinberg-weyl-restricted-freeness: the new node contains no flag line bundle, section module, Weyl module or highest-vector orbit map. The item still proves cyclicity and injectivity; the new node does not restate its conclusion or a clause of it.

## Review by Q02

I read Mathieu's restricted algebra definition, Theorem 1.2 and the proof of Corollary 1.3 on pp.148–149; the definitions of the induced and Weyl modules and Lemma 2.1 on pp.153–154; the full displayed divided-power argument of Lemma 2.3 on p.155; and the annihilator argument of Theorem 2.6 on pp.156–157. The new node packages precisely the restricted PBW algebra and its top functional. Its character refinement follows because each ordered monomial is a T-eigenvector and a positive simple-root height is strictly positive on each root: the top character cannot be attained by a different truncated exponent vector. I also read the full statements of every node used in the proof. For the root-coordinate step I checked the stated conjugation formula and multiplication isomorphism in the existing root-parametrization and root-product nodes; their local Milne references are Theorem 21.11/21.19 and Theorem 21.68(a). No Stacks tag asserts this representation-theoretic theorem, so no unrelated Stacks tag was substituted for Mathieu.

Step 1 uses the rho-orbit node's actual simple-coroot pairings and w0(rho)=-rho, and the existing dual-lowest-distribution-generator's actual statement W_eta=H w with D_i^(n)w=0 for n>m_i. With eta=(p-1)rho, all m_i=p-1 and -w0 eta=eta. Thus its section module and contragredient are the item's V and D, with no appeal to simplicity or a character formula.

Step 2 uses the augmentation node only for existence of the restricted differentiated action; it does not take PBW or injectivity of a distribution embedding from that node. The distribution-calculus statement explicitly gives every C_(i,r)(a) in the Lie-generated algebra, the product formula, generation of H by all simple divided powers, and D_i^(b)=e_i^b/b! for b<p. This justifies the written stability calculation: terms b>=p kill w, every other term stays in A_+w. I corrected the potential implicit identification of the abstract restricted quotient with a distribution subalgebra by working with its image; no such identification is needed.

Step 3 uses the new PBW statement for a weight-vector basis and rho-orbit for the sign change. Conjugation by the chosen group element preserves brackets and pth powers of invariant derivations, so it identifies the two presented restricted algebras and their actions. The explicit formula n0(aw)=Ad(n0)(a)n0w proves cyclicity for the opposite algebra. The finite spanning sets of character vectors give all the weight bounds used later; no characteristic-zero Lie weight argument is being imported.

Step 4 uses the root-parametrization statement's scheme-theoretic conjugation formula to identify the coefficient of t^n as having character eta+n alpha. The structural Borel/root-datum statement gives the same-sign simple-root coordinates, so this contradicts the step-3 bound when n>0. The root-product statement is an isomorphism of schemes, not just a statement about geometric points, so the resulting fixation holds after every algebra extension. This verifies the extra U-fixed clause in the item. The coefficient argument uses distinct characters in the Laurent polynomial coordinate algebra; it remains valid when their differentials coincide in characteristic p.

Step 5 applies the new PBW statement to the opposite Borel, whose roots are negative. Its unique top weight is -2eta, so the weight shift in the surjective orbit map forces a preimage of the nonzero -eta vector w to have nonzero top component. Hence z d_+ is nonzero. This supplies the nonvanishing premise in Mathieu's annihilator proof without assuming the dimension formula, simplicity, or any Frobenius pushforward result.

Step 6 uses exactly the new node's nondegenerate multiplication pairing. For y in a nonzero left ideal, its left partner b yields nonzero top coefficient of by. T-stability of the kernel and coefficient extraction in F[T] place its top component in the ideal, contradicting the already proved nonvanishing. The step writes both the weight-projection justification and the left-module identity explicitly. All elementary-marked steps are short assembly/calculation from the cited statements, not missing non-elementary inputs. Each step is under 800 characters, so none conceals a long inline lemma.

Checked B1–B10: new node statement-only, objects and hypotheses explicit, source places and search outcomes recorded, no bogus leaf, no duplicate blueprint or closed Lean declaration. Checked C1–C8: each used theorem is in uses/proof_deps and quotations in citations.json are verbatim statement excerpts; no reliance on a cited proof; no off-unit proof tool is introduced. Checked D1–D5: the single algebra input is strictly smaller than the item and the six steps contain the representation-theoretic assembly, including the complete kernel argument. Checked E1–E7: the characteristic is prime, both Borels belong to the same reductive group, restrictedness follows from the integer pairing, and all weight equalities are in X(T), never in the tangent dual.

Small cases: G=1 gives A=F, top monomial 1, D=F and the same proof. For SL2, A is F[f]/(f^p), the pairing picks f^(p-1), and the extremal weight forces f^(p-1)d_+ nonzero. At p=2, weights are still integral characters, so no division by 2 or character differential comparison occurs. Repeated weights among intermediate PBW monomials cause no problem: only the top weight is unique. Products of simple factors use the union of positive root systems; the top monomial/pairing are the corresponding tensor products. I did not assume x^[p]=0 for all x, an assumption which is unnecessary here.

## Unfinished work

None for this stage-1 split. The new algebra node is intentionally unsplit. No Lean was written or compiled. Only the sandbox was modified.

## Validation

The required delivery dry run is the authoritative server validation; its result is recorded after it exits below.

Required dry run exited 0: `OK (not pushed) deliver/Q02/lem-sfb-steinberg-weyl-restricted-freeness at ca44285f965: preflight passed`. This includes the server DAG/split checks and quotation/search-log gates. A local read-only reachability audit found no path back to the item among its reachable dependencies. The pre-existing wider dependency closure includes missing references unrelated to this delivery; the authoritative server preflight passed. All newly cited nodes exist, all quoted excerpts match, and proof_deps is the union of uses.
