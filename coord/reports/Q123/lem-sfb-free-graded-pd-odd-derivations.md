## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-free-graded-pd-odd-derivations.json`: statement, now split in seven explicit steps; its mathematical statement is unchanged. No project or Mathlib attachment.
- `dag/nodes/sec-six-functors-basics/lem-sfb-pd-derivation-compatibility-closure.json`: one new statement-only unsplit calculus lemma on arbitrary strictly graded divided-power algebras; no Mathlib match.
- `citations.json`: one checked verbatim quotation for each step/node citation. `searches.jsonl` is the actual msearch log. Sandbox-only scripts record the edits and elementary coefficient checks; no Lean files were written.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, divided powers, odd derivations, and the new compatibility-locus notion. The only broad divided-power hit was the source reference in `AlgebraicGeometry/SelfTorConormalDualChart.lean`; it does not state either lemma.

## WANTED

None. The sources used are present in `literature/stacks-project/dpa.tex` and the current blueprint in `literature/blueprint/latest/`.

## Corrections and scope

The item had no proof. Stacks 09PS (lemma-get-derivation), proof (1),(2), explicitly omits the extension details and hints to proceed one variable at a time. The existing differential-adjunction result assumes a cycle and gives a square-zero differential, so it cannot supply arbitrary generator values here. I filled the omission by an explicit normal-form construction and separated the propagation calculus from this existence argument. The proof is marked agent-written rather than attributed to an argument that the source does not contain.

The inherited `blueprint.from.node` was null: the ancestor command printed `None`. I read the `created`/`blueprint` chain through `lem-sfb-admissible-direct-image`, whose `from.node` is `det-thm-sf-ctf-stability-direct-images`. The full preflight explicitly requires the null value returned by the ancestor command, so both delivered nodes retain null `from.node`; their `from.place` gives the mathematical ancestor and their via lists retain the inherited intermediate chain, adding this item for the new node. I read the latest unit section and the direct-image proof, paragraph (3), so this supporting local algebra stays on its existing route. Neither chapter nor unit records are changed. Searches of all imported blueprint nodes for `divided power`, `divided`, `odd derivation`, and `monomial basis` found no corresponding blueprint statement.

No statement dispute was found. The pre-existing adjunction node already corrects the known typo in Stacks 09PI: the iterate coefficient is `(nm)!/(n!(m!)^n)`. I use that corrected node, not the false coefficient-free iterate formula printed in the example.

## Unfinished work

The new calculus lemma is deliberately statement-only, as required for a one-level split. Its future proof is described below to make its mathematical content reviewable. No part of the item's operator construction or uniqueness has been postponed into a renamed copy of the item.

## Not duplicates

lem-sfb-pd-derivation-compatibility-closure vs lem-sfb-free-graded-pd-odd-derivations: the new lemma assumes an already defined signed derivation on any graded algebra and describes the compatibility locus; the item constructs and uniquely determines a derivation on a free polynomial algebra from prescribed values.

lem-sfb-pd-derivation-compatibility-closure vs def-sfb-graded-divided-power-structure: the existing node gives the divided-power axioms with no operator; the new lemma proves their interaction with an arbitrary signed derivation.

lem-sfb-pd-derivation-compatibility-closure vs def-sfb-nonnegative-strict-graded-algebra: the existing node defines the sign and odd-square conventions, with no divided-power compatibility theorem.

lem-sfb-pd-derivation-compatibility-closure vs def-sfb-nonnegative-graded-algebra: the existing node defines a grading without even requiring commutativity; it says nothing about compatibility loci.

lem-sfb-pd-derivation-compatibility-closure vs def-sfb-divided-power-dga: that definition assumes a globally compatible square-zero differential; the new theorem assumes neither square zero nor global compatibility and proves closure of the elements on which compatibility holds.

lem-sfb-pd-derivation-compatibility-closure vs lem-sfb-divided-power-variable-adjunction: the existing node constructs graded algebras and divided powers under adjunction, with no derivation; the new lemma is calculus for an existing arbitrary algebra.

lem-sfb-pd-derivation-compatibility-closure vs lem-sfb-adjoin-dga-cycle: the existing lemma extends a square-zero differential after adjoining a variable whose prescribed value is a cycle; the new lemma has no adjunction or existence conclusion and does not require a cycle.

lem-sfb-pd-derivation-compatibility-closure vs lem-sfb-square-zero-dga-curvature: that lemma lifts an operator across a principal square-zero ring quotient and describes its curvature; the new one is an intrinsic propagation theorem over a single ring.

lem-sfb-pd-derivation-compatibility-closure vs lem-sfb-square-zero-relation-tor-obstruction: that lemma concludes failure of finite Tor dimension from a lifted relation; the new one asserts no Tor obstruction or relation-lifting result.

lem-sfb-pd-derivation-compatibility-closure vs lem-sfb-lifted-relation-curvature-class: that lemma constructs a homology class representing a relation's curvature; the new one has neither a ring extension nor homology.

lem-sfb-pd-derivation-compatibility-closure vs lem-sfb-finite-tor-ideal-generators-injective: that lemma proves injectivity of a map between ideal-generator spaces in local Noetherian rings; it does not concern the compatibility locus of a signed derivation.

lem-sfb-pd-derivation-compatibility-closure vs lem-sfb-tate-free-resolution: that lemma constructs an acyclic free divided-power DGA resolving an algebra; it does not assert the new calculus lemma for arbitrary existing signed derivations.

## Review by Q123

I read the full statements of every node cited in the seven proof steps, and the source in dpa.tex: 09PG (definition-divided-powers-graded), 09PH/09PI (example-adjoining-odd/even), 0F4I (remark-adjoining-set-of-variables), and 09PS (lemma-get-derivation), proof. For the new node I checked its four propagation assertions and the odd-product assertion against 09PG(3)-(7), rather than treating 09PS's omitted details as a proved black box. Its statement introduces the ring, algebra, grading, divided powers, signed derivation, and the compatibility set, with definition dependencies for both underlying notions. It contains no proof sketch.

Step 1 uses the polynomial-model clause of `def-sfb-divided-power-dga` and the free modules and union clauses of `lem-sfb-divided-power-variable-adjunction`. These statements really supply the exterior/divided-power normal forms. In particular, no target generator of degree e can occur in an element of degree e-1. This is what allows the induction; I did not assume the arbitrary prescribed value was a cycle. Degree-zero polynomial generators have zero operator by the required degree shift.

Step 2 uses exactly the free left-module decompositions in the adjunction statement. It constructs the map before asserting any algebraic property. In each homogeneous coefficient, both terms of the displayed formula have degree p+me-1. The element v belongs to the preceding subalgebra by step 1, and the formula is S-linear. No differential on that preceding algebra is silently assumed; only a signed derivation is in force.

Step 3 uses the even multiplication formula from the adjunction statement and the strict sign rule from `def-sfb-nonnegative-strict-graded-algebra`. I checked both coefficients after moving odd v through homogeneous b: they have the same sign (-1)^(p+q) and Pascal's coefficients add correctly. I separately included m=0 or n=0 so negative divided-power exponents are never used. This is a written calculation rather than an uncited extension theorem.

Step 4 uses the odd adjunction multiplication and the same sign convention. I expanded both mixed products and the product of two terms containing T. Since v has even degree, it commutes with b and T. The two surviving terms in differentiating the zero product have opposite signs, and the other terms contain T^2. Thus the check works in characteristic two without trying to infer square-zero from skew commutativity or cancel a factor of two.

Step 5 uses the union assertion of the adjunction node. Every element, product and prescribed value occurs in a finite stage, and the formulas agree on the preceding stage, so the union is an actual well-defined linear signed derivation. Its divided-power compatibility on each even generator is already the defining formula. The existing node states the union algebra and unique divided powers, not an unstated universal derivation construction.

Step 6 uses precisely the new closure node's assertions: even generators enter the locus by step 5, divided powers stay in it, even multiplication stays in it, and products of two homogeneous odd elements enter it. An even monomial either has no odd generators and is an even multiple of one positive divided-power symbol, or has a positive even number of odd generators and factors as two odd homogeneous elements. The normal forms of the adjunction node give the spanning assertion. Finite sums and zero then cover every positive even element. This uses the new node's statement, not a future proof or a definition in its place.

Step 7 is the elementary uniqueness argument from the free-module normal forms: the target identity forces the value on each even divided-power symbol, and the signed product rule forces all coefficient products. The restriction to P0 is zero for degree reasons. Agreement on stages implies agreement on their union. None of this uses D(v)=0.

The new node is a genuine smaller calculus input: it asserts no existence of a derivation from generator values, assumes no free algebra, and does not restate an existence/uniqueness clause of the item. Its proof requires propagation through four nonlinear operations, including the integral iterate coefficient and the strict odd-product case; it is not merely a two-line corollary of a cited theorem. For review, the argument is as follows. Differentiate the divided-power addition formula and reindex to obtain D(x+y) gamma_(n-1)(x+y). For an even multiplier a, differentiate a^n gamma_n(x); the term n a^(n-1)D(a)gamma_n(x) equals a^(n-1)D(a)x gamma_(n-1)(x), using x gamma_(n-1)(x)=n gamma_n(x). This gives compatibility of ax even when a is not itself compatible. For iterates, write B(n,m)=(nm)!/(n!(m!)^n); the differentiated left side is B(n,m)D(x)gamma_(nm-1)(x), whereas the right side has coefficient B(n-1,m) binomial(nm-1,m-1), the same integer (n=1 is the identity, with B(0,m)=1). These arguments work also for finite sums of different even degrees. For homogeneous odd u,v, n=1 is tautological, n=2 follows from (D(u)v-uD(v))uv=0 by strict odd squares, and n>2 follows because gamma_(n-1)(uv)=0; the left side is zero for all n>1. This proves all clauses without a square-zero condition on D.

I tested empty positive-generator sets (only P0), the zero ring, an exterior generator of degree one with arbitrary scalar image, an even generator of degree two with odd image, and the mixed case over Z and F2. In P=S<u,t> with degrees 1 and 2 and values delta(u)=1, delta(t)=u, one has delta^2(t)=1: this confirms the construction really allows a non-square-zero operator. For the new node, an exterior product uv satisfies the automatic clause, while x=u1u2+u3u4 has gamma_2(x)=u1u2u3u4 and must be handled by sum closure, not falsely declared divided-power-zero. Over Q, gamma_2(t^[2])=3t^[4] tests the corrected iterate coefficient. A sandbox Python check verified the two integer coefficient equalities for small m,n; these are arithmetic spot checks, not Lean validation.

I read the Mathlib search hits. `MvPolynomial.derivation_ext` and `mkDerivationEquiv` are unsigned ordinary derivations, `ExteriorAlgebra.lift` is an algebra-map universal property, and `DividedPowerAlgebra.lift` is ungraded. `DividedPowers.dpow_add`, `dpow_mul`, and `dpow_comp` are input axioms; `ideal_from_ringHom` (DPMorphism.lean:139) and `dpow_comp_from_gens` (line 237) apply to multiplicative ring maps, which D is not. `Derivation/ToSquareZero.lean` has ordinary commutative rings and a square-zero ideal, not the required graded divided-power extension. Recasting D as such a morphism would require additional nontrivial construction. Accordingly neither node is a one-line Mathlib specialization. Every search record comes from msearch.py's actual log, including second phrasings; none was invented or recorded as a match without reading it.

All seven proof steps are below 2000 characters. I checked B through E: self-contained new statement, named notions, source tags with labels, ordinary single-escaped TeX in the new JSON strings, no proof in the new unsplit node, no duplicate or relocated item clause, no unsupported non-elementary inference, no mismatched citation hypotheses, and no cycle through the ancestor's curvature theorem. All proof citations have verbatim statements in citations.json. All cited proof nodes are in the inherited unit, so no off-unit tool declaration is needed. I wrote only in the sandbox and ran no compiler, Lake, local DAG validator, or git command.

## Dry-run repair

The first delivery dry run rejected the step 7 quotation because the short odd-module phrase was under its 40-character minimum. I replaced it with the full free-module normal-form sentence (including the divided-power grading) from the same cited statement; the proof already uses exactly that normal form. No mathematical statement or proof was changed.

The second dry run required new `blueprint.from.node` to equal the ancestor command's actual result, None, rather than the mathematical ancestor inferred from the inherited chain. I restored that exact null field in both files, retaining the explicit provenance in `from.place` and the via chain. This complies with the instructed ancestor output; no tool or repository file was changed.

## Repair of returned delivery

The maintainer returned the reader-approved delivery because the statement of `lem-sfb-divided-power-variable-adjunction` had changed since review. I retained the sandbox's item proof, compatibility-locus node, report, citations and actual search log. I compared the retained item with the current live item: its statement, source, statement dependencies, chapter, unit and created record agree; live is still unsplit and there is no repair note. The delivery command rebuilds the commit over the current server DAG; no repository or launcher file was edited and no manual git command was run. The initial required dry run on the retained files exited successfully at `6f209ad9018`, before these substantive citation repairs.

I re-read the complete current statements of all existing proof citations: `def-sfb-divided-power-dga`, `def-sfb-nonnegative-strict-graded-algebra`, and `lem-sfb-divided-power-variable-adjunction`; I also re-read `def-sfb-graded-divided-power-structure`, on which the retained new node depends, and the new node itself. The adjunction's current clause (3) specifies that comparisons between finite orders preserve divided powers, are the identity on the old algebra and fix generators and hence divided-power symbols. Step 1 now explicitly invokes those comparisons, fixes each finite ordering once, and does not infer preservation of divided powers from a bare graded-algebra isomorphism. The refreshed step-1 quotation is that entire current clause, copied verbatim. Step 5 now names the completed degree stages, checks that their inclusions preserve divided powers and applies clause (4) to precisely that sequence; empty degrees are identity adjunctions. These are mathematical proof-text changes, not an unchanged re-push.

### Citation and hypothesis revalidation by Q123

For step 1, the current DGA definition supplies the underlying polynomial graded algebra without requiring us to equip P with a differential. The adjunction's clauses (1),(2) give the free module normal forms, clause (3) gives the divided-power-preserving finite-order identifications, and clause (4) gives the degree-stage union. Each stage is nonnegative and strictly graded, with divided powers, over the same commutative ring S, so the adjunction's hypotheses hold. The lower-degree argument for the prescribed v remains valid for degree one and for empty generator sets.

For step 2, the same clauses (1),(2) give exactly the left-module basis used to define the operator. For steps 3 and 4, the current even binomial multiplication and odd multiplication formulas are unchanged in mathematical content and still give the displayed sign calculations, with the strict-graded definition supplying odd-square zero as well as signs. I checked m=0, n=0, and characteristic two again. No hypothesis that v is a cycle, or that the operator squares to zero, has entered.

For step 5, clause (4) really states the union's grading and its unique divided powers restricting to every completed stage. Every product and operator value is computed in one sufficiently large stage. The equality gamma_m(T)=T^[m] is explicitly in clause (2), so the generator compatibility follows for every m, including m=1. For step 6, the retained new statement supplies all four closure operations and the homogeneous odd-product assertion; the current normal forms still span the positive even part. A monomial with an odd factor has an even number of odd factors and splits into two homogeneous odd elements; a monomial without one and of positive degree contains a positive divided-power symbol. Step 7 uses the same module decompositions and union, so the elementary uniqueness induction is unaffected. All eleven step/node quotations were checked as verbatim substrings of the current statements, using the sandbox only for the new node.

I re-read Stacks dpa.tex 09PG, 09PH, 09PI, 0F4I and the first paragraph of 09PS's proof. The source still omits the odd-operator extension, and the retained explicit construction fills that omission. The known 09PI iterate typo is already corrected in the current cited statement. The compatibility-locus node's statement and search question have not changed; its recorded searches and results were re-read and reused, rather than rerun or fabricated. Current blueprint searches for odd derivations and divided powers find no corresponding imported node; the project-source search still finds no attachment. The new node remains statement-only and is neither an existence/uniqueness clause of the item nor a two-line fact. I checked its integral iterate identity and its strict odd-product cases again, including x=u1u2+u3u4, where higher divided powers need not vanish. No new node was added during this repair. B--E remain satisfied, and every non-elementary step is below 2000 characters.

Current cited-statement fingerprints (SHA-256 of the exact decoded statement, for the review snapshot):

- `def-sfb-divided-power-dga`: `a7182256b0b95967015d5c13b395707b9ec86620d1289ba2ea299d69231ff1c9`
- `lem-sfb-divided-power-variable-adjunction`: `add2ed769f66f184997ec1e37d203ac9e84140e711a9498e2a3fc8b993a211bd`
- `def-sfb-nonnegative-strict-graded-algebra`: `224892fbbcb2cae009b397ac9e218bdba9591a5f08a5b9770358011e27f2ba72`
- `lem-sfb-pd-derivation-compatibility-closure`: `effeec71da6c0ff94fc9366f31e0cb785003ad6281f701e140e6831329446be2`
- `def-sfb-graded-divided-power-structure`: `e24a5a5f6164f0d81f171ba63fe91a3516f77e1f19c7ba10f7ae3f4464efe7bd`
