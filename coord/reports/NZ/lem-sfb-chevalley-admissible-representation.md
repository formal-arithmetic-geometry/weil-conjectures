# Stage-1 report: lem-sfb-chevalley-admissible-representation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-admissible-representation.json: split, unchanged statement; eight proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-serre-rational-presentation.json: statement, unsplit; no Mathlib match. The specific Serre quotient, not an abstract repeated existence clause.
- dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-root-normalization.json: statement, unsplit; no Mathlib match. Extends an arbitrary prescribed simple-root pinning in a given split algebra.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-highest-weight-modules.json: statement, unsplit; no Mathlib match. Arbitrary dominant integral highest weights over Q, including cyclicity and ordinary weight decomposition.
- dag/nodes/sec-six-functors-basics/lem-sfb-kostant-integral-pbw.json: statement, unsplit; no Mathlib match. Integral ordered basis of the noncommutative enveloping ring, independent of any module or lattice.
- citations.json: one verbatim node-statement quote per use per step.

Four new statement-only nodes, zero new Mathlib leaves. All new nodes inherit the item's chapter and unit. No Lean, compiler, git command, or repository write was used. Temporary extraction and writing scripts are confined to the assigned sandbox.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and Chevalley, admissible lattice, highest weight, Kostant and SerreConstruction. The Chevalley hits are scheme-theoretic constructibility, valuation extensions, or Beck--Chevalley comparisons, not Lie-theoretic realizations. No sorry-free declaration states the item.

## WANTED

WANTED: Serre, Complex Semisimple Lie Algebras, Chapter VII (dominant highest-weight existence and its split rational-field construction), for lem-sfb-rational-highest-weight-modules.

WANTED: Kostant, Groups over Z (1966), integral enveloping-algebra basis theorem, and Steinberg, Lectures on Chevalley Groups (1967), initial integral-form construction, for lem-sfb-kostant-integral-pbw. These sources are cited by Milne but are not in this read clone. They were not downloaded or added to the read-only literature directory. This delivery explicitly leaves their theorems as statement-only work, rather than claiming that Milne proves integral PBW. An online search located Humphreys §§26.4--27.1 as an additional reference, but that scan was not used to pretend the missing source was locally read.

## What was wrong and what changed

The original node had no proof. Its statement is retained verbatim. The construction follows Milne §23h, read from the local PDF, printed pp.503--511, with Appendix C.21--C.26 on pp.612--613. The current latest blueprint is literature/blueprint/latest -> main-20261024; I read the direct-image proof (3) and the chapter and unit records. This deeply nested Lie-theoretic support stays below the inherited root-datum realization route. No chapter or unit is changed. blueprint_refs ancestor returns None: the existing ancestor chain is already null, and the new records faithfully prepend this item to the inherited via list rather than invent an imported ancestor.

## Source error

Milne p.504's printed presentation has transcription/sign errors: the second relation must be [X_i,Y_i]=H_i, the Y relation [H_i,Y_j]=-a_ij Y_j, and the Serre exponent 1-a_ij, with Y_j rather than J_j. Our presentation explicitly uses those correct relations. The wrong exponent a_ij+1 is zero for adjacent type A2 roots (a_ij=-1) and would force the nonzero generator X_j to vanish. Thus copying the printed formula literally would not construct the claimed algebra.

Milne p.511's proof of Corollary 23.73 cites Lemma 22.24 for the fundamental-weight choice. Read against p.469, that lemma supplies only a positive multiple d_i omega_i. These need not generate P: in rank one, the adjoint representation has weights 0, plus/minus alpha and generates Z alpha = 2 Z omega, strictly smaller than P. The replacement input is the split rational highest-weight theorem, stated for arbitrary dominant weights; no already constructed group or simply-connected classification is used, avoiding a cycle through this item.

Milne p.510 asserts admissible lattice existence and cites Chevalley (1961); equation (152) cites Borel. The delivery constructs the lattice U_Z v and proves its decomposition directly. Integral PBW is separately stated, never hidden as an elementary fact. We use no positive-characteristic claim that every Chevalley Lie algebra is semisimple (Milne p.509's unrestricted phrasing fails, for example, for sl2 in characteristic two). Our statements concern Q only.

## Not duplicates

lem-sfb-serre-rational-presentation vs lem-sfb-chevalley-admissible-representation: the new theorem specifies and verifies a Serre-relations quotient, including base existence; the item must still normalize that algebra and construct a faithful full-weight integral representation.

lem-sfb-chevalley-root-normalization vs lem-sfb-chevalley-admissible-representation: the new theorem starts with a given split Lie algebra and arbitrary prescribed rational simple-root vectors, and extends them; it constructs neither an algebra from R nor a representation or lattice.

lem-sfb-rational-highest-weight-modules vs lem-sfb-chevalley-admissible-representation: the new theorem is the highest-weight theorem for every dominant weight; its modules need not be faithful and no integral lattice is asserted. The item constructs a finite sum, proves faithfulness and constructs its lattice.

lem-sfb-kostant-integral-pbw vs lem-sfb-chevalley-admissible-representation: the new statement is an integral basis theorem in an infinite-dimensional enveloping algebra and mentions no lattice in a representation. The item's finite-generation and homogeneous-lattice argument is separate.

lem-sfb-serre-rational-presentation vs lem-sfb-chevalley-root-exponential-group: the latter requires the completed Lie basis, faithful full-weight representation and admissible lattice as input, and constructs a group over a field. It supplies no Serre quotient theorem.

lem-sfb-chevalley-root-normalization vs lem-sfb-chevalley-root-exponential-group: the latter assumes all Chevalley basis identities; the new theorem normalizes root vectors in an arbitrary given rational split algebra.

lem-sfb-rational-highest-weight-modules vs lem-sfb-simple-module-dual-highest-weight: the existing theorem is about uniqueness and duals of rational modules of an already given algebraic group over an algebraically closed field; the new theorem constructs Lie modules over Q for arbitrary dominant integral weights. Using the group theorem here would introduce the wrong hypotheses and potentially the root-datum realization cycle.

lem-sfb-rational-highest-weight-modules vs lem-sfb-simply-connected-character-lattice: the latter starts with an existing simply connected algebraic group and identifies its characters. It depends transitively on our item, so cannot supply the Lie-module existence input.

lem-sfb-kostant-integral-pbw vs lem-sfb-chevalley-root-exponential-group: the latter assumes divided-power stability of a lattice and builds root-exponential groups, not the integral enveloping basis.

lem-sfb-serre-rational-presentation vs lem-sfb-crystallographic-positive-base: the existing node concludes linear independence of certain positive indecomposables, not base existence, rational semisimple Serre realization, or root-space identification.

Whole-DAG searches inspected statement fields, not just search-result text, for Chevalley basis, Serre relations, highest weights, admissible lattices, PBW and Kostant. blueprint_refs searches of Chevalley, highest weight, Cartan, semisimple Lie, Serre, Kostant, PBW and 23.71 found no equivalent imported blueprint statement. The same_as fields are empty. The only blueprint Chevalley hit is the unrelated constructibility theorem. No Stacks tag describes these Lie-theoretic facts; sources are the actual Milne places, not fabricated Stacks tags. The generic finite-free subgroup result already exists and was reused.

## Review by NZ

I read Milne's Serre proof and rational extension, the Chevalley-basis paragraphs and Theorem 23.71, the admissible-lattice definition and equation (152), and the proof of Corollary 23.73. I checked Appendix C's definitions of roots, simple bases and weight lattices and compared the cited Lemma 22.24 with its actual conclusion. The four new statements each introduce their objects and give hypotheses rather than referring to a tag for meaning. They have no proof or proof_deps, because this is a one-level split. For the highest-weight and integral-PBW inputs I distinguish Milne's summary from a full proof and list the absent primary sources above. The overall proof is marked agent-written for this reason.

Step 1 directly verifies the empty case, including injectivity from zero, the nonzero one-dimensional W and the zero weight. Step 2 uses exactly the Serre node's rational semisimplicity, root-space and coroot identification, then the normalization node's extension and bracket constants. The rational split hypotheses of the second theorem are supplied by the first. Step 3 uses the highest-weight node's Z-basis of fundamental weights, existence of modules and integral finite ordinary weight sets. It takes direct sums explicitly; it never assumes a faithful irreducible representation exists for a reducible algebra. Step 4 cites the representation identity in def-wf-lie-algebra, and writes the polynomial eigenspace projections and ideal argument proving faithfulness. The fundamental-weight basis and the root decomposition are already in force from Steps 2--3; no unproved kernel theorem is used.

Step 5 cites the actual integral triangular-basis statement, including the integral span and generator action, and the highest-weight module's cyclic vector and positive-root annihilation. Its hypotheses require the Chevalley normalization obtained in Step 2. It defines Lambda_i as an actual subgroup and verifies divided-power invariance by closure of U_Z, not by clearing an unbounded family of denominators. Step 6 explicitly bounds the number of nonzero negative monomials by height difference in the finite set of module weights. Homogeneous generators then give the weight-intersection decomposition without invoking the unproved Borel assertion for an arbitrary lattice. Step 7 uses the statement of lem-weil-subgroup-finite-free-abelian-group-free, which actually gives finite freeness for subgroups of Z^J. A single denominator clears the now finite generating family, satisfying its finite-index-set hypothesis. The rational-span and tensor-product claims are justified by clearing rational coefficients in a relation on the integer basis. Step 8 again cites the representation identity and calculates the weight shift. Finite weights and nonzero alpha give a uniform nilpotence bound. All citations have been checked against their full statement text and quoted verbatim in citations.json; the two appearances of the highest-weight node use quotes for the respective clauses.

For small cases I tested A1: the Serre algebra is sl2, omega=alpha/2 occurs in its two-dimensional module, U_Z v gives the familiar two-generator lattice and shows why the adjoint module alone fails to generate P. A product A1+A1 is handled by separate fundamental modules, one for each factor; the kernel argument detects both factors. The empty root system is handled independently; no vacuous sum is mistaken for a nonzero highest-weight vector. For A2 the corrected Serre exponent is 2 rather than the erroneous 0. For the trivial highest weight in the general input, L(0)=Q and U_Z acts by integers; integral PBW at rank zero is Z. Arbitrary rational rescalings of a simple-root pinning are allowed in normalization; negative-root scaling is reciprocal and does not require irrational square roots.

The Mathlib searches were executed only through msearch.py, logged as returned and read. Matrix.ToLieAlgebra is a quotient construction, not its finite-dimensional semisimplicity theorem; LieAlgebra.Basis explicitly leaves Chevalley bases TODO; weights and irreducibility predicates do not assert dominant highest-weight existence; UniversalEnvelopingAlgebra.lift does not assert integral PBW. I read the cited source files and candidate declarations. RootPairing.nonempty_base does establish base existence for a paired root system, but this does not make the entire Serre-presentation theorem a one-line leaf. No search that did not run is claimed. No source was used from SGA.

All steps are under 2000 characters. The nontrivial reusable theorems are separate nodes; the explicit lattice assembly stays in the item and is not relocated into a duplicate lemma. No statement was weakened, no hollow data were added, and no cycle through the group realization or simply-connected-character theorem was introduced. The generic subgroup leaf is already a Mathlib leaf and needs no off-route tool-use declaration.

## Unfinished work

None within this one-level split. The four new unsplit statements are deliberately future DAG work, with the missing full references explicitly identified. Delivery awaits the required server dry run and push.

The first complete delivery dry run detected that the citation parser did not recognize grouped definition references. I expanded them to separate [def-...] references in the three affected supporting statements; their hypotheses and mathematics are unchanged. Standalone check_dag and review_split had already passed.
