# Q66 stage-1 delivery: lem-sfb-root-datum-realization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-root-datum-realization.json: item, statement unchanged, five proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-root-datum-lattice-embedding.json: statement-only input, unsplit, no Mathlib match. Rational root/central decomposition and integral finite-index embedding.
- dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-admissible-representation.json: statement-only input, unsplit, no Mathlib match. Rational Lie algebra, full-weight representation and admissible lattice; no algebraic group asserted.
- dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-root-exponential-group.json: statement-only input, unsplit, no Mathlib match. Conditional group construction from the Lie and integral representation data.
- dag/nodes/sec-six-functors-basics/lem-sfb-central-character-sublattice-quotient.json: statement-only input, unsplit, no Mathlib match. Quotient of an already given semisimple group times a torus by an explicitly specified finite central subgroup.

Auxiliary sandbox files: citations.json and searches.jsonl. All recorded new-node Mathlib searches were executed using msearch.py and their hits read. The existing item's older search records are retained; this delivery appends fresh item searches. Four new nodes, zero Mathlib leaves. No Lean was written or compiled.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, root datum, rootDatum, root_datum and Chevalley. The hits were unrelated constructible-image or Beck--Chevalley results; there is no project declaration covering the item. Mathlib's RootDatum is not an attachment.

## WANTED

None. The source used is the locally available literature/milne-algebraic-groups_iAG2017.pdf, converted to sandbox milne.txt for reading. No forbidden SGA route is used.

## Problems found and repairs made

The item was unsplit with no proof. Its statement agrees with Milne 23.55 and Definition C.28 and is unchanged. I read the actual proof in Section 23h rather than treating the statement of the existence theorem as a proof. The proof's reduction through Exercise 21-4 must preserve central directions; realizing only the rational root system would lose them. I use the equivalent finite-central-quotient construction from a full-weight semisimple group and a torus, with the finite-index lattice explicitly specified.

Milne's surrounding discussion describes a torus by scalars on weight spaces. Taken literally as *all* independent scalars, this is too large: for the two-dimensional SL2 representation it gives G_m^2 rather than diag(t,t^-1). The exponential input defines the torus as D(P) acting by the actual weight characters, so all relations among weights are retained. Also no assertion about the Lie algebra of a particular integral form after reduction at bad primes is imported from the last sentence of 23.72. The input needed here is the group and its character root datum. These are clarifications of supporting-source prose; the imported item has no statement dispute. The assembly is explicitly marked agent-written.

The nearest blueprint ancestor is null in the current data; blueprint_refs.py ancestor confirmed that value. I retained the item's inherited place and via chain, and prefixed that chain by the item for each new node, rather than inventing a blueprint id. I read the chapter and unit records and literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (current main snapshot named by COMMITS.txt). This is an existing algebraic-group prerequisite under the inherited alteration route; it changes no unit or chapter. Whole-blueprint searches for root datum, root system, coroot, character lattice, weight lattice, Chevalley, central quotient and admissible lattice found no matching prerequisite. The admissible-lattice hits in smooth base change concern coefficient lattices, a different object.

## Not duplicates

lem-sfb-root-datum-lattice-embedding vs lem-sfb-crystallographic-positive-base: the existing Mathlib leaf proves integral independence of indecomposable positive roots for an already given simultaneous root pairing; it does not construct the rational central complement, weight lattice or finite-index embedding of a one-sided root datum.

lem-sfb-root-datum-lattice-embedding vs lem-sfb-central-lattice-enlargement: the existing statement starts with a semisimple group and enlarges its character lattice by constructing a covering group; the new lemma is only integral/rational lattice theory, has no given or constructed algebraic group, and retains central directions. The existing enlargement depends on the item and cannot be used here.

lem-sfb-chevalley-admissible-representation vs lem-sfb-induced-weyl-dimension-formula: the latter starts with an existing simply connected group and computes induced-representation dimensions. The new input constructs rational Lie data and a full-weight integral representation without assuming any group realization.

lem-sfb-chevalley-root-exponential-group vs lem-sfb-root-datum-realization: the new input assumes actual Chevalley Lie operators and a divided-power-stable lattice and proves properties of their specified matrix-generated group. It does not realize arbitrary character lattices or toral directions. The lattice construction, choice of representation and quotient are separate, necessary steps of the item.

lem-sfb-central-character-sublattice-quotient vs lem-sfb-affine-normal-quotient-geometry: the existing quotient theorem gives representability, flatness, smoothness and connectedness for an already normal subgroup. It does not prove the specified diagonalizable subgroup is central, reductivity of the quotient, or identify its root datum.

lem-sfb-central-character-sublattice-quotient vs lem-sfb-central-isogeny-borel-root-compatibility: the existing theorem assumes a reductive target and an already given faithfully flat map with central kernel. The new node constructs that quotient and proves its reductivity, identifies the kernel from the character lattice and computes the root data; this cannot be obtained by the existing theorem alone.

lem-sfb-central-character-sublattice-quotient vs lem-sfb-root-datum-isogeny-realization: the latter assumes both reductive groups already exist and realizes a map between them; the new lemma constructs a quotient from a specific already existing source group and a specific central subgroup, with no given target group.

## Review by Q66

I checked B--E against the actual statements and source. For the item I read Milne 23.55, printed p.501, Section 23h, pp.503--511, Exercise 21-4, p.461, and Appendix C.28--C.44, pp.613--618. The item is about character lattices, not differentials, and the proof never infers group data merely from a characteristic-p Lie algebra. In particular I did not use the classification equivalence 23.56 to prove existence: that would be circular. I also avoided the existing central-lattice-enlargement, which depends on the item.

For the lattice input I read C.29, C.35 and C.41--C.44. Its only hypotheses are exactly the item's finite-rank lattice and reduced-root-datum axioms. The coroot-annihilator complement makes pi_V(m) pair integrally with each coroot; C=pi_Z(M) is a lattice, and j has full rational rank. I checked the degenerate case R empty: V=P=0, Z=M tensor Q and C=M. For rank one I tested M=Z w with root 2w and coroot w maps to 1 (weight-lattice form), and M=Z alpha with coroot alpha maps to 2 (root-lattice form). The latter produces index two in the weight lattice, as required.

For the representation input I read the rational extension after 23.70, the Chevalley-basis discussion and 23.71, the admissibility condition before (152), and the weight-generator choice in 23.73. Its data are rational Lie algebra and integral representation data, not a rephrasing of a root-datum realization. Nilpotence makes each exponential finite, while divided-power integrality permits reduction in arbitrary characteristic. A direct sum of fundamental highest-weight modules, with a faithful summand if needed, supplies full weight generation. For a reducible root system this is a semisimple Lie algebra and a direct-sum representation, not an unjustified almost-simple assumption. For R empty the zero Lie algebra acting on Q with lattice Z is faithful and satisfies all conditions.

For the exponential input I read (153), 23.72 and 23.73, and made its torus be the image of D(P) via the weights rather than the full block-scalar torus. Since the weights generate P, this action is a closed embedding. The SL2 standard-module example gives diag(t,t^-1), not two independent scalars. The conclusion includes its actual group-root datum with coroots; just a characteristic-zero Lie-algebra semisimplicity assertion would not suffice. This input is non-elementary and left unsplit: the source's omitted verification of the generated group's structure belongs to that node, not to an elementary step of this item.

For the quotient input I read 19.26--19.27, Exercise 21-4 and 23.5. The hypotheses require a finite-index N containing every root, so K is finite and every root is trivial on it. Its centrality, quotient reductivity, maximal torus and coroot formulas are stated as theorems, not hidden in the definition of K. I tested H=1 and arbitrary C (a torus isogeny), C=0 and N=X (identity quotient), and SL2 with N the root lattice inside P. In characteristic two the last case has K=mu_2 and target PGL2; K is nonreduced and is allowed. Its coroot evaluates to 2 on the quotient's root, while its pullback on the weight generator evaluates to 1. A prime-to-characteristic or smooth-kernel requirement would wrongly exclude this case.

Step 1 uses the lattice input's explicit E=V direct sum Z, P, C and j assertions; the file says all of these, including the root and coroot identities. Step 2 uses the representation input's actual existence of g, rho and Lambda and its full-weight and divided-power clauses; I checked all hypotheses match the reduced rational system supplied by step 1. Step 3 uses the exponential input with exactly those data and the given algebraically closed F, taking its asserted semisimple group and full root datum. Step 4 uses the quotient input; the finite-index and root-inclusion hypotheses were proved in step 1, and the semisimple group and character lattice were supplied in step 3. I checked the node supplies quotient reductivity and the coroot restriction formula, not merely quotient existence. Step 5 uses precisely the formulas in the lattice and quotient inputs; the displayed evaluation on every m proves the dual identification, and the root identification is j(alpha)=(alpha,0). It is elementary substitution into two already stated formulas. citations.json contains verbatim statements for every step/node pair, with no invented or bent quotation.

All four new statements introduce their own objects; the rational-root and representation conventions they refer to are explicit statement dependencies. No new node has proof steps or proof dependencies. None is an elementary two-line lemma, and none simply says that an arbitrary datum has a realization. The five assembly steps have lengths 431, 496, 447, 547 and 573 characters, so no long step hides a subsidiary comparison. The roots/coroots formula in the last step is written out rather than abbreviated as 'transport'. New nodes inherit the same unit and chapter. The statement-definition citations to existing Lie algebra definitions use those definitions only. No off-unit proof tool is used in the item.

I read the semantic, Loogle and grep hits for each new node and tried a second semantic phrasing. RootDatum and RootSystem.mk' describe abstract pairings; GeckConstruction gives Lie algebra objects. The closest rational candidate is RootPairing.isCompl_rootSpan_ker_rootForm with ker_rootForm_eq_dualAnnihilator (Finite/Nondegenerate.lean:271--310); those are only part of the lattice input and assume the paired axioms rather than the item's one-sided definition. Basis/Basic.lean explicitly leaves Chevalley bases as TODO. No leaf was declared on the strength of a name or an unavailable service.

## Unfinished work

The four new nodes are intentionally statement-only inputs to the next level of stage 1. No other part of this item remains to be split. Delivery validation follows below.

The first server dry run returned one B3 metadata issue: the lattice input had inline definitions but no node citation at all. I opened def-weil-pbc-free-module and def-weil-submodule-span and added their precise definition citations and statement dependencies. The former defines a basis/free module; over Z with a finite basis it is exactly the finite-rank free abelian group used here. The latter defines the smallest scalar-closed additive subgroup containing a set, exactly the rational root span. These are definition dependencies, not off-unit proof tools. No proof or statement conclusion changed. Regenerated citations.json from the updated statements.
