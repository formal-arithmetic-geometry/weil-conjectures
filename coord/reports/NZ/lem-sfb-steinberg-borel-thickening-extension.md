# Stage-1 delivery: lem-sfb-steinberg-borel-thickening-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-steinberg-borel-thickening-extension.json: item split into four steps, statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-specialization-highest-weight-dimension.json: new statement-only lemma, unsplit; no Mathlib match. It gives a rational highest-weight module of classical Weyl dimension by integral specialization, without asserting simplicity or identifying it with sections.
- citations.json: six citations, each checked verbatim against the cited statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and Steinberg/Borel/highest-weight terminology. The Steinberg hits concern Lang--Steinberg for semilinear maps, not rational representations of nonreduced algebraic subgroup schemes. No Lean was written or compiled.

## WANTED

WANTED: Kaneda, On the Frobenius morphism of flag schemes (1994), Section 2.5, pp.322--323, local copy for the item. Read the primary PDF online at https://msp.org/pjm/1994/163-2/pjm-v163-n2-p07-s.pdf, particularly (4)--(9).

WANTED: Jantzen, Representations of Algebraic Groups (2003), II.2.13 (integral Weyl modules) and II.3.18--3.19 (pre-Kempf Steinberg theorem), local copy for the new integral-specialization input and comparison with the item. The book was not locally available and I do not claim to have read these sections. The actual source read for the new node is Milne, Algebraic Groups (2017), the characteristic-zero part of 22.52 and the admissible-lattice construction at pp.509--511, (152)--(153), 23.72. The proof is marked agent-written.

## Errors and choices

The imported item is mathematically sound; no statement dispute or statement change. Its empty proof did not expose how the H_r-action extends. Merely citing the extension clause of Kaneda (9) would repeat the item. I instead construct a matrix-coefficient isomorphism from an independent rational module of the right dimension.

The existing induced-module Weyl dimension node is unavailable here: it depends through Kempf vanishing and the rho pushforward back on this item. The restricted-rho-simple-dimension and global Steinberg irreducibility nodes share that cycle. None is cited. The new general existence lemma is strictly different: it constructs some rational module with a highest vector and classical dimension, makes no induced-module assertion, and works for every dominant weight. Its intended proof is: choose the characteristic-zero simple highest-weight representation and its classical Weyl dimension; choose an admissible integral lattice with its weight decomposition; the highest-weight intersection is a rank-one direct summand, so a generator remains nonzero modulo p; reduce the divided-power root-action polynomials and torus weights to obtain a rational representation of the simply connected group with the same root datum. Rank and the Borel eigenvector identity persist. This lemma is left statement-only, so its integral realization details are future work rather than hidden steps of the item.

## Source error

The local Milne 22.52 is worded for simple modules without a characteristic restriction. That formula is false in positive characteristic: for SL_2 in characteristic p, the simple Frobenius twist of the standard module has highest weight p and dimension 2, whereas the classical product is p+1. The new node explicitly uses only the characteristic-zero formula and does NOT assert that its specialization is simple. This source error does not affect the unchanged item.

## Blueprint provenance

The inherited blueprint.from.node is null (confirmed by tools/blueprint_refs.py ancestor); it is retained, not replaced by an invented ancestor. Its long from.place records the actual chain to direct-image constructibility. Read the latest blueprint unit and direct-image proof; the extension is a supporting algebraic-group tool beneath its alteration route. No chapter or unit route is replaced. The item is not the unit's key node, so no unit realization record is edited.

## Not duplicates

lem-sfb-integral-specialization-highest-weight-dimension vs lem-sfb-induced-weyl-dimension-formula: the latter gives the dimension of an actual regular-function induced module in every characteristic and uses Kempf; the new node constructs some rational module of classical dimension by integral specialization and makes no induced-module identification.
lem-sfb-integral-specialization-highest-weight-dimension vs lem-sfb-dominant-character-highest-line: that node supplies a highest line but no dimension control; the new lemma supplies classical Weyl dimension, needed for bijectivity.
lem-sfb-integral-specialization-highest-weight-dimension vs lem-sfb-rational-highest-weight-modules: that node concerns representations of a split Lie algebra over Q and gives no rational group representation after reduction or dimension formula.
lem-sfb-integral-specialization-highest-weight-dimension vs lem-sfb-chevalley-admissible-representation: that node gives a faithful Lie representation with full-weight lattice, not a representation at a prescribed dominant highest weight with a prescribed rank.
lem-sfb-integral-specialization-highest-weight-dimension vs lem-sfb-steinberg-borel-thickening-extension: the new statement neither mentions H_r nor extends its induced representation; the item's argument uses both its dimension bound and existing infinitesimal simplicity to construct the required extension.

Whole DAG searches by highest weight, Weyl, integral/admissible lattice, Jantzen places and inducing terminology were read. Blueprint searches Steinberg, Weyl module, Weyl dimension, highest-weight and admissible lattice found no matching imported statement. The corresponding Lean searches found no attachment. Mathlib semantic hits concern Lie weight spaces (often CharZero), finite/abstract groups or Weyl reflection representations. Neither these nor the two grep comments construct the rational algebraic-group module needed. Ran LeanSearch, LeanFinder, Loogle and Mathlib grep with msearch.py; exact queries and results are recorded. Also ran a first LeanFinder phrasing concerning integral highest-weight specialization; it returned LieModule weight-space finiteness and sl2 primitive-vector facts, read and rejected. searches.jsonl retains it.

## Review by NZ

I read delivery-errors B--E, the source item and every cited statement. For the item I read Kaneda 2.5(4)--(9), where induction is on G_rB and extension is stated before the applications to Frobenius splitting. Kaneda's Borel has negative positive-system convention; our given covariance has the opposite sign already, and all applications here use the displayed positive covariance without changing it. For the new node I read Milne's characteristic-zero Weyl formula at p.480 and the lattice reduction construction at pp.509--511, including the full weight decomposition (152) and polynomial root actions (153). I confined the use of 22.52 to characteristic zero because its unrestricted wording has the counterexample recorded above.

Step 1 uses exactly the semisimple-implies-reductive clause of the Borel-pair node, the simple-coroot pairing-one clause of the rho orbit node, and the existence, highest vector and dimension clauses of the new node. The input lambda is an actual character by the item's assumption and is dominant because q-1 is nonnegative. Its given Borel character is trivial on the radical. The product cancellation occurs in Q with positive denominators, not in F; hence the answer q^N is a true dimension even for p=2.

Step 2 uses precisely the function-restriction isomorphism in the Frobenius Borel induction geometry node, with chi = rho-tilde to the power -(q-1). This matches its chi-inverse covariance exactly. The PBW node explicitly supplies rationality and dimension q^N for Z_r(eta), for arbitrary eta and all r. The simplicity node explicitly supplies a nonzero simple L_r-module, rather than global induced-module simplicity. They concern the same L_r and P_r defined by relative Frobenius. Reading these statements was essential: the existing global dimension theorem would create a cycle.

Step 3 is an elementary matrix coefficient construction from the supplied W and v. I wrote its covariance and equivariance formulas on every test algebra. The inverse transpose gives a regular group action on the dual; taking coordinate functions of hv proves regularity without a new induced-representation theorem. The same test-algebra equations prove identities of coactions on nonreduced H_r, not merely equivariance for H_r(F).

Step 4 uses the results already established in steps 1--3. The linear functional nonzero at v gives a nonzero image. Because the map is H_r-equivariant it is L_r-equivariant, and the simple target forces surjectivity. Equal finite dimensions force bijectivity. I displayed the conjugated coaction and explained cancellation for its two axioms and its restriction, so 'transport' does not hide a comparison lemma. For S=1, N=0, both sides have dimension one. Rank-one SL_2 gives a module of dimension q and the expected induced space dimension q. Reducible root systems contribute a product; every fraction is q. Neither the argument nor the new existence assertion excludes p=2 or requires division by 2 in F.

Every non-elementary assertion of the item is a cited statement. No new node is elementary or a restatement of the extension clause; the sole new node is a general integral representation construction. All four steps have fewer than 2000 characters. The new node is statement-only with empty proof and proof_deps. I kept inherited metadata and searches, supplied same_as and the inherited ancestor chain, and generated verbatim citation records. No SGA source is used.

## Unfinished work

None within the one-level split. The new statement-only integral-specialization lemma remains an item for the queue, as required.
