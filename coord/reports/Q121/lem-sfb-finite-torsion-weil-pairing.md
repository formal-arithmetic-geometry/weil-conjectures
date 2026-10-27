# Stage-1 delivery: lem-sfb-finite-torsion-weil-pairing

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-torsion-weil-pairing.json — existing statement, split into nine steps; no Mathlib match.
- citations.json — verbatim statement quotations for every cited node in every step.
- searches.jsonl — actual msearch log; the item's previous Q108 searches remain in its JSON.
- report.md — this report. prepare.py is a sandbox-only generation aid, not a delivered node or project script.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and for Weil pairing, weilPairing, weil_pairing, Poincare, finite geometric pairing, and biextension. The Weil pairings in Derived/WeilFrobenius and PoincareDuality/Frobenius are pairings of cohomological Weil objects, not abelian-variety torsion. No exact project declaration was found, and no sorry-bearing declaration is treated as an attachment.

## WANTED

None. Read the local Milne PDF, Chapter I §§8–9 and §13, printed pp.36–42 and 57–58, and local Stacks descent.tex, proposition-fpqc-descent-quasi-coherent (Tag 023T). No SGA source is used.

## Problems found and corrected

The imported item has a correct statement, which is retained verbatim. Its source cites Proposition 13.2(a),(d), but Milne states those on integral Tate modules, not directly as finite-level formulas. Merely quoting them here would either omit the finite calculation or circle through lem-sfb-abelian-weil-pairing, which already depends on this item. Instead the proof directly compares the two normalized trivializations of a Poincare-fibre tensor power. The transition, finite adjunction, and finite skew formulas are calculated on those maps. The perfectness argument descends a compatible trivialization along [m], and finishes with an explicit finite character count.

A universal-family isomorphism alone does not identify the two representing group laws. Step 1 supplies the missing rigidity argument before using the relative Poincare calculus. Likewise, pointwise translation invariance alone would not give a scheme descent datum without a reduced/split kernel. Step 4 explicitly cites the etale-field equivalence to identify the whole finite etale kernel with its constant point scheme, then identifies the whole overlap with A times that kernel. No hypothesis is added to the item.

The inherited blueprint ancestry terminates in a created node without blueprint_kind: blueprint_refs.py ancestor prints None. Retained the inherited null from.node and full via chain rather than inventing an ancestor. Read the newest literature/blueprint/latest unit and direct-images proof (3); this is an auxiliary geometric prerequisite in the inherited alteration/level-rigidity chain, and does not change the unit route.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for Weil pairing, Poincare, biextension, biadditive, Cartier dual, descent character, and torsor descent found no other statement of the item. Existing lem-sfb-abelian-weil-pairing is its rational Tate-module consequence, not a usable proof dependency (it depends on this item). Existing lem-sfb-abelian-space-poincare-calculus supplies the universal normalized identities and uniqueness; lem-pc-fpqc-descent supplies effective descent and compatible trivializations. Both are reused, rather than creating specialization nodes. The two finite-dimensional pairing nodes and the cohomological Weil nodes do not construct a finite geometric pairing. No additional node is necessary for the tensor-ratio computations or the coordinatewise finite character count.

## Mathlib search results

Ran msearch with leanfinder, leansearch, loogle and grep on this item. Read the returned signatures: LinearMap.IsPerfPair.of_injective concerns vector spaces over a field, whereas the needed construction is geometric and the finite groups are modules over Z/ell^n, generally not a field. RootPairing's perfectness is an assumed field of a root-system structure. The elliptic-curve point-map and coordinate-ideal hits supply no torsion pairing. Grep's sole Poincare hit is Dynamics/Ergodic/Conservative.lean:37, the recurrence-theorem keyword. Loogle "WeilPairing" returned no hits. The two semantic phrasings independently test the geometric construction and its torsion/dual compatibility. All actual query strings and results are recorded in the item and searches.jsonl; no unavailable service is recorded as a negative match.

## Review by Q121

I read Milne I §8's normalized difference family and representing property, Remark 8.5 on additive pullback of Pic^0 bundles, §9's dual map and character explanation, and all of §13's finite construction, Lemma 13.1 and Proposition 13.2. I used the actual local PDF, not just the node's reference. The proof is marked agent-written because it expands the finite arguments Milne leaves as exercises, using already stated geometric inputs. The statement's prime-to-characteristic condition is necessary for the etale kernel and primitive-root character count; it is checked at each such application.

Step 1 uses polarization-calculus for the item's representing dual and space-poincare-calculus for the other representing dual, not either node for an unmentioned biduality theorem. I read both statements. The latter allows schemes over every locally Noetherian base and has the needed automorphism-uniqueness clause. Spec k is such a base. The schemes in the rigidity application are copies of the abelian variety C^vee: characterization gives the geometrically connected/reduced first factor; the second is connected, the target separated and of finite type. Commutativity is supplied by av-commutative. The slice h(s,0) and value h(0,t) are explicitly zero, which identifies the group laws without assuming the conclusion.

Step 2 uses precisely the two biadditivity isomorphisms and rigidified-automorphism uniqueness in space-poincare-calculus. Applying uniqueness on C times the other parameter coordinates proves the associativity, commutativity and interchange diagrams; these are short consequences, not hidden new lemmas. Module-pullback-tensor states the actual tensor comparison and its pure-tensor action. Step 3 uses those maps and axis trivializations, constructs a scalar ratio independent of basis, multiplies ratios to prove bilinearity, and uses mx=0 to prove its m-th power is 1. It does not assume that an arbitrary bilinear map is the Weil pairing.

Step 4 uses mult-n-finite-flat and mult-n-isogeny for finite flatness and surjectivity, making the singleton fpqc (finiteness supplies quasi-compactness). Ntorsion-etale supplies etaleness. Etale-field-gsets says an equivalence for all etale schemes over a field, and with trivial absolute Galois group it gives the constant point model including morphisms; it is stronger than the mere point-count statement. Subtraction gives an actual inverse on every test scheme for the displayed overlap map. This node is a declared generic off-unit tool, not a replacement route.

Step 5 calculates the deck scalar as t2/t1 on the entire overlap from biadditivity. I read the statement of fpqc-descent: its part 3 explicitly requires compatible trivializations and concludes triviality. Here compatibility is exactly the scalar being 1, and q is the fpqc singleton established in step 4. Rescaling makes the resulting isomorphism preserve the identity rigidification, so polarization-calculus's representing property really implies b=0. No character-descent theorem is smuggled in through the proof of a cited node.

Step 6 uses the dimension equality from polarization-calculus, the explicit (Z/m)^(2g) torsion structure from ntorsion-etale for both A and its dual, and the primitive m-th root from primitive-root. The count and separation are written coordinatewise, so no general finite-group duality lemma is needed. Equal finite cardinalities convert each injection to a bijection and prove both evaluation clauses, not only one-sided nondegeneracy.

Steps 7 and 8 use the normalized biadditivity and pullback comparisons in space-poincare-calculus, not the uncited proof of that node. In step 7 both maps act on the same tensor power P(u,v)^(mr^2); each becomes the r-fold tensor power of the level mr map, producing exponent r, not r^2, in the ratio. Step 8 compares the two maps separately before taking their ratio, so dual functoriality has its required orientation. Step 9 uses the explicitly stated N_L family and commutativity of A, then swaps the first and second normalized maps, giving the inverse ratio. It never divides by 2, assumes L ample, or assumes phi_L invertible.

I checked delivery-errors B through E: no statement-only new node hides an argument; no undefined auxiliary objects or invented Stacks tags; no unrun searches; every use appears in proof_deps and has a verbatim quotation; no source proof is used as though its statement supplied a stronger conclusion; no cycles through the rational pairing; no relabelled conclusion nodes; and no elementary step carrying an unproved geometric input. All non-elementary steps are under 2000 characters. Tested A=0, n=1, ell=2, char k=2 with odd ell, a=0, L trivial, and a non-ample L. The trivial cases give value 1; the kernel proof still applies for g=0; finite skew at ell=2 is the exact conclusion and does not assert diagonal vanishing. The statement and statement dependencies are unchanged.

## Unfinished work

None in this one-level split. Its cited unsplit prerequisites remain separate existing DAG work; this delivery neither claims them proved nor substitutes a new restatement. Required server checks and delivery are recorded by the delivery tool.

## Dry-run repair

The first full preflight objected to the phrase “the item's dual pullback” in step 8 as not self-contained. Replaced it with “the dual pullback fixed in the statement”, referring to the objects introduced in this node itself. No mathematical dependency or statement changed.
