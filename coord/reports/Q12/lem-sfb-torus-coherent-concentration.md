# Q12: lem-sfb-torus-coherent-concentration

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-coherent-concentration.json`: statement unchanged, five-step agent proof, status split; not a Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-coherent-localization-sequence.json`: statement-only unsplit input for a general equivariant closed/open pair; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-nonfixed-complement-annihilation.json`: statement-only unsplit input for classwise annihilation on a possibly singular nonfixed locus; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-torus-fixed-euler-unit.json`: statement-only unsplit input for the regular fixed immersion and its invertible conormal exterior operator; no Mathlib match.
- `citations.json`: one verbatim statement excerpt for each of the six step/node citations.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint id and by torus, coherent, concentration and fixed-point concepts. Its existing coherent sheaf infrastructure and unrelated concentration results do not state this item or any new input. No sorry-containing declaration was treated as a finished proof. No Lean was written and no compiler, Lake or build tool was run.

## Wanted literature

WANTED: R. W. Thomason, *Une formule de Lefschetz en K-theorie equivariante algebrique*, Duke Math. J. 53 (1986), equivariant localization/devissage, concentration and conormal Euler invertibility, for the item and all three new inputs. The document is not present in the literature directory. I did not download it or pretend to have read it. No Stacks tag giving these equivariant results was found or invented.

## Findings and scope

Milne, *Algebraic Groups* (iAG2017), printed p.480, Theorem 22.50, is only the motivation/source anchor: the proof invokes Nielsen's general fixed-point theorem and Iversen 9.4. It does not prove concentration. I read that page with pdftotext (PDF page 492). The source field already describes the concentration lemma as agent-supplied; I preserved it and marked this proof as agent-written. No SGA is used.

The imported statement is retained exactly, with all statement dependencies. In particular the groups are integer Grothendieck groups, the fixed functor is scheme-theoretic after every algebra extension, arbitrary characteristic is allowed, and the trivial torus and empty loci are included. I found no statement dispute. The statement's introductory pullback-isomorphism direction is read as the chosen convention for the inverse linearization; the fibre action is the direction explicitly specified in the statement.

The chapter and unit records were read. This supporting node is not the unit's key theorem, so no unit record was changed. `blueprint_refs.py ancestor` reports null for the inherited ancestry; every new node keeps that null and prepends this item to the entire inherited via chain. Its place records the supporting concentration step. Searches of the current latest blueprint and all imported blueprint nodes found no equivalent equivariant coherent statement; `same_as` stays empty. No ancestor was invented to conceal the inherited broken chain.

## Not duplicates

- lem-sfb-equivariant-coherent-localization-sequence vs lem-sfb-equivariant-coherent-proper-pushforward: the latter constructs proper pushforward and says a closed immersion gives ordinary extension by zero; it gives neither surjectivity of open restriction nor its kernel.
- lem-sfb-torus-nonfixed-complement-annihilation vs lem-sfb-torus-coherent-concentration: annihilation concerns classes on an open, possibly singular scheme, without any inclusion-isomorphism conclusion; the item's proof still needs localization and a separate injectivity argument.
- lem-sfb-torus-fixed-euler-unit vs lem-sfb-equivariant-regular-self-intersection: self-intersection assumes a regular immersion and proves the Tor identity; it does not prove regularity of a torus fixed immersion or invertibility of its Euler operator.
- lem-sfb-torus-fixed-euler-unit vs lem-sfb-torus-fixed-scheme-smooth: the latter assumes the ambient scheme is affine and asserts only smoothness of the fixed scheme. It supplies neither the required projective-case regular immersion nor the localized Euler automorphism.
- lem-sfb-torus-fixed-euler-unit vs lem-sfb-projective-torus-fixed-weight-schemes: that node assumes an equivariant embedding in a specified representation and describes its fixed affine charts. It does not provide an embedding for every smooth projective torus scheme or the conormal Euler automorphism.
- Each new node vs lem-sfb-torus-coherent-fixed-point-formula: that node computes the Euler character for isolated reduced fixed points and itself uses concentration; no new input computes any such formula.

These pairs were checked by reading the statements, not only titles. Whole-DAG statement searches for equivariant coherent localization, G_0, torus annihilation, fixed conormal weights and Euler classes found no generalization usable in one line. Blueprint searches for concentration, equivariant coherent localization and Euler classes likewise found no match. None of the three lemmas is a two-line consequence of an existing node, and none merely replaces the item by its whole conclusion.

## Review by Q12

I reread delivery-errors B through E in full and reviewed each statement with the cited statements open. The three new nodes introduce their group, field, scheme, actions, characters, fixed functor and groups; each repeats the common linearization/Grothendieck construction rather than pointing to unspecified ambient notation. Their proof lists and proof-dependency lists are empty, as required for unsplit nodes. Their source records honestly distinguish the locally read Milne page from the missing Thomason reference.

Step 1 uses precisely the statement that projective implies proper, then the definition of proper for separatedness and finite type, and the new localization statement for the kernel/image equality. The torus-character-to-representation-ring map is written explicitly: character tensors multiply. This verifies that the R-linearity is the item's twisting action, without needing an unproved identification R(T)=Z[X]. Fixedness makes W invariant and hence makes the complement invariant. The closed/open localization node has exactly these hypotheses and does not require W to be reduced or regular.

Step 2 uses the new annihilation statement with this separated finite-type Y and its represented fixed locus. For b/s it gets t annihilating j*b, lifts tb by the kernel/image equality, and writes the preimage a/(ts). The fractions therefore prove surjectivity directly; no exactness-of-tensor or flatness fact is hidden. This is not an application of the conclusion of a new concentration-isomorphism node.

Step 3 uses the fixed-Euler node with exactly the item's smooth projective hypotheses. Its statement supplies bounded regular-sequence lengths, the conormal and the automorphism of the localized G_0 module. I corrected my initial wording: a general G_0 group has no ordinary tensor-product ring structure on coherent modules. The final input asserts an exterior vector-bundle tensor operator, rather than calling an arbitrary coherent class a multiplicative unit. I also kept projectivity in this input instead of silently applying the existing affine fixed-smoothness node to a nonaffine Y.

Step 4 uses the existing equivariant regular self-intersection node, whose complete statement I read. The hypotheses it asks for are separated finite type, an equivariant closed immersion and locally regular ideals with bounded lengths; steps 1 and 3 establish exactly these. Its statement gives an R(G)-linear finite Tor map and the exact identity i! i*=lambda_-1(N^vee), both quoted in citations.json. Extending these R-linear maps to fractions preserves the equation. Applying the inverse Euler operator to i! i* beta=0 proves beta=0, which supplies injectivity separately from step 2.

Step 5 checks the definition-level edge cases: for r=0 the group scheme is trivial and the fixed immersion is the identity with Sigma={1}; empty coherent categories have zero Grothendieck group. There is no dense cyclic torus element assumption, so the algebraic closure of a finite field is allowed. All steps are shorter than 2000 characters; there is no long inline identification concealing another lemma.

I tested the new statements on W=Y and W=empty, U=empty, Y=empty, r=0, and a point with trivial action. For nonfixed-locus annihilation, the translation action of G_m on itself has a semi-invariant unit, so 1-e annihilates every class; an action through t^n requires 1-e^n and is still covered, including n divisible by the characteristic and a nonreduced mu_p stabilizer. For the Euler operator, A^1 with its standard action has conormal weight plus or minus the standard character depending on pullback convention, and both factors are inverted; P^1 has two such fixed points. A trivial action on any smooth projective scheme has conormal rank zero and identity operator. Nonisolated fixed components cannot be handled by replacing the Euler operator with its fibre rank; this is why the geometric Euler-operator input remains a real lemma. Its future proof must combine the weight decomposition with the rank-zero/nilpotence argument for vector-bundle classes on the smooth projective fixed scheme. No coefficient reduction modulo char F occurs.

I ran the msearch wrapper for all created statements, inspected its hits, and tried a second mathematical phrasing before recording absence. The searches actually run for this item are retained in searches.jsonl; the recorded query strings/tool names are taken from those records. The ordinary module-localization, abstract group-representation, Lie weight and exterior-power hits are not one-line specializations to algebraic torus equivariant coherent groups. The new-node searches use the delivered node ids conceptually but are logged under this item's delivery sandbox so the delivery gate can verify them. The earlier explorations and the imported item's searches were preserved. No fabricated search is recorded.

`proof_deps` equals the union of step uses. Every quoted excerpt in citations.json is verified as an exact substring of the delivered or live cited statement. I checked the argument uses that statement, not its proof. The new inputs have no proof dependencies and none refers to the item, avoiding circularity. The generic projective-implies-proper input is declared as an off-unit tool in split_report; it only verifies a geometric hypothesis.

## Remaining work

No unfinished part of this one-level split. The three new statement-only lemmas remain genuine stage-1 work. Thomason's missing reference remains explicitly WANTED; this delivery does not claim to have proved every supporting theorem down to Mathlib.

## Validation

Server review_split passed during preparation. The required full delivery dry run exited successfully: `OK (not pushed)`, commit `5ac3b66ca2a`, preflight passed. This report-only citation-count correction is followed by a fresh final dry run before pushing.
