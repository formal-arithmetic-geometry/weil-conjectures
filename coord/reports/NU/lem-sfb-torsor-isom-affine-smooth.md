# Stage-1 delivery: lem-sfb-torsor-isom-affine-smooth

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torsor-isom-affine-smooth.json — statement, split with six proof steps; no exact Mathlib match.
- citations.json — one verbatim statement quotation for each of the 19 step/node citation pairs.
- searches.jsonl — five actual searches for this item, with their returned results inspected.
- report.md — this report.

No new DAG nodes or Mathlib leaves.

## Attachments

None. Searched WeilConjectures for the blueprint tag, torsor/Isom combinations, and equivariant isomorphisms. Read the candidate EtaleTorsor, EtaleTorsorDescent and Sites/EtaleIsoTorsor interfaces. They concern finite constant etale torsors or the G_m sheaf of trivializations of an invertible module; they do not state representability of this scheme Isom functor for arbitrary affine smooth group schemes over arbitrary bases. There is no attachment claim.

## WANTED

No missing source is needed for this proof. The item's inherited source mentions Alper–Halpern-Leistner–Heinloth, Section 2 Claim 3, printed p.3, as WANTED locally; the construction here uses the available Stacks sources instead.

## Audit and changes

The original item was unsplit and contained no argument. The statement is unchanged. Its arbitrary base B matters: lem-sfb-smooth-affine-group-torsor-representability assumes a field underneath its base, so it cannot simply be applied here. Also Isom(P,Q) is generally a torsor under an inner form of H, not canonically under H itself; no such global H-action is assumed in the proof. Two-sided transition maps give affine descent directly.

The mathematical construction is explicit. On W=P×_Y Q, use its tautological sections p,q. The torsor square gives trivializations by h↦ph and h↦qh. A right-equivariant map has coefficient c with ph↦qch. If p_2=p_1a and q_2=q_1b, its coefficient changes by c_2=b^{-1}c_1a. Multiplication order is essential. The triple-overlap cocycle follows from a_13=a_12a_23 and b_13=b_12b_23. Affine descent constructs I; fully faithful morphism descent identifies its points with precisely the equivariant isomorphisms in the item. Smoothness descends first along Q_P→P, then P→Y, checking quasi-compactness on these individual arrows.

Searched the whole DAG by source tags 049C, 0245 and 02VL and by affine descent, morphism descent, smooth base change, and torsor isomorphisms; inspected the resulting statements. Ran blueprint_refs ancestor and searches for torsor/isom and 0245. The ancestor command returns None, as in the inherited blueprint.from.node; its existing long place and via are retained, with same_as=[] after the search. Read the latest blueprint unit and direct-images proof (3), snapshot main-20261024. This is the recorded auxiliary affine Isom input below the unit, with no change to the unit or chapter route.

Mathlib: ran LeanFinder for the full equivariant Isom statement, Loogle for "Torsor", "Scheme", grep for Isom/torsor combinations in AlgebraicGeometry, LeanSearch for affine smooth Isom representability, and a second LeanFinder phrasing using principal homogeneous spaces and faithfully flat descent. Loogle and grep returned no hits. Semantic hits are affine-space parametrizations, flat affine morphisms, and elementary affineness/smoothness declarations; none constructs this Isom scheme. Retained the item's original searches and appended the five new searches with their actual result records. No unavailable service was reported as an absence.

## Not duplicates

No new nodes were created. Reused lem-galois-fpqc-affine-descent-effective (0245), lem-galois-fpqc-morphisms-descend (02W0), lem-weil-pbc-fpqc-descend-affine (02L5), the smooth base-change clause of lem-pc-proper-base-change, and lem-trf-smooth-fpqc-base-descent (02VL). The field-based smooth-affine-torsor representability node is not an arbitrary-base Isom representability result and is not used as a substitute.

## Review by NU

I read Stacks groupoids.tex remark-fun-with-torsors (049C), including its explicit reference to affine descent; descent.tex lemma-affine (0245), lemma-refine-coverings-fully-faithful (02W0), lemma-descending-property-affine (02L5), and lemma-descending-property-smooth (02VL); morphisms.tex lemma-base-change-affine (01SD) and lemma-base-change-smooth (01VB); and topologies.tex the fppf covering definition and covering lemmas 022C and 022D. The Isom-specific coefficient calculation is agent-written from these sources and is honestly marked proof_origin.by=agent. There are no new-node source claims to check.

Step 1 uses the represented-right-torsor definition only for its flat, surjective, finitely presented structure maps. def-pc-fppf-site says these singleton families are fppf covers; lem-trf-fppf-covering-is-fpqc gives the same fpqc covers; lem-weil-pbc-fpqc-covering-axioms supplies their base changes and their composition. This avoids assuming that a jointly surjective family is automatically a singleton cover.

Step 2 is elementary from the torsor square and the group diagrams in def-sc-group-scheme. Pulling back the inverse torsor isomorphism gives a scheme morphism extracting h, not just uniqueness on geometric points. Evaluating an equivariant map at p yields c and the displayed c^{-1} formula gives its inverse. This does not require commutativity or a global section on Y.

Step 3 checks the full noncommutative coefficient formula and cocycle before using descent. The same two definition nodes justify extracting a,b as sections. lem-weil-pbc-affine-morphism-permanence states arbitrary base change of affineness, so H_W→W is affine. lem-galois-fpqc-affine-descent-effective states effectivity for exactly a singleton fpqc cover and an affine morphism with a cocycle; the cover was proved in step 1. Its conclusion gives I and its compatible pullback isomorphism, but does not claim I→Y is affine, so that conclusion is proved separately in step 5.

Step 4 uses the actual bijection of morphisms onto compatible local morphisms in lem-galois-fpqc-morphisms-descend. Applied over T, it descends sections of I_T and maps between P_T and Q_T. Applying its injectivity to composites descends the inverse identities, and applying it to maps out of P_T×_T H_T descends equivariance. The fpqc-covering axioms provide the test-scheme cover. The same local formulas under T'→T and uniqueness prove naturality; this is not a bare assertion that an isomorphism sheaf exists.

Step 5 uses exactly the affine base-change and affine-source clauses of lem-weil-pbc-affine-morphism-permanence, and the arbitrary covering-family descent conclusion of lem-weil-pbc-fpqc-descend-affine, specialized to the constructed singleton cover. It is not extracting affineness from the effectivity node's proof.

Step 6 uses only clause (2) of lem-pc-proper-base-change, whose statement explicitly says arbitrary base change preserves smoothness. It imposes no properness hypothesis on that clause. lem-pc-quasi-compact-base-change supplies quasi-compactness of Q_P→P. Flatness and surjectivity of this arrow follow from it being a singleton fpqc cover (step 1 and def-weil-pbc-fpqc-covering). The torsor definition gives flatness, surjectivity and quasi-compactness of P→Y and of Q→Y. These are exactly the three covering-map hypotheses of lem-trf-smooth-fpqc-base-descent, used twice. No universal quasi-compactness or finite-type assumption on the base B or Y is inserted.

For C4, opened every cited node and copied its statement verbatim into citations.json; the uses above are clauses actually stated there. For C1, the non-elementary inputs are covering calculus, affine base change, effective affine descent, fully faithful morphism descent, affine descent, smooth base change, quasi-compact base change and smooth descent, each explicitly cited. Remaining operations are the fibre-product universal property and the written group calculations. No step exceeds 2000 characters; the local coefficient calculation is one elementary argument, not an unextracted standard lemma.

Checked delivery-errors B–E: no new-node formatting or searches are invented; statement and hypotheses are preserved; no duplicate or clause-restatement nodes are introduced; proof dependencies are exactly the union of step citations; no source proof is being cited as a stronger statement; no assertion about general representability is substituted for an argument. The four off-unit non-leaf citations are declared in split_report.tool_uses with their generic scheme-descent purpose. They do not replace a six-functor route step.

Small cases: if Y is empty then P,Q,W and I are empty and all formulas/descent assertions remain valid. For H=1 the local parameter scheme is W and I is Y. For P=Q the identity coefficient transforms compatibly, while a chosen local trivialization need not glue globally. For a noncommutative constant S_3 group, the displayed cocycle has the required multiplication order; replacing b^{-1}ca by a conjugation or a one-sided translation would fail. Nontrivial torsors with no Y-points still give the cover W and require no choice of global section. Nonreduced and non-affine bases cause no change because all descent inputs and base changes are arbitrary. A smooth affine H need not have been assumed finitely presented in the statement: the only finite-presentation hypotheses used to check the covers are those on P→Y and Q→Y already in the torsor definition.

## Unfinished work

None in the stage-1 split. No Lean files were written and no compiler, Lake or build command was run. The required dry run exited successfully: OK (not pushed) at 65427c801be, with server preflight passed. Direct push follows the final dry run.
