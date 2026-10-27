# Stage-1 split: lem-sfb-tate-free-resolution

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-tate-free-resolution.json: statement; split following Stacks 09PN, with the prescribed polynomial augmentation retained exactly. No Mathlib match for the item.
- dag/nodes/sec-six-functors-basics/lem-sfb-adjoin-dga-cycle.json: statement; new unsplit differential extension lemma (09PM) on the existing variable-adjunction algebra. No Mathlib match.
- citations.json: one entry for every step/node citation, copying the cited statement verbatim.

One new node, zero new Mathlib leaves. Existing Mathlib leaves supply the Noetherian inputs. No Lean files were written and no compiler, Lake, or build command was run. All edits are in this sandbox.

## Attachments

None. I searched lean/WeilConjectures both for the exact blueprint tag and for Tate resolutions, divided powers and adjoining variables. The Tate-resolution references in KoszulIdealAlternatingProducts, KoszulConormalCycleRelations, SelfTorConormalComparison and SelfTorConormalComparisonExistence are contextual references or comparison statements; they do not state the existence of the augmented divided-power DGA with every clause of this item. Thus they do not justify ATTACH.

## WANTED

None. Every source needed here is present in literature/stacks-project/.

## Corrections and scope

The item statement is unchanged. I added def-weil-pbc-mv-polynomial-ring to its statement dependencies, since it introduces a finite-variable polynomial algebra. I replaced its empty proof by the finite Noetherian construction of 09PN. The initial kernel generators and later cycle generators may be empty.

There was no earlier sandbox split, report, citations file or searches.jsonl to reuse. I retained the item's existing Mathlib searches, source and provenance and added only searches actually executed for this work. New-node searches include leanfinder, loogle, grep and leansearch, followed by a second semantic phrasing and a second grep; their exact queries/results are in searches.jsonl and the new node. The hits concern ordinary divided powers on ideals, Kahler derivations, alternating complexes, or unrelated differential ideals/manifold differentials, and none states the new lemma. In particular Mathlib/RingTheory/DividedPowers/Basic.lean:78 defines ordinary DividedPowers, and DividedPowerAlgebra/Init.lean:251 only proves spanning in an ordinary algebra. These are not differential graded extensions. Item searches in two phrasings similarly find smooth/finite-type algebra facts, not a Tate resolution.

The helper blueprint_refs.py reports no imported blueprint ancestor for this item. I preserved the inherited null ancestor and its existing place/via chain, and gave the new node the additional item at the head of that chain. The current blueprint read was literature/blueprint/latest/, snapshot ef6f9619fdbffa59e88528fb56483d76c70258c8. Its chapter, unit and direct-image proof place this commutative-algebra input below direct-image branch (3), through the existing lci etale-invariance chain. The split changes neither that route nor any unit/chapter record. Whole-DAG searches for 09PN, 09PM, 09PH/09PI, differential extension and finite Noetherian inputs, and whole-blueprint searches for divided power, extend differential, Tate resolution and 09PM found no existing extension theorem. The finite-type Noetherian theorem and finite-submodule theorem were reused instead of creating duplicates.

## Source error

The copied Stacks dpa.tex Example 09PI incorrectly prints gamma_n(T^(i)) = T^(ni) for its divided-power symbols. For n=i=2 over Q, T^(2)=T^2/2, so gamma_2(T^(2))=T^4/8=3 T^(4), not T^(4)=T^4/24. The correct coefficient is (ni)!/(n!(i!)^n), exactly axiom (7) of 09PG and the project's def-sfb-divided-power-dga. The new extension lemma requires gamma_a(T)=T^[a] and inherits the correct composition axiom; it does not reproduce the erroneous displayed normalization in 09PI. This is a correction to the supporting source's formula, not a dispute of or a change to the item statement, which is valid as written.

## Not duplicates

lem-sfb-adjoin-dga-cycle vs def-sfb-divided-power-dga: the existing node defines the divided-power DGA notion and polynomial monomial conventions (including 09PG, 09PH and 09PI); it does not assert existence of an extended compatible differential after adjoining a variable with prescribed cycle as differential. The new node supplies precisely that 09PM differential existence/uniqueness statement for an arbitrary input DGA. Its algebra and module structure are taken from the existing variable-adjunction node. It neither resolves an algebra nor asserts any homology vanishing, so it also does not restate a clause of the item.

lem-sfb-adjoin-dga-cycle vs def-sfb-graded-divided-power-structure: this existing node states the graded divided-power axioms and explicitly has no differential; the new node extends a differential with prescribed value on a new variable.

lem-sfb-adjoin-dga-cycle vs def-sfb-nonnegative-strict-graded-algebra: this existing node defines the grading and strict commutation rules, without divided-power extension or differential; the new node is a differential extension theorem.

lem-sfb-adjoin-dga-cycle vs lem-sfb-divided-power-variable-adjunction: this existing node constructs the graded algebra and its divided powers, supplies the monomial module formulas, and treats sets/unions; it has no differential. I reused it as a statement dependency of the new node and as a proof citation in steps 2, 4, 5 and 6. The new node now states only the differential extension, its uniqueness and formulas.

The first dry run detected these three concurrently landed nodes while checking source tags. I opened all three and the revised def-sfb-divided-power-dga. I narrowed the new node to differential extension on the existing algebra, added the existing algebra-adjunction lemma wherever its monomial/union assertions are used, and regenerated the definition citations from the updated live statement. This supersedes the initial draft's bundled graded-algebra construction. No existing node is edited.

## Review by Q02

I read the local Stacks dpa.tex statement and full proof of 09PN, the full single-variable constructions 09PH and 09PI, 09PM, and the defining axioms 09PG and 09PJ. I compared the item with 09PN clause by clause: the supplied finite polynomial surjection provides finite type; the construction starts at that exact P and retains that exact pi; the resulting algebra has finitely many new variables per positive degree. I also read the entire statements of the concurrently landed def-sfb-nonnegative-strict-graded-algebra, def-sfb-graded-divided-power-structure and lem-sfb-divided-power-variable-adjunction, including its corrected factorial coefficient and union clause. I also read algebra.tex 00FN (Noetherian permanence) and 00IK (finite submodules), along with each of the existing definition/statement nodes used below. I did not rely on SGA.

Step 1 cites lem-weil-pbc-finite-type-algebra-noetherian for exactly its stated finite-type permanence assertion. It applies to P because P is the quotient of itself by zero and R is the given Noetherian ring. The cited definition def-weil-pbc-noetherian-ring actually says every ideal is finitely generated, so it supplies the finite list for ker(pi), including the zero ideal. The cited def-sfb-divided-power-dga gives the axioms, all vacuous in positive degrees for A(0)=P. I did not cite the Z-only polynomial Noetherian node for a general coefficient ring.

Step 2 uses the new single-variable lemma with degree one and f_j in degree zero, where d(f_j)=0. The cited existing algebra-adjunction lemma's module formula gives A(1)_1 as the direct sum of P u_j and its differential formula gives image exactly ker(pi). Thus the map with degree-zero component pi is a chain map and induces the required H_0 isomorphism. The same existing lemma gives the exterior-monomial finite P-bases explicitly. No regular-sequence hypothesis is used and no positive acyclicity is claimed at this stage.

Step 3 states the complete induction invariant before using it. It derives finite freeness in each degree by counting weighted monomials, with each positive exponent bounded by the fixed total degree. It then cites lem-weil-pbc-noetherian-submodule-finite, whose statement really gives finiteness of every submodule of a finite module over a Noetherian ring, for the cycle submodule of A(m)_m over P. I choose generators of that cycle submodule; their images generate its homology quotient by the elementary image-of-generators argument. This is a harmless choice of representatives in the source construction and avoids assuming any uncited theorem about finite homology or the H_0-action.

Step 4 checks the hypotheses of the new node again with degree m+1 and d(z_j)=0. Adjoining variables successively preserves the original cycles. Because m>=1 the new differential values have positive degree, so the augmentation extends. The separately cited existing algebra-adjunction lemma, not the new differential-only node, says that the old terms up to degree m remain identical and the only added summands in degree m+1 are P v_j. The displayed boundary sum therefore equals the old full cycle module. This proves H_m=0 while preserving all lower homology, including H_0. It is the actual induction step, not an application of a newly named resolution theorem.

Step 5 cites clause (4) of the existing algebra-adjunction node for the graded divided-power union, and uses the preservation of differentials asserted by the new node and the axioms in def-sfb-divided-power-dga, to form the ordinary union with operations evaluated in a common finite stage. These are literal monomial inclusions, so there is no injectivity or filtered-colimit exactness theorem being silently assumed. Every axiom is checked in a common stage. The homology calculation uses the three consecutive stationary chain terms at stage i+1, not a bare assertion that homology commutes with colimits. Thus it follows immediately from the induction already proved.

Step 6 uses the actual direct-sum module formulas of the existing algebra-adjunction node and the coefficient/multimonomial definition in def-weil-pbc-mv-polynomial-ring. It writes the R-basis as the ordinary degree-zero monomials times the positive-degree divided-power/exterior monomials, with both spanning and independence checked. Freeness is over R and need not be finite rank over R, whereas the positive-degree monomial basis over P is finite. The exact augmented resolution then follows from the already established homology and kernel statements.

For small cases I checked n=0, the empty relation list (S=P, with A=P sufficient), S=0 (the kernel contains 1 and d(u)=1 makes the augmentation acyclic), and R=0. The new extension lemma also includes z=0, e=1 and e=2, arbitrary characteristics and zero base rings. For e=1 its formula is the usual exterior/Koszul extension. For even e, z is odd and has z^2=0 by strict graded commutativity, so the displayed differential squares to zero without requiring 2 invertible; for odd e the derivative of T^2 is zT-Tz=0 since z has even degree. The factorial composition check over Q detected and corrected the 09PI typo described above. No nonzero-ring, field, characteristic-zero, injective-augmentation or regularity hypothesis was added.

Against delivery-errors B--E: the new node is a self-contained statement only, with no proof or proof dependencies, its own hypotheses, definition dependency, source tags/labels and executed searches. It states a genuine one-variable input, not the item or a clause of the item. Every non-elementary construction is cited; the elementary union, weighted-monomial and coefficient arguments are written out. Every proof citation has a verbatim quote from the exact node statement in citations.json. The related definitions and algebra-adjunction statement are distinguished above; the two Noetherian statements are reused. No step is over 2000 characters. The graph edges introduce no return dependency on the item: the new node depends only on the existing divided-power DGA definition and the existing graded algebra-adjunction lemma, neither of which depends on the item or on differential extension.

## Unfinished work

Nothing remains in this stage-1 item after successful dry run and delivery. The new single-variable extension node is intentionally unsplit and queued for its own future stage-1 item; its source 09PM omits the direct computation, which that later split must supply. No claim of a Lean proof is made.
