# Stage-1 delivery: lem-sp-restriction-transition-transpose

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-restriction-transition-transpose.json — statement, split into seven steps; no Mathlib match for the full geometrically normalized assertion.
- citations.json — exact statement excerpts for every step citation.
- searches.jsonl — actual searches run with msearch.py; the inherited item searches are retained in its JSON, and today's additional queries and results are appended.
- report.md — this report. write_split.py is a sandbox-only preparation script.

No new nodes and no Mathlib leaves. No unit record changed: this is a child, not the key statement of its unit.

## Attachments

None. Searches of WeilConjectures/ for the exact id, its blueprint docstring tag, restriction/transpose terminology and compact-support scalar terminology found no declaration stating the item. ProEtale/ScalarExtension.lean defines the underived scalar adjunction and its conjugate pullback comparison, not the claimed unbounded mixed-coefficient compact-support identity. TraceFormula/Adic.lean:137 has nonempty_rightDerivedLowerShriek_comp_iso, which only composes assumed operation comparisons; it does not identify the specified counit-normalized maps. LowerStarProjection.lean concerns geometric projection transposes, not this scalar mate. The master checkout is reference material only and was not used as proof evidence. The item has no inherited Lean audit requiring an unattached sorry frontier to be processed.

## WANTED

None. The split is explicitly agent-written using available Stacks results and the current blueprint's route.

## Corrections and observations

The statement is unchanged. Its statement dependencies now explicitly include the normalized scalar adjunction, the geometric derived operations, and extension by zero; the weaker derived-change-of-rings construction and the unused separate geometric ring-change citation were removed from stmt_deps. The latter remains a proof dependency where its adjunction-compatibility assertion is actually used.

The imported statement correctly insists on an ambient b_f at Res L. This matters: restriction along Z/ell^2 -> Z/ell can send a perfect B-object to an A-object with infinite Tor amplitude. The proof never applies Dctf preservation to such a restricted object and never claims restriction preserves K-injectives. All operations in Steps 1–5 are ordinary uncompleted unbounded derived operations; Dctf is used only to invoke the specified invertibility on K, and in Step 6 to keep its scalar extension in Dctf.

## Not duplicates

No new nodes. The entire DAG and imported blueprint were searched using tools/blueprint_refs.py search for restriction transpose, restriction scalars, scalar adjunction, and coefficient comparison; the item's ancestor is det-sp-tower-gluing. Existing lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-weil-pbc-ring-sheaf-change-adjunction, lem-sfb-ringed-derived-monoidal-comparisons and lem-cbc-proetale-extension-zero supply the generic facts needed. In particular no new node was made for either the proper or open clause of the item, for the elementary naturality expansion, or for generic mate calculus already present in Mathlib.

## Review by NI

I read the chapter record and sk-prop-sp-tower-geometric unit, then the current main-20261015 gluing statement and proof, especially its Levels paragraph. That paragraph requires the actual transition maps, so an arbitrary isomorphism of functors is insufficient. I also read the current det-sp-reduction-direct-image statement and proof: its Step 1 defines the proper comparison by the geometric counit and its open part by the canonical tensor comparison. For the underlying literature I read sites-cohomology.tex Tag 07A6 (lemma-adjoint), Tag 0D6D (lemma-derived-pullback-composition), Tag 0D6E (lemma-derived-pushforward-composition), and the compatibility lemma immediately following the base-change remarks; I read sites-modules.tex Tag 0E8I (lemma-j-shriek-and-tensor). These give the adjunction and canonical comparison route; the mixed-map algebra is mine, not a purported verbatim Stacks theorem. No SGA source is used.

Step 1 uses the actual statement of lem-pur-sheaf-ring-derived-coefficient-adjunction, including its normalized unit and transpose, to write v-sharp = epsilon T(v). The derived-change-of-rings functor alone would not supply that assertion. I checked def-weil-pbc-proetale-operations for the geometric adjunction and prop-weil-pbc-proetale-constant-ring-map for the coefficient identifications. The direction convention is explicit: D is the inverse of the comparison named d in lem-weil-pbc-ring-sheaf-change-adjunction. det-sp-reduction-direct-image specifies exactly the proper-counit normalization used to define gamma. All rings and schemes satisfy that node's finite ell-primary and separated finite-type-over-k hypotheses.

Step 2 uses lem-sfb-ringed-derived-monoidal-comparisons for more than mere existence of a compositor: I opened its statement and checked that it asserts adjunction compatibility and the exact composite-counit formula without flatness or boundedness. The two ringed-topos factorizations have the same source (Z,B) and target (Y,A), because pullback of constant coefficients preserves the specified coefficient map. Its comparison agrees with the canonical geometric restriction comparison stated in lem-weil-pbc-ring-sheaf-change-adjunction. The displayed equation explicitly inserts D-inverse before cancelling it with D; it compares counits rather than asserting unexplained transport. Geometric counit naturality makes the transpose of R_B(epsilon) gamma identical to the expanded composite counit. The last inference is injectivity of the geometric Hom bijection of def-weil-pbc-proetale-operations. This step uses neither a faithfulness claim for derived restriction nor a claim that restriction preserves K-injectives.

Step 3 uses lem-cbc-proetale-extension-zero for exactness, the open adjunction and compatibility with restriction of scalars, and det-sp-reduction-direct-image for the canonical open tensor map E. I read def-weil-extension-by-zero: its presheaf is the given sheaf on objects over X; coverings there remain over X. This proves the unit is identity and the open Hom test is injective. The restrictions of both maps are the same scalar counit, with normalization provided by lem-pur-sheaf-ring-derived-coefficient-adjunction. This checks the specific open normalization, not an unspecified tensor isomorphism and not conservativity of ordinary geometric stalks on pro-etale sheaves.

Step 4 uses exactly the factorization of d_f in the statement of lem-sf-compact-support-restriction-of-scalars and the proper/open normalization of b_f in det-sp-reduction-direct-image. The three-line expansion pastes the equations of Steps 2 and 3. I wrote the adjunct argument proving ambient naturality of gamma, so no naturality restricted only to Dctf is applied outside that subcategory. Step 5 then expands the scalar transpose and substitutes Step 4. It invokes the scalar adjunction's naturality and the natural open tensor map, and gives the original desired formula. The converse substitution t = identity at rL is explicitly made in the ambient category; it need not satisfy the narrower Dctf hypotheses.

Step 6 uses the composite-counit normalization of lem-sfb-ringed-derived-monoidal-comparisons, the actual associator and Dctf-preservation clauses of det-sp-scalar-extension-functor, the coefficient-composition clause of lem-sf-compact-support-restriction-of-scalars, and the full cocycle equation stated by det-sp-reduction-direct-image. I checked the order: the composite counit is epsilon^(B,C) after T^(B,C)(epsilon^(A,B)); b^(B,C) is evaluated at T_X^(A,B)K, not at K. This identifies both successive transposes and the actual b factors under the tensor associators. Step 7 uses the identity-adjunction normalization in the generic ringed-topos comparison statement and the explicit open presheaf, then the proved counit equation gives b = identity. Functoriality gives the identity result when t is identity too.

I checked delivery-errors B–E against the files: the statement is self-contained, the mathematical text uses single TeX escapes after JSON decoding, every non-elementary input is an opened existing node statement and has an exact excerpt in citations.json, no fact is imported from a cited proof alone, no new statement or duplicate or one-clause replacement is introduced, and no change leaves the unit's reduction/transition route. Off-unit generic tools are declared in split_report.tool_uses for review. I checked the small cases f = identity, j = identity, h = identity, empty X, zero complexes and the zero coefficient ring; the equations reduce to the corresponding adjunction equations or unique zero maps. For a nonflat quotient Z/ell^2 -> Z/ell the ambient argument remains typed, while Res B illustrates why the finite-Tor shortcut would fail. The proofs use no existence of geometric points to detect arbitrary pro-etale derived maps. Every step is below 2000 characters; the proper composite-counit computation and the open Hom test are written explicitly and rely on already existing generic comparison theorems.

## Unfinished work

None in the requested one-level split. Existing dependency nodes retain their own statuses and are not edited. Required server dry run and delivery are the final checks.
