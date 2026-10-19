## Files written

- `dag/nodes/sec-smooth-purity/lem-amb-linear-trace-invariance.json`: statement, split into seven proof steps; Mathlib searches give no matching etale compact-support trace theorem. Zero new nodes and zero new Mathlib leaves.
- `citations.json`: 24 step/node citations with verbatim excerpts of the statements read.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag, linearTrace/linear_trace/traceInvariance/trace_invariance, affineSpace combined with trace/integration, and linear trace invariance. No declaration gives this assertion. `dag/lean_names_upstream.json` has no declaration for the item. Upstream master sorry declarations are not treated as finished proofs.

## WANTED

None. The item's master blueprint, its unit and chapter records, and the supporting Stacks sources used here are present.

## Statement corrected

STATEMENT-DISPUTED: the imported formula leaves the coefficient ring and base assumptions implicit, while its statement dependency `def-coefficient-twists-detailed` constructs objects on the **pro-etale** site. This is not a well-typed specification of the ordinary-etale map used here: the imported object `A_T(1)` lives in `D(T_proet,A)`, whereas `def-amb-etale-compact-support` has domain `D(T_et,A)`. No identification of these categories is supplied by that definition. Moreover, the named trace is the finite-coefficient, Noetherian-base counit, not an unspecified trace for arbitrary coefficients or arbitrary schemes.

I read the preceding master blueprint `lem-amb-affine-space-top-trace.md` and its current node. Its statement specifies a finite commutative ring A annihilated by an invertible integer N, a Noetherian base, the ordinary finite etale Tate sheaves, and the coordinate-tower counit. The correction spells out exactly that inherited context, allows d=0, replaces the inappropriate pro-etale twist dependency by `lem-asd-etale-finite-twist-pullback`, and defines the pullback action and the equation saying the trace is preserved. It changes neither the trace normalization nor the class of linear changes intended in the source. It makes no adic/rational coefficient assertion.

## Problems repaired

The imported first step cites `def-amb-etale-compact-support` for automorphism functoriality, but that definition only constructs a candidate from a compactification. The new step 2 instead cites the actual exchange theorem with its naturality/pasting clauses, and supplies the relevant compactifications and coefficient identifications. The imported second step invokes an isomorphism-detection result to conclude equality of scalars; that cited statement does not give equality of maps. Steps 3--6 instead use the actual degree-zero Hom bijection and section/function bijection, so equality follows directly. No new stalk-faithfulness lemma is needed.

The group-scheme and domain observations are written out in the proof, rather than introduced as new nodes restating elementary facts. Ordinary residue-field fibres suffice for the connectedness argument; this is the same universal-GL proof as the source and also proves its geometric-fibre assertion. This lemma is a detailed input to unit sk-prop-an Step 7; the unit's statement and route are not changed, and the item is not the unit's key node.

## Searches and reuse

Ran all recorded Mathlib searches through `/home/ubuntu/weil-launcher-nt/msearch.py`; the sandbox `searches.jsonl` is the log. Two semantic phrasings were tried. LeanFinder returned etale-algebra and affine-space-coordinate lemmas on the first query and unrelated Galois/group-cohomology results on the second. LeanSearch returned affine equivalences of torsors, not scheme-cohomology trace invariance. Loogle's quoted trace/etale query and both source greps returned no hits. No unavailable service was called a successful negative search.

Searched the full DAG by the item's name, the trace/linear-coordinate notions, locally constant sections, degree-zero full faithfulness, and compact-support exchange; searched the blueprint with `tools/blueprint_refs.py search` for `linear changes`, `constant sheaf sections connected`, `derived single`, and `compact-support exchange`, and checked the blueprint ancestor. The only blueprint node stating linear-coordinate trace invariance is the item itself. Existing generic nodes supply the needed infrastructure; specifically, the pro-etale rank-one-aut/rigidity nodes were read and deliberately not used for an ordinary-etale assertion.

## Not duplicates

No new nodes.

## Review by NO

I read the item in the master blueprint, both paragraphs of its proof, and the complete sk-prop-an unit and smooth-purity chapter records. The universal invertible-matrix argument is retained, as is the affine-space counit from the preceding trace node. I also read Stacks Tag 03P5 (`etale-cohomology.tex`, `remark-constant-locally-constant-maps`), which explicitly identifies sections with Zariski locally constant maps; Tag 06XS (`derived.tex`, `lemma-negative-exts`, part 2), which gives degree-zero Hom; and Tag 01T6 (`morphisms.tex`, `lemma-finite-type-noetherian`), including its Noetherian-base conclusion. I opened each cited node's **statement**, not merely its title or proof, and made a verbatim citation entry for each use.

Step 1 uses the affine-space definition for polynomial charts, the spectrum definition for their ring maps, and the scheme definition for the open subscheme. The finite-type definition applies because the displayed localization algebra has the finite generators x_ij and z, and the finite-type-over-Noetherian statement then gives precisely the Noetherian hypothesis needed for the trace on G. The adjugate formula gives an actual inverse, so no assumption about GL being generated by elementary matrices is used.

Step 2 reads the standard-open statement for A^d in P^d and the properness statement for the projective projection. The principal-open descriptions on the finitely many projective charts verify quasi-compactness, and finite-type inheritance verifies that the affine and projective spaces are Noetherian. The fibre-product statement justifies the model with top arrow a and the transported compactification j composed with a. Polynomial generators and the equations t_i-u_i verify the separated finite-type hypothesis of `thm-cbc-finite-torsion`. The input is a sheaf shifted by 2d, so it is bounded below. The exchange theorem really states naturality, independence of compactification, identities and both pasting laws. These give the displayed action equation, with the coefficient-map compatibility supplied by the Tate pullback statement. Thus the action is a specified canonical map, and its inverse and specialization to the identity matrix are checked. A mere definition node is not being used as the theorem.

Step 3 reads `lem-amb-affine-space-top-trace` for both isomorphy of this particular counit and its actual base-change equation, and the degree-zero fully-faithful statement for the Hom bijection in the abelian category of A-module sheaves. It does not assume arbitrary derived maps are detected by cohomology. Module linearity explicitly proves multiplication by the section alpha_0(1). The section/function node supplies exactly the Zariski-local-constancy assertion, and the constant-ring local-representatives statement makes pullback of the scalar identification explicit. This avoids importing the pro-etale lisse-rank-one statement, which has different hypotheses and site.

Step 4 is an elementary algebra/topology calculation, written in full: leading monomials show the polynomial ring is a domain, evaluating the determinant at the identity shows it is nonzero, and the fraction equation proves its localization is a nonzero domain. The zero prime then lies in every nonempty basic open, proving connectedness. The cited spectrum definition supplies the prime-ideal Zariski space; the Noetherian inheritance statement checks that the residue-field fibres are legitimate Noetherian bases in the next step. No GL connectedness theorem or algebraic-closure theorem is concealed in a new node.

Step 5 uses the already established action and trace pullback equations to evaluate the scalar at e_s as 1; the cited connected-locally-constant-map statement then applies to the nonempty connected fibre from step 4. The coefficient ring need not be a field, and the fibre field need not be algebraically closed. Step 6 uses the section/function bijection to infer equality of sections, and the faithful degree-zero functor to infer equality of derived endomorphisms. The cited fibre-product statement gives the lift of x into the residue-field fibre from its residue-field map, so the passage from fibrewise values to global values is justified; no isomorphism-conservativity statement is being used for equality. Step 7 substitutes the two actual pullback equations along s_g and cancels the exchange isomorphism, giving the equality for the exact normalized trace.

I checked B--E against these statements: no statement-only children or duplicated nodes were introduced; no clause was moved to a new node; all non-elementary facts are existing cited statements; all notation is ordinary-etale and the Tate coefficient comparison is explicit. Tested d=0 (empty determinant 1 and identity action), d=1 (nonzero scalar on the line), the empty base (unique function), a disconnected/nonreduced base (argument uses connected fibres, not connectedness/reducedness of S), the zero coefficient ring (unique endomorphism of the zero module), and arbitrary characteristic prime to N. The determinant-domain argument is only applied over residue fields, never over a nonreduced base ring. No smallness or constructibility hypothesis is silently needed: the compact-support theorem is used on its stated bounded-below finite-ring inputs.

## Unfinished work

None at this stage. No Lean files, compiler, Lake command, live repository write, direct git command, or other agent was used. The required delivery dry run is the only packaging operation; this sandbox is for the independent second reader and is not pushed by this worker.

## Second reading by NO

Independent second reader, 2026-10-16. Read delivery-errors B--E, GOAL.md and coord/dag-sync.md before reviewing. Verdict: PASS; the existing mathematical split needs no repair.

- Statement: compared every hypothesis, the specified trace and the action with the master blueprint item and the current lem-amb-affine-space-top-trace statement; the finite ordinary-etale/Noetherian clarification is justified by that trace's domain. Confirmed the reported pro-etale versus ordinary-etale type discrepancy against def-coefficient-twists-detailed and def-amb-etale-compact-support. PASS; retain the explicit STATEMENT-DISPUTED explanation and corrected statement.
- Step 1: checked all five cited statements, especially polynomial affine charts and finite-type-over-Noetherian (Stacks 01T6, morphisms.tex, lemma-finite-type-noetherian). The localization presentation and adjugate inverse supply the universal matrix and every section without assuming generation by elementary matrices. PASS.
- Step 2: checked the affine/projective chart and properness statements, def-pc-fibre-product, the complete thm-cbc-finite-torsion statement, and the coefficient identifications in lem-asd-etale-finite-twist-pullback. The model (a,p_d) is an isomorphism onto the pullback, j composed with a is the resulting compactification, the inputs are bounded below, and both pastings have the same top map. This gives the actual action equation, including identities. PASS.
- Step 3: checked the trace's exact base-change equation, degree-zero Hom bijectivity (Stacks 06XS, derived.tex, lemma-negative-exts (2)), and both constant-sheaf statements (Stacks 03P5, etale-cohomology.tex, remark-constant-locally-constant-maps; 00WK, sites.tex, lemma-sections-sheafification; 00YR, section-sheaves-algebraic-structures, beta/gamma). Module linearity gives multiplication by alpha_0(1); local constant representatives justify the ring/additive identification and its pullback. PASS; no claim of faithfulness on arbitrary derived objects is used.
- Step 4: checked against def-weil-affine-spectrum and 01T6. The elementary leading-term, nonzero-determinant, localization and zero-prime calculations establish connectedness only over fields, where each hypothesis is available. PASS, including d=0 with determinant 1 and one-point spectrum.
- Step 5: checked the connected-locally-constant-map statement against the nonempty connected residue-field fibre of step 4. Substitution of the two pullback equations of steps 2--3 at the identity gives the scalar 1, hence its constant value on that fibre. PASS; the coefficient ring need not be a field.
- Step 6: checked both bijections against their cited statements and the lift of Spec(kappa(x)) against def-pc-fibre-product. Every x lies under such a fibre point; composition of the scalar functions proves b=1, and the degree-zero Hom injection proves equality of derived maps. PASS; the empty scheme gives the unique section/function and causes no exception.
- Step 7: checked the exact trace equation in lem-amb-affine-space-top-trace and the action equation already proved in step 2. Pullback along s_g and cancellation of C_s_g give the claimed equality for the specified counit. PASS.
- New nodes: none; B1--B7 and child-node pruning require no changes. No Mathlib leaves were added. The full-blueprint search for linear changes returns only this item; the route still realizes sk-prop-an Step 7, and the chapter is untouched.

Small cases checked independently: d=0, d=1 over a field, an empty base, a disconnected base, a nonreduced Noetherian base, and the zero coefficient ring. In particular, the proof does not assert that a polynomial ring over a nonreduced base is a domain: that calculation is restricted to residue fields. All 24 citation excerpts were compared programmatically with the current cited statements, and each complete statement was read; the union of the step citations equals proof_deps.

Changes made and why:

- Added this independent per-step review; retained the first worker's sections, including Review by NO, and all seven mathematical steps.
- Ran a fresh LeanFinder query using automorphism/identity vocabulary and a broader trace/compact/etale source grep through msearch.py. LeanFinder's eight hits concern cotangent maps, affine-space coordinates and Hilbert 90; none states this trace theorem. The grep returned zero hits. Appended the actual records to mathlib_searches; searches.jsonl contains their original outputs.
- Rechecked the read-only slopmaster2 by the item id and broader affine/trace and linear/invariance patterns: only unrelated Lie-invariance and finite-etale curve trace-duality hits, no declaration matching this item. No upstream sorry declaration is treated as a proof.
- No mathematical, statement, dependency or citation change was necessary; citations.json remains correct for every retained use. No live-project or launcher edits, Lean edits, compilers, build tools, direct git commands or agents were used.
