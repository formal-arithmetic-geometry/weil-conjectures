## Worker report

Group NA; item lem-route-transition-comm-shift-exists-unique; stage 1; 2026-10-27.

### Files written

- dag/nodes/sec-smooth-purity/lem-route-transition-comm-shift-exists-unique.json: rewrote the provisional Lean/docstring placeholder as a quantified proposition and supplied five proof steps. Not a Mathlib leaf: Mathlib has general shift-localization machinery, but not this fixed intrinsic scalar transition, its integral-image normalization, and uniqueness.
- citations.json: one verbatim statement quotation for each of the twelve step/node citations.
- report.md: this report and signed self-review.
- searches.jsonl: original records written by the prescribed search command, retained unmodified.

New nodes: none. New Mathlib leaves: none. There is no new statement-only node, duplicated elementary lemma, or replacement of the item by its own clause.

### Attachments

None. The exact route declaration WeilConjectures.SfAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique in lean/Sheaf/Paper/SfAlgebraicallyClosedCoefficients.lean:157 has a sorry proof at line 176. Searches in lean/WeilConjectures by its name, the blueprint tag, transition/shift terminology and localization/commShift terminology found no declaration proving every clause. StageSystem/Shift.lean assumes transition CommShift data; it does not construct this normalized data. ScalarExtensionExactIntrinsic supplies some exact rational shift, which does not assert the requested normalization or uniqueness. The proved generic semilinear-localization interface is already owned by lem-pur-semilinear-scalar-localization and is reused, not attached to this item.

### WANTED

None. The argument is explicitly agent-written, using existing DAG statements and the live route docstring, not attributed to a nonexistent Stacks theorem about this named functor.

### What needed repair

The imported item was a machine-made placeholder containing a truncated Lean signature and its docstring, with no statement dependencies or proof. I replaced it with the same quantified assertion: finite-field datum D; prime ell different from D.p; arbitrary-universe algebraic closure Omega; finite E <= L; arbitrary scheme Y; the actual intrinsic integral and raw rational categories; the prescribed integral normalization; uniqueness of the whole CommShift structure subject to its degree-one HEq. No extra geometric hypotheses, exactness hypothesis on the rational functor, new objects, or idempotent completion were introduced. The Lean record is preserved verbatim.

The current literature/blueprint/latest points to main-20261026 (a8806c1f60d0aec15c57e02339aea4bedc0e3759). It no longer contains the ancestor file def-weil-algebraically-closed-coefficients. I read the current sec-six-functors-basics/sk-def-purity-conv/def-sf-setting.md, especially Integral and rational coefficients point 2, and det-def-sf-operations.md. The current source defines native condensed coefficient categories and proves tensor-Hom comparison, whereas this retained SHEAF obligation concerns the intrinsic raw model. The proof records that distinction and does not silently identify the two models. This is an expansion of the provisional exact live signature, not a weakening or mathematical correction of it.

### Search and recovery evidence

The required archive-list command returned no directories for this item under any group. The active sandbox had no item, split, report, or previous searches; I copied the live item before editing. No repair note for this id was found. No failed construction was repeated.

The prescribed msearch command ran LeanFinder twice with distinct phrasings, Loogle, LeanSearch and Mathlib grep. All five returned successfully; their exact queries and returned names are in the node and searches.jsonl. I read Mathlib/CategoryTheory/Shift/CommShift.lean:47-185 (zero, addition, coherence), and Shift/Localization.lean:130-240 (commShiftOfLocalization and its component formula). These are general tools and do not assert the item in one specialization: one must identify the actual rational functor, check scalar-localization hypotheses, compute the normalized component, and prove uniqueness. No unavailable service was recorded as no match.

DAG concept searches included semilinear localization, rational shifts/localization, degree-one normalization, integer-shift uniqueness and the integral route name. Whole-blueprint searches with tools/blueprint_refs.py included shift, semilinear, shift comparison, commutes with shifts, and algebraically closed coefficient. The relevant hits were inspected through their statements: the original coefficient definition packages transitions, and general stage-system results assume coherent finite shifts. Neither proves the unique normalized transition of this item. The existing lem-pur-semilinear-scalar-localization states precisely the needed transformation extension and coherence preservation. Its reuse avoids creating a generic scalar-localization duplicate.

### Unfinished work

None in this stage-1 split. The actual Lean proof remains future stage-3 work; this delivery writes no Lean and invokes no compiler or Lake command. The normalized integral transition is a separate existing DAG obligation, not asserted proved here.

## Not duplicates

No new nodes. Existing semilinear extension, linearity, coefficient-localization, raw-category and integral-normalization nodes are cited directly.

## Review by NA

I read the current source passages named above, the full live route declaration and docstring, SfRationalizationKaroubi.lean:49-115 and 180-300, and the normalized integral transition declaration immediately preceding the item. The latter fixes all integral shift components by the ordinary-to-completed comparison. The item only fixes the rational comparison at one and asks for uniqueness of its coherent extension; my statement preserves this distinction. In particular K in the signature is a raw rational object with integral field K.obj, not a Karoubi summand or an arbitrary native condensed object. Every such K is literally Q_E(K.obj). The algebraic closure can have an independent universe, and the small coefficient models are only the recorded equivalent realizations of E and L. The scheme Y has no map to the finite field in the Lean signature, so I imposed none.

For step 1 I opened lem-weil-integral-scalar-extension-constructible: its last sentence explicitly gives the restricted O_E-linear functor between the two intrinsic categories. I opened lem-weil-integral-constructible-linear: it gives linear shifts on precisely those categories. I opened lem-weil-l-adic-integers-localization-uniformizer: it identifies O_F[1/varpi_F] with F. Thus the coefficient ring map, additive semilinearity, and unit-image hypothesis of lem-pur-semilinear-scalar-localization are satisfied; a source uniformizer need not be a target uniformizer. The short verification that a field inclusion carries a unit to a unit is elementary.

For step 2 I read the last paragraph of def-weil-rationalization-karoubi, which specifies the object and pure-tensor morphism formulas for the actual rational transition. The first extension clause of lem-pur-semilinear-scalar-localization gives uniqueness with exactly that object map and scalar agreement. Consequently the functor used in the item is this extension. I am not inferring anything from its construction hidden in a proof. The specified object equalities account for the endpoint equality morphisms in the Lean HEq.

For step 3 I reopened the integral route node: its statement records the normalized coherent integral shift, not just exactness of some witness. The second paragraph of lem-pur-semilinear-scalar-localization explicitly states extension of natural transformations and natural isomorphisms, identity/vertical-composition/whiskering preservation, and preservation of shift equations. These are exactly the non-elementary ingredients used. I wrote the resulting comparison as F(q_E inverse); Q_L(t_n); q_L, so its source and target can be checked individually. It starts at F((Q_E K)[n]) and ends at (Q_L(TK))[n]. The naturality claim is for all rational arrows, as stated by the extension node. Inverting the localized inverse proves invertibility. Coherence uses the cited equation-preservation clause, rather than an unjustified assertion that integral arrow naturality alone is enough. The fixed triangulated localization node is cited for the induced shift and localization comparisons. No exactness of T with this particular normalized shift is used: only the transformation and equation extension clauses of the semilinear theorem are needed, not its final exact-functor clause.

For step 4 I checked def-weil-linear-scalar-localization's last sentence, which specifies the shift on objects/tensor arrows and Q[1]=[1]Q. I also read the attached theorem exists_triangulated_scalarLocalization in Sheaf/CategoryTheory/ScalarLocalizationTriangulated.lean:116-145 and the chosen witnesses in SfRationalizationKaroubi.lean:62-104: the degree-one shift functor is the tensor extension and the comparison for Q is HEq to the identity. This is the precise meaning of the cited induced shift here. Its two identity factors reduce the displayed step-3 formula to Q_L(t_1). The statement does not assume a strictly equal object map where the published functor only supplies a propositional equality; the endpoint transports are stated explicitly.

For step 5 the only categorical input is that [n] is an autoequivalence (the integer powers of the automorphism in def-weil-triangulated-category) and raw localization keeps every object (def-weil-linear-scalar-localization). The rest is the zero/addition equations defined inline in the item's own statement. At n=0 the comparisons are canonical. Positive induction uses (n,1). At negative degree -r, the (r,-r) equation isolates the unknown factor at X[r]; cancellation and naturality along Z isomorphic to (Z[-r])[r] give it at every Z. Thus inverse shifts are handled explicitly. Equality of all natural-isomorphism components and proof irrelevance give equality of the structures, not merely isomorphism of structures. This short recurrence argument is elementary; it does not need a new integer-shift-uniqueness lemma node.

I checked delivery-errors B through E against the files. B: no new nodes, all objects and hypotheses introduced, one TeX escape level, genuine recorded searches, blueprint place/same_as filled. C: all twelve step citations were checked against their statement texts and copied verbatim into citations.json; no definition is used as a theorem about an unrelated construction and no node's proof is mined for an unstated claim. All proof dependencies lie in the same ambient-typing unit or are its definitions; no off-route theorem is substituted. D: the argument is the actual assembly and uniqueness proof, not an application to newly invented clauses of itself. E: E=L, ramified E subset L, empty Y, the zero object, zero morphisms, and positive/zero/negative shifts require no extra hypotheses. Tensor localization never assumes Q is faithful or flatness reflects equations; it carries existing integral equations forward. In particular rationalization may kill torsion and the proof still works. No new mathematical statement needed counterexample repair.

Every step is below 2000 characters (the longest is the explicit uniqueness induction). The source's terse sentence about integer iteration was expanded rather than hidden in a long step. There were no new nodes to test individually, and no SGA source was used.
