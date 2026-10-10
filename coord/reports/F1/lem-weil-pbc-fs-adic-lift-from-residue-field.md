# Worker report: lem-weil-pbc-fs-adic-lift-from-residue-field

Date: 2026-10-10. Group: F1. Stage 1 only; no Lean edits, builds, git operations or server access.

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-fs-adic-lift-from-residue-field.json`: unchanged statement, six-step split of Stacks 07NR.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-complete-local-map-regular-presentation.json`: new unsplit statement, regular/parameter consequences of 07NN; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-local-quotient-kernel-parameters.json`: new unsplit statement, Algebra 00NR; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-formally-smooth-closed-fibre-adic.json`: new unsplit statement, 07NQ (2) => (3); no Mathlib match.
- This worker report. Lead review remains for the lead to write.

## Attachments

None. Item and new tools have no source-repository Lean declarations attached.

## WANTED

None: all mathematical sources are in the supplied Stacks checkout `/tmp/stacks-project`, corresponding to the listed Stacks literature. Read 07NR (`lemma-lift-fs`), 07NN (`lemma-embed-map-Noetherian-complete-local-rings`), 07NQ (`proposition-fs-flat-fibre-fs`), 07NM (`lemma-quotient-power-series-ring-over-Cohen`), and Algebra 00NR (`lemma-regular-quotient-regular`); verified tags from tags/tags. Reused existing statements for 00NQ, 07DY, 0325, 00DV, cotangent dimension, 07EL (2)=>(1), 07EG and tensor-quotient base change.

## Corrections and argument

The item was an unsplit statement. Its reviewed statement agrees with 07NR, including the compatibility of the final isomorphism with A_0. No statement or unit route change was needed. The unit is sk-thm-p1 and chapter sec-proper-base-change; both records were read and left unchanged.

The proof now constructs R -> S presenting A_0 -> E, takes the regular fibre S/m_R S, removes parameter generators of its kernel to E, and forms T. The source invokes 07NM to reidentify the quotient as a power series ring; for the only conclusions needed here, the already available 00NQ parameter quotient and 07DY flatness theorem suffice on exactly the same presentation/parameter route. This is a node-level simplification, not replacement of a unit step. Explicitly, the t-classes are independent in m_S/m_S^2; the chosen x-classes are independent modulo their span; extending their union to a basis and using Nakayama yields a parameter system of S. Permute x first and use 00NQ to get T regular with the t-images still parameters. Its closed fibre is E, so 07NQ applies. The final ring C = T/IT for I = ker(R -> A_0) is a complete Noetherian local quotient, equal to the tensor base change, and the proof checks locality, topology and A_0-linearity of the fibre isomorphism.

## B-E self-check

B: each new node introduces all objects, defines local map and regular system of parameters inline where used, cites definitions for Noetherian/completeness/regularity/flatness/formal smoothness/algebra structures as applicable, gives the source tag and exact TeX label, has no proof content, and records LeanSearch, LeanFinder and actual Mathlib source grep. TeX is encoded once. No Mathlib leaf is claimed. Search caveat: `/tmp/mathlib-f1` is current-head sparse source, not the pinned project checkout; service indexes can lag. No pin-level absence claim is made.

C: searched DAG by 07NN, 00NR, 07NQ, labels and regular-parameter/flat-fibre concepts before creation. The 00NR citation in `lem-weil-pbc-regular-local-hypersurface-criterion` occurs only in a proof: its statement concerns one hypersurface, not arbitrary regular quotients. The existing 07NQ node states (3)=>(1), not the needed converse. No existing node states the compatible presentation. All proof dependencies are the statements actually used; no step uses the internal construction of another node. The three new statements are generic tools strictly smaller than the item: a presentation with no formal-smooth lift, a kernel theorem with no base change, and a criterion that constructs no ring. No step simply renames the desired lifted C. The check finds zero cycles.

D: the cotangent/Nakayama argument and final quotient identification are written out. New nodes are not split recursively and carry only statements. The six item steps do the construction instead of delegating the conclusion to a new existence node.

E: checked locality of A_0 -> E because m_0 maps to zero; q is surjective local, hence gives residue-field isomorphism and q(m_R)=m_0; lifts x_i lie in ker(S -> E); every quotient ideal is proper; the sequence t in T is regular by 00NQ; 07NQ applies to flat local Noetherian R -> T; extended m_T in C equals m_C; C/m_0 C = T/m_R T with A_0 compatibility. Edge cases: d=0 (R a field, empty t), r=0 (kernel zero, T=S), r=dim(S/m_R S) (E a field), I=0 (A_0=R), A_0 already a field, and both residue characteristics. None needs nonempty parameter lists or characteristic assumptions. The regular-quotient node permits c=0 and c=d; the criterion assumes no completeness or finite-type hypothesis.

## Validation and unfinished work

`python3 tools/review_split.py lem-weil-pbc-fs-adic-lift-from-residue-field`: PASS, three new nodes.

`python3 tools/check_dag.py`: zero cycles and zero self-loops; exit 1 solely for seven existing unrelated unflagged unreachable nodes: constructible-finite-pushforward-approximation, constructible-finite-pushforward-noetherian, constructible-approximation, finite-cover-killing, finite-stage-killing, prime-torsion-devissage, pushout-monicity (with their normal lemma prefixes). No item/new-node error. These files were not changed.

The three new tools remain unsplit for later work, as required by one-level splitting. Mathematical lead review is pending.

## Review by F1

I read Stacks 07NR and its cited 07NN and 07NQ statements and proof, and Algebra 00NR. The item keeps 07NR's hypotheses and its conclusion as an isomorphism compatible with the original residue-field algebra structure. The new 07NN helper states a compatible regular presentation, 00NR supplies only the regular-quotient kernel generators, and 07NQ supplies only the flat plus formally smooth closed-fibre implication. Each is a stand-alone statement strictly smaller than the lifting conclusion, with its exact tag and label and three recorded Mathlib searches; none contains proof steps or claims a Mathlib match (B, D).

The cited regular-parameter quotient, cotangent dimension, Nakayama, flatness and completeness nodes expose the facts used in steps 2–4. The cotangent argument explains why the lifted fibre kernel generators can join the existing parameters; no power-series presentation is needed after this point. Step 5 applies 07NQ to the regular flat map with closed fibre E. Step 6 uses the tensor-quotient identification and the complete-local-quotient result; it verifies both that the extended maximal ideal is the maximal ideal of C and that the final fibre map respects A_0. These are the conditions required for the cited adic base-change statement (C, E).

I checked empty parameter lists, zero kernel, field residue ring, both residue characteristics and I=0. The presentation result handles the coefficient-ring case, and the quotient and fibre calculations remain valid. The item has a real six-step construction rather than a new node restating its existence conclusion. `review_split` passed and no new cycle or reachability issue was found; the seven pre-existing reachability warnings are unrelated (A, F).
