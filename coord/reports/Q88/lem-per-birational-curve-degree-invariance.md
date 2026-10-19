# Q88: lem-per-birational-curve-degree-invariance

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-birational-curve-degree-invariance.json`: statement, now split into nine steps. Statement and statement dependencies unchanged. No Mathlib match.
- `citations.json`: 29 literal statement quotations for every node cited by every step.
- `searches.jsonl`: the required search command's unmodified log. Four fresh searches supplement the item's inherited Q104 searches.
- `report.md`: this report. No new nodes and no Mathlib leaves created.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 checkout by the blueprint tag, birational/degree, Euler-characteristic and pullback notions, then read `Cohomology/EulerChar.lean`, `Curve.lean`, and `Cohomology/LongExact.lean`. `AlgebraicGeometry.Scheme.Modules.degree_pullback` at EulerChar.lean:187 is field-extension base change, not a birational map of curves. The related Picard degree comparisons also require base-change squares. None states this item. The existing Euler-additivity node is used only for its short-exact-sequence clause, matching `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_add_of_shortExact` at LongExact.lean:161.

## WANTED

None. All literature used is already present.

## Problems found and changes

The imported item is true and matches the rank-one integral specialization of Stacks 0AYU, `lemma-degree-birational-pullback`. No statement dispute or change is needed. Its proof was empty. I retained its source, ancestry, creation record, statement dependencies and inherited search records. I supplied the proof using existing nodes and added fresh logged searches for this item. There was no substantive earlier sandbox attempt to recover: it had only dispatcher markers, and no delivery process was active.

The generic defect sequence simplifies in this integral case: the structure map is injective. Step 3 proves this on finite affine charts and proves that the cokernel has zero generic stalk. It does not assume that the originally chosen dense isomorphism open already has no extra inverse-image points. The rank-one projection formula and tensor exactness are proved on a trivializing cover rather than invoked without a node. These are elementary from the definitions and create no queue items.

Source pointer correction made while checking: the current Stacks tag index gives 01E8 for `cohomology-lemma-projection-formula` (01E6 is its section) and 0BEW for `varieties-definition-degree`. The inherited degree-definition node has an older/mismatched tag pointer, but its actual formula is precisely the one needed; I cite the checked current tag in this item's proof and do not edit another worker's node.

## Existing-node and blueprint searches

I searched the whole DAG by 0AYU, 0AYT, 0AB7, birational/degree, ordinary affine cohomology, coherent kernels and cokernels, finite pushforward, and the source labels. I read the matching node statements, not just their names. `tools/blueprint_refs.py search` for birational, degree and birational pullback found no blueprint node stating this item; the ancestor command gives `lem-per-artin-gabber-affine-curve`. I read the chapter and unit records and the current main-20261015 unit text. This is the existing exceptional-curve normalization degree comparison below the ancestor's Step 1, not a replacement for a unit-level argument. Unit/chapter files are untouched.

The substantive existing inputs reused are: proper-over-separated; proper birational integral-curve finiteness; finite-type Noetherianness; coherent iff quasi-coherent finite type; invertible pullback; finite coherent pushforward; coherent cokernels; affine generic fields; scheme-theoretic support; zero-dimensional-support Euler invariance; affine cohomology; proper coherent cohomology finiteness; Euler additivity. I checked that the finiteness and zero-support inputs do not depend back on this item. Off-unit generic tools are declared in `split_report.tool_uses`; the trace-formula chapter input is only a scheme-theoretic finiteness theorem, not any trace or Poincare result. No SGA source is used.

## Mathlib searches

All new records are the actual commands logged in `searches.jsonl`: LeanFinder for birational proper curves and cohomological degree; LeanSearch for normalization and invertible-sheaf degree (a second phrasing); Loogle for `"degree", "birational"`; grep for `birational.*(degree|deg)|degree.*birational|deg.*birational`. Both semantic services returned eight hits and were available. I read their returned types: they concern general scheme morphism properties, Weierstrass base change, polynomial normalization or scheme normalization, not this degree theorem. Loogle and grep returned zero hits. The fresh queries and returned names are recorded alongside the original searches, without claiming a service failure or an unrun query.

## Not duplicates

No new nodes. All available ingredients are cited in place.

## Review by Q88

I read Stacks `varieties.tex` at 0AYU (`lemma-degree-birational-pullback`) with its proof and checked the source hypotheses against the unchanged item: arbitrary field, proper integral curves, dimension one, dense-open birationality, invertible module of rank one, and degree over the same field. The more general vector-bundle and reducible assertions are not being asserted here. I also read 0AB7 (`lemma-finite-in-codim-1`) and 0AYT (`lemma-chi-tensor-finite`), `coherent.tex` at 01XZ, 01Y6 and 089W, `modules.tex` at 01BY, and `cohomology.tex` at 01E8. There are no new nodes whose source or small cases remain to check.

Step 1 uses the properness definition for separatedness/finite type, the finite-type Noetherian theorem over the Noetherian field, and the scheme-sobriety statement for generic points. Restriction of an isomorphism of dense opens really identifies their generic stalks. The proper-over-separated node states exactly the needed properness of f; the integral-curve finiteness node assumes precisely the integral, separated, finite-type, dimension-one, proper, dominant, function-field-isomorphism facts just established. I did not infer properness of an arbitrary map merely from both spaces being proper without citing that result.

Step 2 uses the coherence characterization on the now locally Noetherian curves, the pullback node's invertibility clause, finite coherent pushforward for F and f_*f^*L, and the cokernel clause of the coherent-abelian node for Q. Each cited statement supplies those precise claims. Finite pushforward's statement deliberately omits higher-image vanishing, so I do not use it for vanishing.

Step 3 uses the finite-morphism definition's affine algebra description and the integral affine function-field node's injective germ maps. Their conclusions identify both coordinate rings with subrings of the common generic field, proving the injection. Localization at the target's nonzero elements then equals that field because it is a subring containing the entire field. This proves both generic-stalk equality and the exact sequence; no normality is assumed.

Step 4 uses coherence iff quasi-coherent finite type, then the scheme-theoretic-support node's actual closed-immersion and support-equality clauses. Closedness and omission of the generic point imply dimension at most zero by the explicit chain argument, with empty support covered. The zero-dimensional Euler-invariance node explicitly includes coherence of Q tensor L and equality of its Euler characteristic with Q, for proper X over any field. These hypotheses are all present.

Step 5 has only definitions as inputs, and it supplies the actual bilinear map and its inverse on every rank-one trivialization, together with agreement under a unit change of basis. This is the ordinary projection formula proved directly; it uses no derived projection formula and hides no non-elementary comparison. Step 6 likewise checks tensor exactness on the same cover, where tensoring is the identity. It uses the definitions of rank-one local freeness and sheaf tensor rather than citing a flatness definition as if it were an exactness theorem.

Step 7 uses the affine-cohomology node's actual isomorphism on all cohomology groups (and its scalar linearity), not merely the vanishing of higher direct images. Proper coherent cohomology supplies finite dimensions and eventual vanishing; the Euler-characteristic definition then gives the two claimed equalities. The morphism is over k, so the relevant scalar restriction is the same k-action throughout. No field extension or residue-field degree is suppressed.

Step 8 takes exactly short-exact additivity from the Euler-additivity statement and exactly invertible-twist invariance from the zero-support statement. The symmetry used to reverse tensor factors is explicitly the elementary map on tensors. Substitution cancels the same chi(Q) on both sides; the subtraction signs were checked against 0AYU. Step 9 applies the degree definition to the two proper curves and the two invertible modules already established.

I checked delivery-errors B--E against the finished files. No new statement is a duplicate, elementary queue item or relabelled clause; no source label substitutes for a node citation. Every non-elementary imported fact has an existing cited node whose statement was opened. The elementary local arguments are written out rather than hidden behind “standard” or “transport.” Each proof step is under 1000 characters, so there is no step over the 2000-character review threshold. All 29 quotations are literal copies of cited statements, and proof_deps is precisely the union of uses.

For small cases, f equal to the identity has Q=0 and both sequences give degree equality immediately. For the normalization of a nodal proper integral curve, Q has nonzero finite support; the proof cancels its Euler characteristic and correctly does not assert chi(O_X)=chi(O_X'). The same check works for a cuspidal curve, so smoothness or normality has not slipped into the proof. A closed point with residue field l contributes its k-dimension, not 1, to chi(Q); twisting preserves that dimension, so a non-algebraically-closed or imperfect k causes no change. L=O gives zero degree on both sides. Empty support is allowed, while empty curves are excluded by integrality as in the statement.

## Unfinished work

None in the stage-1 split. Existing dependencies remain their owners' items. Server dry run and delivery follow this report; no local compiler or DAG-check script is run.
