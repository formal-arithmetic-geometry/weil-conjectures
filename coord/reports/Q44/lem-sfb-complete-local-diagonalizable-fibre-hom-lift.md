# Q44 stage-1 delivery: lem-sfb-complete-local-diagonalizable-fibre-hom-lift

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-complete-local-diagonalizable-fibre-hom-lift.json`: item, split into seven steps; statement and statement dependencies unchanged. Mathlib verdict: no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-flat-multiplicative-deformation.json`: statement-only structural prerequisite; unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-subgroup-identity-neighbourhood-open.json`: statement-only translation prerequisite; unsplit, no Mathlib match.
- `citations.json`: one entry for every use in every step, with the verbatim cited statement. The full statement is quoted so the precise quantifiers and hypotheses are reviewable.
- `searches.jsonl`: actual search-command records, retained unchanged.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact item tag and by diagonalizable, multiplicative type and lifting language found no declaration proving this item. No Mathlib declaration is claimed as an attachment. No Lean was written, built or compiled.

## WANTED

WANTED: Brian Conrad, *Reductive group schemes*, Theorem B.3.2 and its proof, printed pp.288–290, for this item and both new nodes; local archive `literature/conrad-reductive-group-schemes.pdf`. The primary PDF https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf was read online, especially printed pp.285–290. There is no local Conrad file in the permitted literature directory. No document was downloaded or written into the repository. This delivery is marked agent-written because the local archive is missing and the final openness argument is expanded by an agent. There is no SGA citation in the delivery: Conrad's mentions of SGA are not adopted as sources.

## Corrections and limits

The item is a faithful split-source instance of Conrad B.3.2(2): the target is only affine, flat and finite type; its special fibre, rather than the whole target, is assumed multiplicative type. Both the Hom bijection and the open-and-closed assertion are retained. No STATEMENT-DISPUTED correction is necessary.

The source's proof on printed p.289 invokes Corollary B.2.6 while lifting an isomorphism to a diagonalizable group that can be nonsmooth. B.2.6 explicitly assumes a smooth target, so it does not by itself supply that step when the character group has residue-characteristic torsion. The delivery does not apply that corollary: the genuine infinitesimal deformation assertion is isolated as a new structural theorem. In particular, it does not claim that the existing smooth square-zero lifting node proves it. This is a source-proof gap in the displayed justification, not a counterexample to the theorem. The new node is deliberately left unsplit for an actual nonsmooth deformation proof.

The inherited unit is `sk-thm-sf-ctf-stability` and chapter is `sec-six-functors-basics`. I read both DAG records, the three-level requirements in SETUP, and the current latest blueprint direct-images proof at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). This remote structural prerequisite is far below that step. No unit or chapter route was changed. The inherited creation chain terminates at a module-name record, so `blueprint_refs.py ancestor` returns null. I preserved the item's existing null `from.node`, its explicit place and its via list; each new node extends the same chain and identifies the exact B.3.2 proof paragraph it serves. Whole-blueprint searches found no equivalent imported theorem, so `same_as=[]`.

There are no unfinished steps of this split, but the two new prerequisite statements still need their own stage-1 splits. No existing node was edited except the assigned item in the sandbox. The previous six Mathlib searches in the live item are retained, and four fresh actual searches were appended (two script reruns temporarily appended the same records again; they are genuine log entries, not invented searches). All added searches are supported by this sandbox's command log. No inference of absence is based only on grep or on an unavailable service.

## Not duplicates

lem-sfb-nilpotent-flat-multiplicative-deformation vs lem-sfb-complete-local-diagonalizable-fibre-hom-lift: the new node concerns the structure of a flat group across an arbitrary nilpotent ideal, with no complete ring and no Hom-from-an-arbitrary-source conclusion; the item assembles compatible homomorphisms and proves an immersion over a complete local base.

lem-sfb-nilpotent-flat-multiplicative-deformation vs lem-sfb-square-zero-diagonalizable-hom-lift: the existing result requires a smooth target and only constructs a homomorphism; the new node treats possibly nonsmooth flat deformations and constructs a diagonalizable group structure. It is not a specialization of smooth lifting.

lem-sfb-nilpotent-flat-multiplicative-deformation vs lem-sfb-adic-diagonalizable-hom-effectivity: effectivity starts with a supplied compatible family; it neither constructs that family from a special fibre nor recognizes nilpotent multiplicative-type deformations.

lem-sfb-nilpotent-flat-multiplicative-deformation vs lem-sfb-relative-diagonalizable-character-duality: duality requires the groups to be split diagonalizable already; the new node establishes the missing structure from the reduction of a flat group.

lem-sfb-nilpotent-flat-multiplicative-deformation vs lem-sfb-multiplicative-type-fpqc-descent: fpqc descent assumes multiplicative type after a flat cover; a nilpotent quotient is not such a cover. The new node supplies nilpotent deformation, not fpqc descent.

lem-sfb-nilpotent-flat-multiplicative-deformation vs lem-sfb-diagonalizable-nilpotent-triviality: the existing node forces an already defined homomorphism to be trivial; it says nothing about recognizing the structure of a deformed group.

lem-sfb-nilpotent-flat-multiplicative-deformation vs lem-sfb-complete-local-split-torus-hom-lift: the latter has smooth target and free characters, constructs lifts from a torus over a complete ring, and cannot handle the nonsmooth infinitesimal structural assertion.

lem-sfb-flat-subgroup-identity-neighbourhood-open vs lem-sfb-complete-local-diagonalizable-fibre-hom-lift: the new node starts with an existing closed subgroup and an actual identity neighbourhood it contains; it constructs no homomorphisms and has no completeness, diagonalizable or special-fibre hypotheses.

lem-sfb-flat-subgroup-identity-neighbourhood-open vs lem-sfb-local-torus-subgroup-special-trivial: the latter detects triviality of a closed subgroup inside a split torus over a local base; the new node recognizes openness of a supplied flat subgroup over an arbitrary scheme.

lem-sfb-flat-subgroup-identity-neighbourhood-open vs lem-pe-flat-lfp-monomorphism-open: the existing node assumes the immersion H → G is flat. The new one assumes only that H → S is flat and contains a neighbourhood; proving flatness/openness of H → G is its content.

lem-sfb-flat-subgroup-identity-neighbourhood-open vs lem-sfb-flat-closed-family-ideal-base-change: that node gives exactness and finite type for the ideal after base change; it does not propagate an identity neighbourhood by group multiplication.

lem-sfb-flat-subgroup-identity-neighbourhood-open vs lem-sfb-affine-multiplicative-type-monomorphism-closed: the existing theorem gives closedness from a multiplicative source; it does not give openness or the translation criterion.

lem-sfb-flat-subgroup-identity-neighbourhood-open vs lem-sfb-smooth-group-relative-neutral-open: the latter constructs a fibrewise identity component for smooth groups over a DVR; the new criterion is about an arbitrary given flat subgroup and an actual neighbourhood, over any scheme.

lem-sfb-flat-subgroup-identity-neighbourhood-open vs lem-sfb-adic-diagonalizable-hom-effectivity: no formal Hom or effectivity assertion occurs in the new node.

lem-sfb-flat-subgroup-identity-neighbourhood-open vs lem-sfb-complete-local-split-torus-hom-lift: the existing theorem produces lifts from split tori with smooth target and concludes closedness; the new one concerns a supplied subgroup and concludes openness without smoothness.

## Proof plans for the statement-only prerequisites

For nilpotent flat deformation, reduce successively to square-zero ideals. The needed input is genuine deformation theory of flat Hopf algebras with diagonalizable reduction, including nonsmooth characters: degree-two regular cohomological obstructions vanish for diagonalizable groups. A lift of the Hopf structure's prescribed diagonalization yields the asserted group isomorphism, not merely an underlying scheme isomorphism. The general multiplicative-type assertion is the local version of that structural theorem. Conrad identifies exactly this prerequisite on p.289; the displayed citation to the smooth corollary is not sufficient for torsion. A later split must provide that calculation, rather than assume a smooth diagonalizable target or appeal to forbidden SGA sources. The present node is a complete statement, not a proof sketch disguised as a statement.

For the translation criterion, let V → H → G be as stated. The map a:H ×_S V → G, (h,v) ↦ i(h)v, factors through H. On H ×_S G, the map (h,g) ↦ (h,i(h)g) is an automorphism, with inverse using h inverse; its restriction to H × V followed by the second projection is a. The projection is the base change of H → S, hence flat and locally finitely presented, and these properties imply a is open. Its image O is open and contains i(H), since e_V supplies (h,e_V) over every test scheme; conversely the factorization through H gives O contained in i(H). Over O, a is a surjective flat locally finitely presented morphism. Pullback of the closed ideal of H in O vanishes because a factors through H. Faithfully flat detection of zero modules, affine locally on this covering, makes that ideal zero. Thus H → G identifies H scheme-theoretically with O. This is a genuine sheaf/flatness argument and is not the two-line topological assertion about a subgroup of a topological group. The generic lemma is independent of completeness and of diagonalizable groups; it is not one clause of the item under renamed hypotheses.

## Review by Q44

I read the primary source's exact B.3.2 statement, its reduction to Artinian bases, the square-zero structural assertion and final kernel/flatness argument on printed pp.288–290. The Hom statement agrees hypothesis by hypothesis; the source allows torsion and does not assume target smoothness or commutativity. I retained all these features. I read B.2.6 as well and corrected the tempting but invalid smooth-target application described above. For the second new node I read the source's translation paragraph, and wrote out the separate generic flat-subgroup argument above, whose inputs are different from the item's conclusions.

For Step 1 I opened the affine fibre-product, finite-type/Noetherian finite-presentation, and flat-module base-change statements. They give exactly tensor-coordinate base change, finite presentation and flatness of the reduced coordinate algebra. Reducing the displayed finite generators and relations is elementary. The new deformation node has flatness and finite presentation as hypotheses; both are checked before its use, and its quotient ideal is nilpotent. I do not use a smooth lifting theorem here.

For Step 2 I read every clause of relative character duality: on an open cover each homomorphism is uniquely a character map and that map is locally constant. Nilpotent quotients preserve the whole underlying topology, so the same locally constant maps give the unique lift on a diagonalizing affine. This does not assume R is connected or reduced. The fppf affine-refinement theorem supplies the covering affines; ordinary morphism gluing supplies equality on overlaps after affine localization. Fppf base-change and fppf-to-fpqc statements make the pulled-back covering of H_n an fpqc covering, and representable descent states existence and uniqueness of precisely the maps being glued. Its uniqueness also checks all three group equations, by pulling the cover back to products as necessary. I checked that none of these citations is merely a definition replacing descent.

For Step 3 I read the full effectivity statement: it requires a complete Noetherian local ring, finitely generated characters and an affine finite-type target; it does not require smoothness. All are present. Compatibility is proved by the finite-level uniqueness from Step 2, not assumed. Its injectivity gives the required global uniqueness, including for the later j.

For Step 4 I read the affine fibre-product formula, affine quotient definition of closed immersion, and local split-torus subgroup theorem. I form the actual scheme-theoretic kernel. Its immersion into the torus comes from a surjection Z^t → M and composite surjections of algebras; this allows torsion. The existing local subgroup theorem does not assume flatness of the subgroup, and its hypothesis is exactly that its special fibre's identity section is an isomorphism. The special-fibre isomorphism j_0 gives that hypothesis. Trivial kernel implies a monomorphism on every test scheme by cancellation, not only on field-valued points.

For Step 5 I opened the affine-target multiplicative-type monomorphism theorem; finite presentation was proved in Step 1 and monomorphy in Step 4. It gives closedness, not openness. The ring-flat/affine-flat equivalence gives the two relative flatness statements from the free source algebra and the assumed flat target. I read the full ideal-base-change statement, including its exactness at the left: with T=S, X=G, Z=H it identifies L/mL with the kernel of the special-fibre coordinate map, so L=mL follows from that coordinate isomorphism. The finite-type algebra theorem makes B Noetherian, and the definition of Noetherian makes L finite as a B-module. L is not asserted finite over A.

For Step 6 I read the annihilator version of Nakayama: it permits any ideal and produces f in 1+mB annihilating L. I deliberately do not claim mB is in the Jacobson radical of B. The principal-open affine-ideal node's clause (0) gives the actual affine open and its localization ring; the annihilation identifies the localized quotient with it. The identity section lands there because its augmentation sends f to a unit of A. A set-theoretic containment alone would not have been enough to factor V through H; here the ideal really vanishes.

For Step 7 I checked the new translation theorem's exact hypotheses: an existing closed subgroup, H flat and locally finitely presented over the base, an actual factorization V → H, and an actual identity section S → V. Steps 1, 5 and 6 supply each. Its conclusion supplies openness and Step 5 supplies closedness. Thus this is a proof of the item's second clause, not a citation to a renamed special-fibre immersion assertion.

I checked delivery-errors B through E against all three JSON files. Both new nodes introduce every object, define multiplicative type/group schemes inline or cite their definitions, have empty proofs/proof dependencies, no argument in their statements, accurate primary-source places and genuinely run search entries. DAG searches included B.3.2, diagonalizable, multiplicative type, deformation, nilpotent and subgroup/identity/open, and the whole-blueprint search commands were run before creation; all potentially close statements were opened and are distinguished above. The query hits concerning formally unramified/smooth algebras and topological groups do not match. No source tag has been fabricated for a structural theorem absent from Stacks. The actual Stacks facts used are cited by existing nodes, especially 00FP (finite presentation), 00HI (flat base change), 023Q (descent), 00DV (Nakayama), and 00HL/01TV/02FV in the ideal-base-change node.

Small cases: M=0 gives the identity source and a unique homomorphism; for a trivial special fibre, the kernel and identity-neighbourhood proof still apply. A field base makes every A_n equal A and the Hom reduction the identity. An Artinian nonreduced base is directly the nilpotent situation. M=Z/p in residue characteristic p gives mu_p, not a smooth torus: this is why no smoothness claim is made. Split nonsmooth targets are handled by character duality. The statement-only nilpotent theorem is consistent with I=0 and with a flat deformation of mu_p; dropping flatness would be false and is not done. For the translation theorem, H=G works with V an identity neighbourhood; the identity subgroup of G_a over a field has no containing open neighbourhood in G_a, so it does not satisfy the hypotheses. Empty base and rank-zero source cause no obstruction. The localization/Nakayama argument uses a finite B-module, not an infinite source algebra treated as a finite A-module.

Every non-elementary item step is shorter than 2000 characters. I have extracted the nonsmooth deformation argument and the generic scheme-theoretic translation argument instead of hiding either in a long step. The remaining algebraic manipulations are written explicitly. No alternate chapter route or weakened hypothesis has been used.
