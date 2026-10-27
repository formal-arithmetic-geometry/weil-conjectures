# Stage-1 delivery: lem-sfb-relative-self-normalizing-quotient

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-self-normalizing-quotient.json — statement unchanged; nine-step split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-jet-normalizer-detection.json — new statement-only node; unsplit; no Mathlib match after LeanSearch, LeanFinder, qualified Loogle and two source greps.
- citations.json — one verbatim statement quotation for every step/node citation.

No Lean, library, launcher, repository or unit file was written. The sandbox initially contained only dispatcher markers, with no previous node, report or search log to resume.

## Attachments

None. Searched the live project's WeilConjectures/ tree for the exact blueprint id, self-normalizing/normalizer, homogeneous quotient, and fppf quotient terminology. No declaration proves this item. Existing field-only homogeneous-space nodes and their declarations do not cover an arbitrary affine base. No attachment claim is made for a declaration containing sorry.

## WANTED

WANTED: Brian Conrad, Reductive group schemes (2014), Theorem 2.3.6 and proof, printed pp.72–75; Proposition 2.1.6 and proof, pp.61–63; literature/conrad-reductive-group-schemes.pdf, for the item and lem-sfb-finite-jet-normalizer-detection. Read the primary author's PDF online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf. No local copy exists in literature. The item's assembly is marked agent-written; its actual argument is present in the steps. No prohibited source is used.

## What was wrong or needed completion

The item was an unsplit statement with no proof. It is mathematically consistent with Conrad's theorem and no statement correction was necessary. In particular, fibrewise projectivity alone was not used as an unconditional properness criterion: smoothness, separatedness, finite presentation, nonemptiness and geometric connectedness are all supplied before the properness argument.

The existing node lem-sfb-connected-proper-fibres-proper assumes a locally Noetherian base. Applying it directly to Spec A would omit a hypothesis. Instead the proof follows Conrad's clopen-component argument using the existing arbitrary-henselian-pair lifting result (Stacks Tag 0CT9) and existing strict-local properness test. This retains the source's argument while covering the actual arbitrary-ring statement, without silently imposing Noetherianity.

The nearest-ancestor command reports blueprint.from.node = None. The item's supplied null ancestor and full via chain were retained, and the new node adds the item to that chain. The latest blueprint direct-images proof, literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, was read. Its step (3) is the ancestor place supplied by the live item; the long chain concerns an auxiliary rank-one flag quotient used below that route. Neither the chapter nor the unit route was changed.

## Not duplicates

lem-sfb-finite-jet-normalizer-detection vs lem-sfb-relative-smooth-subgroup-normalizer: the existing node represents the full normalizer as a closed finitely presented group scheme and proves its base-change identification; it does not state finite locally free identity jets or that one finite jet already detects the full normalizer. The new node makes no assertion that the full normalizer is smooth or that any quotient exists.

lem-sfb-finite-jet-normalizer-detection vs lem-sfb-relative-self-normalizing-quotient: the new node assumes no self-normalizer hypothesis and has no quotient, torsor, smooth-quotient or properness conclusion. It supplies finite linear data for the argument, rather than repeating a clause of the item.

lem-sfb-finite-jet-normalizer-detection vs lem-sfb-free-quotient-grassmann-projective: the Grassmannian node represents arbitrary quotient bundles and supplies its projective embedding; it says nothing about group-scheme jets or normalizers. The item cites that existing Grassmannian theorem separately.

Searched the whole DAG for the source theorem, normalizer, infinitesimal neighborhoods and finite-jet phrases, and ran blueprint_refs.py searches for self-normaliz, normalizer, infinitesimal normalizer, infinitesimal neighborhood/neighbourhood and Grassmann. None states the new lemma. Broader searches found field homogeneous quotients, existing free-action algebraic-space quotients, schematicity and properness tools, which were reused. The finite-jet result is not a two-line consequence of the normalizer definition: its source uses universal weak schematic density, finite-flat jet algebras and Noetherian stabilization with finite-presentation approximation.

## Review by NX

I read Conrad Theorem 2.3.6 including the Grassmannian construction on printed p.74 and the clopen proper-part argument on pp.74–75. For the new finite-jet lemma I read Proposition 2.1.6 and its proof on pp.61–63: it explains universal weak schematic density, finite-flat infinitesimal neighborhoods, and the direct-limit reduction. I also read the p.74 stabilization paragraph. On a Noetherian model the descending closed normalizers stabilize; the finite presentation and universal base-change description permit the same finite-order detector after pullback to A. Finite Zariski refinement trivializes the two finite locally free jet algebras, including their ranks. This is the retained proof plan for the new unsplit statement, not a claimed completed proof in its JSON. In the item's proof it is used only to construct a faithful orbit map into an existing Grassmannian.

I opened every cited node and read its statement. citations.json contains their verbatim statements, so each use can be compared directly. In particular:

1. The free-action node explicitly gives an algebraic-space quotient, flat lfp surjection, local sections and the relation isomorphism. The action h.g = g h^{-1} has the requested right-coset orbits. Smooth-flat supplies precisely the needed flatness/lfp of H, with no normality assumption.
2. The same quotient node supplies local lifts on every scheme test. The displayed maps b to a^{-1}b and h to ah identify the pullback with H. The smooth base-change/fppf-locality node applies to those scheme test targets, and the lft source-and-target locality node explicitly allows the smooth cover G to Q. No field-base torsor representability lemma is used over arbitrary A.
3. The relation closed immersion is the pullback of the given H to G under (g,b) to g^{-1}b. The covering-calculus node gives the double fppf cover, and the closed-immersion fppf-descent node says exactly that this descends. The qcqs-source node supplies absolute quasi-separatedness after relative separatedness. Continuity and point-surjectivity are in the point-calculus node, and the compact-image argument is written out.
4. The new node gives the finite free quotient C to D and identifies its functorial stabilizer with the full normalizer on every test scheme, not only geometric points. The Grassmannian node classifies exactly these quotient bundles and includes ranks 0 and M; here r is positive because the identity lies in H_n. Self-normalizing then identifies that stabilizer with H. The sheafification definition supplies the extension of the orbit map; the local-sections node supplies local lifts and local equality, proving injectivity. No use of a mere definition as a quotient-existence theorem occurs.
5. The lft-cancellation node has algebraic spaces as source and target, unlike a scheme-only cancellation theorem. The qcqs lft-monomorphism node applies because both spaces were proved qcqs and the orbit map was proved monic; its conclusion includes representability by schemes. The projective-proper node supplies the target's quasi-compactness and separatedness. I replaced an earlier informal claim of Zariski-local schemeness with the existing lem-galois-glue statement: the overlaps represent the same sheaf and hence give the precise cocycle it requires.
6. The source-descent theorem expressly assumes a flat surjective lfp map of schemes and a smooth composite. These are now available because step 5 has made Q a scheme. It proves the required smooth structural map. The qcqs-morphism statement, read in full, supplies both finite-presentation finiteness conditions.
7. Base change is proved using local representatives and their ratio in H. The cited sheafification statement has both local existence and local equality. The argument does not commute arbitrary sheafification with arbitrary inverse image by assertion, nor identify presheaf sections with quotient-sheaf sections globally. The relation formula is unchanged under pullback, giving the actual torsor identification.
8. Projectivity implies properness by the cited statement. Connectedness and nonemptiness are continuous-image consequences of the actual geometric fibre map. The strict-local properness statement assumes finite presentation, already proved in step 6, and has no Noetherian hypothesis. The strict-henselization structure statement supplies a local henselian ring. I corrected the initial citation for separated base change to the algebraic-space separated/fp composition node, whose statement explicitly includes it; the proper-permanence node alone did not state that clause. Smooth base change is also cited explicitly.
9. The henselian clopen-lift node allows an arbitrary henselian pair and a separated finite-type scheme, which Y is. Its conclusion gives a proper clopen Z, not merely a formal subscheme. Residue-field properness descends by the fpqc properness node, whose statement permits this field extension. Smooth restriction and smooth-flat give flat lfp of Z; the open-map theorem supplies openness and properness supplies closedness. Surjectivity, geometric fibre connectedness and exhaustion are then explicit set/topology arguments. I corrected the source tag to 0CT9 by consulting the Stacks tags file; 0CWI is its algebraic-space analogue, and the initial 0AG1 label was not retained.

Every non-elementary input is a cited statement; definitions are used only for their meanings. All generic off-unit tools are declared in split_report.tool_uses. I checked the existing dependencies transitively for a cycle back to the item before citing them. The one elementary step is the local section/equality proof of arbitrary base change from the already-established torsor; it is a few-line consequence of the cited statements, not a separate new node. No proof step exceeds 2,000 characters and no argument is parked in a statement-only node's proof fields.

Small-case checks: A = 0 gives the empty base and empty conclusions; H = G gives X = S and trivial Grassmannian stabilizer orbit; G = H = 1 gives rank-one jet algebras and the point Grassmannian; H = 1 in a nontrivial G is excluded by self-normalizing, as it must be. For the new lemma H = 1 and H = G are both valid, without self-normalizing; identity jets have positive rank, relative dimension zero gives rank one, and ranks may vary only before the prescribed open refinement. The proof never replaces the group-scheme normalizer by its geometric-point normalizer, which would lose nilpotent tests. The closed fibre need not be algebraically closed: properness descends from its algebraic closure before henselian lifting.

## What could not be finished

No unresolved mathematical issue for this one-level split. The new finite-jet detection statement is intentionally unsplit for the next stage-1 item. There are zero new Mathlib leaves. Server dry-run and delivery results follow below when obtained.
