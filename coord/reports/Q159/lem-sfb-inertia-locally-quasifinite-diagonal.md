# Worker report: lem-sfb-inertia-locally-quasifinite-diagonal

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-inertia-locally-quasifinite-diagonal.json: item, statement unchanged, six proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-locally-quasifinite-pseudo-torsor.json: new statement, unsplit; no Mathlib match. This is Stacks 0DSK(2), not the existing unramified 0DSK(1) lemma.
- citations.json: one entry per cited node per numbered item step, with exact substrings of the cited statements.
- searches.jsonl: actual outputs/digests recorded by the required msearch command; ten searches for the item and new-node concepts, including two semantic phrasings for each.
- report.md: this report.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and item id, inertia/diagonal, algebraic-stack and pseudo-torsor terminology. No project declaration states the item or the new lemma. No Lean was written or compiled.

## WANTED

None. All mathematical sources needed here are present in literature/stacks-project/.

## Problems found and changes

The live item is unsplit and contains no proposed proof. Its statement agrees with Stacks stacks-morphisms.tex, 0CL0 (lemma-diagonal-diagonal), part (5), including arbitrary morphisms of algebraic stacks, relative rather than absolute inertia, representability, and the special case of a scheme target. No statement dispute or source error was found; no hypothesis or conclusion was changed. There is no repair note for this item.

The source's relative Isom pseudo-torsor reduction must retain the condition f(phi)=alpha, and its group consists of automorphisms whose image is the identity. Using the whole absolute automorphism group would be wrong for a stack target. Steps 2 and 5 explicitly retain and verify these conditions. The local finite type of BOTH the pseudo-torsor and the group is needed by 0DSK; step 4 obtains it from the already existing relative-diagonal theorem rather than from the absolute Isom theorem, which would not by itself supply the relative fibre assertion.

No unfinished work remains in the one-level split. The new node intentionally has a statement only and joins the subsequent queue. Its proof route, for a future worker, is the source's 0DSK(2): quasi-finiteness at a point is tested after passing to the residue field of its image, then after a field extension supplying a point of the pseudo-torsor; that point identifies the fibre pseudo-torsor with its acting group. The empty fibre is harmless. This is not elementary local algebra, and is correctly a supporting lemma rather than an inline unproved assertion. It is not a restatement of either implication of the stack criterion.

## Searches and blueprint route

Read AGENTS.md, the worker role, coord/brief-stage1.md, stages/1-dag.md, SETUP.md including its three levels and tool-lemma rule, GOAL.md, coord/STATE.md and tools/README.md. The human's task-specific stage-1-only and sandbox-only instructions govern this work. No agents were started.

Read dag/chapters/sec-six-functors-basics.json and dag/units/sk-thm-sf-ctf-stability.json, and the latest blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This is a supporting input below that route's finite-inertia construction, not the unit's key statement; no unit record needs realization changes. The ancestor command returns None, as the item already records. The inherited from.node, via chain and exact from.place are preserved, and the new node extends that chain with the item and the precise 0DSK(2) use. Whole-blueprint searches for inertia, pseudo torsor, 0CL0, 0DSK, quasi-DM and locally quasi-finite found no equivalent blueprint statement. Searches of the whole DAG for tags, labels and concepts found the existing relative-inertia geometry and relative-diagonal local-finite-type nodes, which are reused.

The Mathlib searches were made through /home/ubuntu/weil-launcher-all/batch2/msearch.py, with actual queries retained in the node records and searches.jsonl. LeanFinder, Loogle, grep and LeanSearch all answered. LeanSearch/LeanFinder returned scheme locally-quasi-finite classes and permanence results, ring-map results, or unrelated topological group actions. I read Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean: these declarations concern schemes and cannot specialize in one line to the algebraic-space pseudo-torsor lemma or stack criterion. In particular the source notes that Mathlib's bare LocallyQuasiFinite does not itself require local finite type, so it is not silently identified with the source's notion. The grep searches found no algebraic-space, algebraic-stack or pseudo-torsor API, and the Loogle conjunctions found no hit. There are zero Mathlib leaves in this delivery. The item's inherited searches are retained, followed by the new actual searches.

## Not duplicates

lem-sfb-locally-quasifinite-pseudo-torsor vs lem-sfb-unramified-pseudo-torsor: the existing node is 0DSK(1), transferring unramifiedness; the new node is 0DSK(2), transferring local quasi-finiteness, allowing infinitesimal groups such as mu_p and therefore not a specialization of the unramified assertion.

lem-sfb-locally-quasifinite-pseudo-torsor vs lem-sfb-smooth-atlas-automorphism-diagonal-test: the existing node is an absolute stack diagonal's unramifiedness criterion tested on one smooth atlas; its proof cites 0DSK(1). The new node is a general algebraic-space pseudo-torsor lemma for local quasi-finiteness and assumes neither a stack nor a chosen atlas.

## Review by Q159

I read stacks-morphisms.tex 0CL0 (lemma-diagonal-diagonal), its full statement and proof, the higher-diagonals paragraph preceding it, 04XS (lemma-properties-diagonal), and 0CPK (lemma-isom-pseudo-torsor-aut-over-space). I also read spaces-groupoids.tex 04TW (definition-pseudo-torsor) and 0DSK (lemma-pseudo-torsor-implications), including both parts and its proof. The item is precisely 0CL0(5) with quasi-DM expanded; the new node is precisely 0DSK(2), with group structure, action and pseudo-torsor conditions written out. Its two local-finite-type hypotheses have been retained, and no flatness, surjectivity, separation or Noetherianity is added.

For step 1 I opened lem-sfb-relative-inertia-second-diagonal-geometry and read its entire statement: it explicitly supplies representability of both maps, the same relative inertia, and the ordinary-inertia specialization. For step 2 I opened def-sfb-stable-pointed-moduli-groupoids: it defines the fibrewise 2-fibre-product triples and their arrows. The displayed maps and inverses calculate those triples directly and commute with pullback; conjugation is checked to remain in the relative kernel. This uses a definition rather than pretending that definition asserts a theorem about Isom spaces. Step 3 is elementary testing: the arbitrary scheme fibre of inertia and the special diagonal scheme fibre are the SAME sheaf over the SAME T, so their chart projections coincide. It uses no unmentioned stack-level descent or base-change theorem.

For step 4 I opened lem-sfb-stack-relative-diagonal-finite-type. Its statement explicitly gives an algebraic space locally of finite type over every testing scheme, for arbitrary algebraic-stack morphisms; it applies to (a,b,alpha) and (b,b,1). This justifies the relative J and H, not merely absolute Isom spaces. Local quasi-finiteness of H is the given inertia hypothesis tested at b. The group operations are the fibre-groupoid operations of the cited definition; their kernel condition is preserved by f. In step 5 the same definition supplies composition and inverse. I checked the formula (psi,phi) maps to (psi phi^{-1},phi), its kernel condition f(psi phi^{-1})=alpha alpha^{-1}, both inverse equations, action laws, and compatibility with arbitrary pullback. These elementary calculations prove the pseudo-torsor condition even for an empty J and require no existence of isomorphisms a to b.

In step 6 I read the new node's statement again: it transfers local quasi-finiteness from a locally finite type group to a locally finite type pseudo-torsor. Step 4 verifies the two finite-type assumptions and group hypothesis, and step 5 verifies its exact action isomorphism. Its base B is the scheme T regarded as an algebraic space, and its S is the original arbitrary base. Every diagonal test is covered. All uses are quoted verbatim in citations.json, and proof_deps is exactly their union. The statements used by non-elementary steps say precisely what those steps take from them; none uses a construction buried only in another proof.

Small cases checked: empty X and empty Isom fibres; f=id_X, where relative inertia is trivial even if X has large absolute stabilizers; a scheme X, whose automorphisms over a fixed test are trivial; BG_a over a field, where the diagonal and inertia both have positive-dimensional fibres and fail the criterion; and Bmu_p in characteristic p, where both are locally quasi-finite but generally not unramified. For the new node I checked X empty, X=G, the trivial group, and G=mu_p with its own translation action. A positive-dimensional G_a does not satisfy its locally quasi-finite hypothesis. No finite-group order or reducedness assumption was smuggled into the action argument.

I checked delivery-errors B through E against the node files: the new node introduces all objects, defines its group/action/pseudo-torsor notions and cites all other notions; it has no proof or proof-dependency sketch, and its source tags and labels were read. The two same-tag existing nodes differ as documented above. No new node is elementary, duplicated, a clause of the item, or already a one-line Mathlib specialization. All six proof steps are under 2000 characters; the longest is 958, so there is no long step hiding a comparison lemma. The explicit comparisons here are direct formulas in the cited 2-fibre-product definition. The statement, source, ancestry and other maintainer fields of the item are retained. No SGA is used and no off-unit theorem is used as a new tool. I corrected the potential relative/absolute Isom confusion before writing the split; no mathematical correction to the live statement was needed.

Required server dry run and delivery are recorded by the delivery tool after this report is written.
