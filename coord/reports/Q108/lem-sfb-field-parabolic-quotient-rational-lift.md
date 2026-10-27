# Worker report — Q108

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-parabolic-quotient-rational-lift.json: item, split into seven steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-infinite-field-reductive-rational-density.json: new statement-only unsplit input.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-connected-group-torsor-point.json: new statement-only unsplit input.
- citations.json: verbatim statement excerpts covering every step/node citation.

Two new nodes, zero new Mathlib leaves. The former cocharacter-presentation node is removed from dag/nodes; its record and the previous proof, report and citations remain in repair-history/. The original searches.jsonl and all surviving nodes' search records are retained.

## Repair of the returned delivery

The return concerns the reader-approved head 5081f632ee8 and asks for rebasing onto the current DAG, rereading changed citations, adjusting the split and pushing again. It supplies no numbered mathematical objections. The printed route notices explicitly say they are recorded rather than refused; they are not treated as the failure reason. Before changing the retained split I ran the required dry run; it exited successfully at 25b0b073d95. I also ran server review_split, which passed. Thus the truncated landing failure does not reproduce with the retained split on the current base.

I nevertheless found and repaired the substantive current-DAG overlap. The existing lem-sfb-parabolic-prescribed-split-cocharacter supplies a stronger cocharacter presentation once a maximal split torus in P is supplied. I removed lem-sfb-rational-parabolic-cocharacter-presentation from this delivery and replaced its use by that existing node. The additional hypothesis is now proved, not assumed: tangent injections bound the ranks, and the integer-matrix description plus surjectivity of the Laurent-coordinate map shows an equal-rank closed torus inclusion is an isomorphism. This makes a greatest-rank split torus maximal under inclusion. The old cell step is now step 4 and its descendants have been renumbered.

I read the current server statements of every retained proof citation and every statement dependency and compared them with the read clone. None differs at the time of this repair; repair-current-citations.json records the complete statements read. In particular the general homogeneous quotient still supplies flatness, surjectivity, finite presentation and equality on all test schemes; the dynamic-subgroup node still supplies the opposite multiplication open immersion; the open-subfunctor node still permits arbitrary sheaves with an fppf local presentation. The three additional existing statements used for the bounded-rank argument were read in full. Delivery tooling builds on current origin/sheaf-dag and preserves the base's maintainer-owned fields; no repository git command or write was used.

## Attachments

None. The retained Lean searches and a fresh search in lean/WeilConjectures for the exact item tag, parabolic and cocharacter found no project declaration stating the complete item. No Lean was written or compiled.

## WANTED

None. The Milne PDF and Stacks sources are available and were read. No SGA source is used.

## Sources and blueprint

The item's proof follows Milne, Algebraic Groups, Theorem 25.9(b), printed p.546: an opposite cell and density when the field is infinite, and Lang's theorem on the fibre torsor when it is finite. I reread Theorem 25.1 and its Galois-averaging converse on p.544 and the prescribed-torus choice in Theorem 25.6(b) on p.546. The existing stronger cocharacter node is used precisely for that choice. The new density statement is exactly Theorem 17.93(b), p.382, including its parenthetical density conclusion. The new finite-field statement is the torsor form of Corollary 17.98, p.383, with Proposition 3.50, p.80, and Definition 2.66/Proposition 2.69, p.60, providing the meaning of torsors and their H^1 classification.

The inherited blueprint ancestry is broken: the recorded ancestor query returned None. The null from.node and detailed place/via are retained. The latest blueprint's det-thm-sf-ctf-stability-direct-images proof (3), with its alteration/moduli prerequisites, is the inherited route through Milne 25.10 to rational lifting in 25.9(b). No unit or chapter record is edited. I reread the assigned chapter and unit records. The latest blueprint has no duplicate cocharacter, density or Lang statement (recorded searches retained; the additional search for 'parabolic cocharacter' returned no match).

## Searches

The original whole-DAG, blueprint and project-source searches and their results remain in the archived report. Current-DAG searching additionally found lem-sfb-parabolic-prescribed-split-cocharacter; it replaces the removed proposed cocharacter node. I opened lem-sfb-split-torus-hom-matrices and lem-sfb-affine-group-dual-number-calculus before citing them. The latter states both finite dimensionality and injectivity for closed subgroup tangent maps; the former states all split-torus homomorphisms are integer monomials, including rank zero.

All Mathlib searches were run with msearch.py and recorded verbatim in searches.jsonl and the node records. Both surviving new nodes have LeanFinder, Loogle, grep, LeanSearch and a second phrasing; all services answered. The results were reread instead of rerunning unchanged questions. Partial-map domain density does not assert rational-point density. Abstract AddTorsor assumes Nonempty, and Hilbert90 concerns field-extension units, so neither proves Lang's theorem for arbitrary connected group torsors. The item's searches give abstract cosets and modular cusps rather than rational points of a represented quotient. No new node or changed search question is introduced in this repair.

## Not duplicates

- lem-sfb-infinite-field-reductive-rational-density vs lem-pc-rational-points-dense: the existing statement requires a separably closed field and allows arbitrary smooth schemes; the new statement concerns reductive groups over every infinite field, including imperfect fields.
- lem-sfb-finite-field-connected-group-torsor-point vs lem-sc-lang-steinberg: the existing statement concerns semilinear vector spaces over an algebraically closed field, rather than arbitrary connected algebraic-group torsors over finite fields.
- lem-sfb-finite-field-connected-group-torsor-point vs lem-sfb-additive-affine-torsor-section: the existing statement concerns additive-group torsors over affine bases, while the new input allows every smooth connected affine group over a finite field.

The two new inputs state neither the quotient torsor/kernel assertion nor rational surjectivity for a parabolic quotient. They are independent general inputs in its proof. The removed cocharacter node would now be redundant with the prescribed-torus node after the explicit elementary choice argument.

## Review by Q108

I checked the repaired item against Milne 25.9(b), p.546, with the source open; its statement retains every original clause and hypothesis byte for byte after JSON decoding. The quotient construction follows Milne 5.24–5.28, pp.104–105; the opposite product is 13.33(d), pp.265–266. For both new nodes I reread the exact source statements listed above: 17.93(b) requires reductivity rather than perfectness, and 17.98 requires connectedness over a finite field. Smoothness permits the torsor interpretation through 3.50. Both new nodes are self-contained, statement-only, with inline meanings and definition dependencies, blueprint ancestry and genuine logged searches.

Step 1 uses lem-sfb-algebraic-group-homogeneous-quotient exactly for its separated finite-type quotient, finite presentation and all-test equality criterion. Affine G is separated by the displayed coordinate-ring diagonal argument. The explicit inverse (g,h) -> (g,g^{-1}h) gives the torsor isomorphism. The base-change covering statement supplies fppf local lifts; the gluing statement lem-a1-algebraic-space-fpqc-sheaf, after def-trf-scheme-algebraic-space and lem-trf-fppf-covering-is-fpqc, identifies that quotient with the specified sheafification and constructs the action. All five cited statements were read and their hypotheses checked. Step 2 is the elementary evaluation of the established torsor isomorphism at (1,g), including both implications on nonreduced test algebras.

Step 3 now cites the current prescribed-cocharacter statement, not a new restatement. Its G and P hypotheses are exactly those of the item. To obtain its S hypothesis, lem-sfb-affine-group-dual-number-calculus gives finite tangent dimension and injectivity under closed inclusion; the explicit dual-number units calculate the tangent dimension of a rank-r split torus. Ranks are thus bounded and rank zero occurs. The integer monomials of lem-sfb-split-torus-hom-matrices and the surjective coordinate map from def-weil-closed-immersion show that a same-rank closed inclusion has a unimodular exponent matrix and an inverse. This argument supplies maximality under inclusion without using rational conjugacy or any descendant of the item. I read Milne 10.14, printed p.190, for tangent injections, and 12.9(a), pp.233–234, for the torus-map classification. These statements say exactly what is used; the rank choice and Laurent-basis computation are elementary consequences written out in the step.

Step 4 applies lem-sfb-relative-dynamic-subgroups with conjugation by the chosen lambda. Its smooth affine finite-presentation hypotheses hold: smooth gives local finite presentation by def-sbc-smooth-morphisms and affineness gives quasi-compactness and quasi-separatedness. Its P_a equals our P on every algebra, and its stated open immersion is precisely N times P -> G. Step 5 first proves the monomorphism and pullback square explicitly from the torsor and open product; lem-trf-fppf-local-open-subfunctor-descent then gives the represented open and local section. Its sheaf premise and local-lift premise come from step 1. I reread Stacks Tag 02WU, spaces.tex lemma-finding-opens, and Tag 04P2, spaces-descent.tex lemma-fpqc-universal-effective-epimorphisms, including the equalizer assertion, for these descent and gluing inputs.

Step 6 uses only the new density input beyond preceding steps. Its open V is nonempty after an fppf lift, without assuming a rational lift. The rational point a supplied by density yields the explicit lift a s(a^{-1}x). Step 7 uses the covering-base-change node and the new finite-field torsor node. The fibre inherits the right P action, torsor isomorphism and flat/surjective/locally-finite-presentation map. P is smooth and geometrically connected by the definition in the item and affine finite type because closed in affine finite-type G. Lang supplies a point of the fibre, hence the desired lift. These conclusions were checked against the actual cited statements, not their proofs.

I checked B–E on the actual files: no new elementary node, no clause relabelling, no circular use of the item, no unlogged search, no hidden proof in a new statement, and no extra field/perfectness hypothesis. Small cases include G=1, P=G (lambda=0), tori and rank zero, finite fields (no density application), and infinite imperfect fields (density uses reductivity). For the new maximality argument I also checked an equal-rank power map: a non-unimodular power map, including a pth power in characteristic p, has a nonsurjective Laurent-coordinate map and is not a closed immersion, so it cannot invalidate the argument. Connectedness is deliberately retained for finite-field torsors; disconnected finite groups can have nontrivial torsors. Every proof step is below 2000 characters. citations.json covers every cited node with a verbatim statement excerpt.

The two general tools lem-trf-fppf-local-open-subfunctor-descent and lem-a1-algebraic-space-fpqc-sheaf remain declared in split_report.tool_uses: they supply general open descent and morphism gluing absent from the unit's statements. The inherited lattice-torus route notices are advisory; this item's new torus calculation uses the existing integer-homomorphism and tangent nodes directly.

## Unfinished work

The two general inputs remain unsplit as required for a one-level stage-1 split. Required final server dry-run and direct delivery follow this report. No Lean work or compiler/build tool was used.
