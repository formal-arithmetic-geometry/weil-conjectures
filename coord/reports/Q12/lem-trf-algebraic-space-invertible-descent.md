# Worker report: lem-trf-algebraic-space-invertible-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-algebraic-space-invertible-descent.json: statement, split; original statement and inherited provenance retained. Eight explicit steps construct the module, local isomorphisms and morphism bijection.
- dag/nodes/sec-trace-formula/lem-trf-scheme-etale-invertible-comparison.json: statement, unsplit; no Mathlib match. One new node, zero Mathlib leaves. It compares ordinary invertible modules on a scheme with line modules on that scheme's small etale site, including morphisms and etale restriction compatibility.
- citations.json: verbatim statement excerpts for every step/node use, including the pullback clause when used.
- report.md and searches.jsonl: this report and actual launcher search records.

## Attachments

None. Searched the project source for the item tag, algebraic-space module descent and Zariski/small-etale invertible comparison. Read WeilConjectures/AlgebraicGeometry/Descent.lean, Sites/EtalePicard.lean and Sites/GmTorsorDescent.lean in the read-only slopmaster2 checkout. Scheme fpqc descent is not the algebraic-space assertion, and the Picard/torsor results do not state the module-category comparison with all module morphisms. Upstream master is reference only, not proof evidence.

## Literature wanted

None. All sources are in literature/stacks-project/.

## Audit findings and changes

The imported statement is sound and was kept verbatim. The source place originally mentioned 05VG for the scheme comparison; 03DX(2) supplies the equivalence itself and 03LC(1) supplies pullback compatibility. The new input records all three, rather than treating the definition of the associated sheaf as a comparison theorem.

Read spaces-descent.tex, 04W8 (proposition-fpqc-descent-quasi-coherent) and 060X (lemma-finite-locally-free-descends). For this etale special case, the compatible-tuples proof of sites.tex 04TR (lemma-glue-sheaves) and sectionwise morphism gluing of 04TQ (lemma-glue-maps) give an explicit construction. Finite local freeness of rank one here is checked directly with frames, rather than introducing a node restating the descent clause. The algebraic-space etale site need not have F itself as a terminal scheme; accordingly we do not apply lem-pe-set-sheaf-cover-descent to a nonexistent terminal object. Products and an equalizer are instead formed on the actual small site using lem-weil-pbc-site-sheaf-sets-limits-sectionwise, whose statement was read in full.

The new comparison is a different-site equivalence on one scheme, not another formulation of descent from an atlas of an algebraic space. No new node merely restates the effectivity, locality or full-faithfulness clauses of the item. Coordinatewise module laws, the graph inverse, cocycle calculations and morphism amalgamation are written in the item's steps. Each step is below 2000 characters; none hides an unproved comparison.

Blueprint searches were run for the item, the tags 04W8, 03DX and 05VG, and the notions algebraic-space invertible descent, quasi-coherent modules, and invertible etale. No blueprint node states either item or new comparison. The inherited ancestor is lem-trf-local-term-locality; its descent input is reached through the unchanged polarized-scheme and log-descent chain. The new node prepends the item to that chain. This is a non-key child of sk-i-curve-zero; no unit realization is edited.

## Not duplicates

lem-trf-scheme-etale-invertible-comparison vs lem-trf-algebraic-space-invertible-descent: the new node compares two sites of one scheme, including all linear maps; the item constructs a module on an algebraic space from an atlas and glues compatible maps.
lem-trf-scheme-etale-invertible-comparison vs lem-pc-fpqc-descent: fpqc descent on schemes relates modules to descent data for a cover, not to all line modules on the small etale site with its structure sheaf.
lem-trf-scheme-etale-invertible-comparison vs def-sc-etale-qcoherent-module: that definition specifies the associated additive sheaf and its restrictions; it asserts neither categorical full faithfulness nor essential surjectivity for etale line modules.
lem-trf-scheme-etale-invertible-comparison vs lem-sc-etale-qcoherent-descent: that node proves the associated presheaf is a sheaf, not that every etale line module arises and every etale module map is ordinary.
lem-trf-scheme-etale-invertible-comparison vs lem-sc-etale-zariski-qcoh-comparison: that theorem compares cohomology groups; it does not state an equivalence of module categories or its pullback compatibility.
lem-trf-scheme-etale-invertible-comparison vs lem-trf-algebraic-space-ample-local: the latter uses scheme-site interpretation to descend relative ampleness and scheme representability; it does not prove the interpretation theorem.

The source-field search of the entire DAG for 03DX, 03LC and 05VG found only the item (05VG). Broader searches also inspected the associated-sheaf, cohomology-comparison and scheme-descent nodes above; none states this new theorem.

## Mathlib search review

Every recorded query was actually run with the launcher search command. The comparison has two different natural-language phrasings in LeanFinder and LeanSearch, two Loogle patterns, and source greps in AlgebraicGeometry and Algebra. The genuine log records are embedded as results, with the exact tool and query. The item retains Q81's inherited searches and has additional logged searches with a second phrasing.

Read the strongest hits: Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:57-70 proves full faithfulness of forgetting to presheaves on the same Zariski site; Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean:135-156 compares the affine etale site with the whole etale site and gives Grothendieck abelian categories; Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:30-95 supplies module presentations. None gives the ordinary/small-etale module equivalence. The two natural-language result lists also return ring-module rank/free-locus statements, not a sheaf comparison. Loogle's generic module equivalences concern sections, free modules or colimits, not this theorem. No unavailable service was reported as a negative match.

## Review by Q12

I read the item against 04W8 and 060X in spaces-descent.tex. The base is any scheme, the algebraic space has representable diagonal, and the cover is jointly surjective etale by schemes. There is no quasi-compactness, separatedness or noetherian hypothesis. The transition maps are module isomorphisms on the actual fibre products over F, not intersections or products over S. Their orientation is from the j-module to the i-module. The tuple equations and graph inverse use this same orientation. The diagonal assumption is used only after pulling a_aa back along the diagonal, never to replace it by identity on the whole self-overlap.

For the new node I read descent.tex 03DX (proposition-equivalence-quasi-coherent), specifically its small-etale clause (2), 05VG (lemma-equivalence-quasi-coherent-properties), and 03LC (proposition-equivalence-quasi-coherent-functorial), clause (1). A line module is locally free with one generator, hence locally has a finite free presentation and is quasi-coherent on that site. The categorical equivalence restricts to finite locally free modules by 05VG; the rank-one condition is unchanged by field extension at a point of an etale covering, so ordinary and etale rank one agree. Conversely an ordinary local frame gives an etale local frame. This explains the restricted equivalence without claiming that arbitrary locally free modules are covered by 05VG's excluded general locally-free case. All module morphisms, not just isomorphisms, are included; pullback compatibility is explicitly part of the statement. The node is self-contained, cites each notion, has no proof or proof sketch, and leaves the proof for the next worker.

Step 1 uses the new comparison's equivalence and its natural etale pullback clause, def-trf-algebraic-space's actual site and structure sheaf, and def-weil-size-convention's small skeleton. The cited comparison really asserts pullback compatibility; neither a sheaf-condition lemma nor cohomology comparison is substituted for it. Identity/composition compatibility preserves the cocycle.

Step 2 uses def-trf-algebraic-space's representable diagonal and base-change meaning of etale maps to make every W_i and W_ij a scheme test object. The site/sheaf axioms of def-weil-pbc-sites-and-cohomology say exactly that coverings pull back and sections satisfy the stated equalizer. The double intersections are identified by the fibre-product universal property, so H_i and K_ij satisfy that same equalizer. There is no unproved assertion that a forgetful presheaf is a sheaf.

Step 3 cites the precise statement (1) of lem-weil-pbc-site-sheaf-sets-limits-sectionwise. Its small-diagram hypothesis is checked for discrete I, discrete I times I and the finite equalizer diagram, within the chosen universe. It supplies the sheaf property and section formula actually used, not merely abstract limit existence.

Step 4 uses def-weil-sheaf-of-modules-category's sectionwise module and semilinear-restriction definition. Addition, negatives and scalar multiplication preserve each compatibility equation by linearity of a_ij. Every law follows coordinatewise. This is a direct verification, not a citation of the definition as a substitute for a module descent theorem.

Steps 5 and 6 use no new theorem. On an etale test W over V_a the two explicit graph formulas are inverse: one composite uses the diagonal identity; the other is exactly the (i,a) tuple equation pulled back along the graph. The triple cocycle checks the inverse tuple condition. The equation h_a d'_a=d_a h checks naturality; the graph into W_ab checks the claimed transitions. These are elementary equalities with all maps and directions specified.

Step 7 uses def-sc-invertible-module for ordinary Zariski frames, the new comparison for their etale interpretation and structure-module identification, and the composition-of-coverings axiom for the refinement of W_a over W. The line condition is precisely the local condition in def-trf-algebraic-space. It does not assume that an etale-locally trivial ordinary module is automatically Zariski trivial; the comparison theorem supplies exactly the ordinary interpretation required. Its faithfulness returns the original transition maps.

Step 8 uses the comparison's Hom bijection and pullback compatibility to interpret the input maps, then the sheaf equalizer axiom for N to amalgamate their values on W_i. Naturality, additivity and scalar linearity are checked by uniqueness on that covering. Restricting along a graph proves recovery of g_i, and separatedness proves uniqueness, so both directions of the Hom bijection are proved for arbitrary M and N, not merely the constructed module.

I tested the identity cover, a repeated cover member with a nontrivial self-overlap, the empty scheme/empty cover, and nonaffine overlaps. With an identity cover graph evaluation recovers the original module. Repeated members require the full cocycle and do not permit setting a_aa to identity off its diagonal. If F is empty, the empty-cover sheaf condition gives one section over the empty object, the coordinatewise module is zero, and it equals the structure module there; the Hom sets and matching families are singletons. No affine, finite-cover or connectedness assumption occurs. The new comparison also holds for the empty scheme and does not claim rank is read at a point when no points exist.

The main corrections during self-review were avoiding a generic covering-of-a-terminal-object theorem on F_et, avoiding duplicate nodes for the item's own clauses, and adding the actual 03DX/03LC comparison input in place of an appeal to a definition. I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the written nodes and sources. Only the generic limits lemma is an off-unit statement tool; split_report.tool_uses declares that use without editing maintainer-owned tool_uses. The natural-language proof source is the compatible-tuples argument of 04TR and 04TQ, with the algebraic-space test-object construction made explicit. No SGA source, Lean writing, compiler or library build is used.

## Unfinished work

The new comparison is deliberately unsplit as required for a newly introduced non-Mathlib input. The item's stage-1 split is complete; server dry run and delivery are performed next.
