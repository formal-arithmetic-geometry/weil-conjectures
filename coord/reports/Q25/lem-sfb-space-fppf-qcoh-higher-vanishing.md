## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-fppf-qcoh-higher-vanishing.json`: item, statement, split; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-scheme-fppf-qcoh-acyclic.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement excerpt for every step/node citation.

## Attachments

None. I searched `lean/WeilConjectures/` for the item tag, fppf, and cohomology/acyclicity combinations. The fppf occurrences are topology infrastructure and Picard/Jacobian constructions, not this module higher-direct-image theorem or the affine fppf acyclicity input. Nothing justifies an ATTACH disposition. No Lean source was written and no compiler was run.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## Findings and changes

The item statement is unchanged. It correctly asks for the second vanishing in Stacks 0DGN(7), for module direct image and the tensor-associated sheaf, not inverse image of the underlying abelian sheaf. The original node had no proof. The split now gives the local argument rather than creating a node which restates the higher-image conclusion. One smaller input remains unsplit: the ordinary affine-scheme fppf cohomology vanishing used inside the proof of 0DEW(7).

The inherited blueprint chain has no machine-resolvable imported ancestor (`blueprint_refs.py ancestor` returns None); I retained its null `from.node` and exact via chain, and added the precise place served. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, paragraph (3). That current proof gives the six-functor compactification route; the old alteration/moduli wording in the inherited chain is provenance, not a claim that the new blueprint states an fppf theorem. This foundational lemma continues the assigned duality/descent prerequisite and does not replace a unit-level route. The item is not the unit's key statement, so no unit file is changed.

## Not duplicates

No existing node had source tag 0DEW when I searched the shared DAG. Searches for 0DGN, 03DW, 03P2, `fppf`, affine acyclicity, and cohomology found the following nearby statements, all opened or inspected by their statement fields:

- `lem-sfb-affine-scheme-fppf-qcoh-acyclic` vs `lem-sfb-space-fppf-qcoh-higher-vanishing`: the new node concerns global cohomology on a scheme big fppf site with affine base; the item concerns a higher direct-image sheaf for an arbitrary algebraic space. Localization, dense comparison, and sheafification remain in the item's proof.
- `lem-sfb-affine-scheme-fppf-qcoh-acyclic` vs `lem-sfb-scheme-big-fppf-quasicoherent-equivalence`: the existing node is underived equivalence and tensor/colimit calculus, not positive cohomology vanishing. It is reused in the new node's statement.
- `lem-sfb-affine-scheme-fppf-qcoh-acyclic` vs `lem-sc-etale-zariski-qcoh-comparison`: the latter compares the small etale and Zariski cohomologies; it does not mention the big fppf cohomology needed here.
- `lem-sfb-affine-scheme-fppf-qcoh-acyclic` vs `lem-sfb-qcoh-cohomology-etale-pullback-naturality`: this likewise states the etale comparison and its naturality, not fppf acyclicity.
- `lem-sfb-affine-scheme-fppf-qcoh-acyclic` vs `lem-sfb-big-fppf-zariski-ringed-comparison`: the existing comparison constructs an underived tensor pullback, including for non-quasi-coherent modules; it does not compute positive derived sections.
- `lem-sfb-affine-scheme-fppf-qcoh-acyclic` vs `lem-sfb-flat-object-fppf-derived-sections`: this latter node uses the item, so citing it would be circular. The new affine scheme input does not use it.

Whole-blueprint searches with `blueprint_refs.py search` for fppf, 03DW, 0DEW, affine/cohomology and quasi-coherent/cohomology returned no statement of the new node. I also searched the current latest blueprint text and the upstream Lean source for fppf cohomology/acyclicity. The same-as lists are empty.

## Mathlib searches

The exact queries and outcomes are in `searches.jsonl` and the node records. Both item and new node were searched by LeanFinder, LeanSearch, Loogle, and grep, with a second semantic phrasing. Every service answered; no unavailable result was converted into absence. The new node's first phrasing found affine limit section theorems, generic quasicoherent data and cohomology-presheaf definitions; the second found faithfully-flat ring/module facts and finite-presentation predicates. These do not give vanishing of derived evaluation. I read Mathlib's `AlgebraicGeometry/Sites/Fpqc.lean` (fppf precoverage and subcanonicity only) and `CategoryTheory/Sites/SheafCohomology/Basic.lean` (definitions of H/cohomologyPresheaf, with slice comparisons still TODO). The item searches found the same presentation predicates, not module fppf/etale acyclicity. No Mathlib leaf was created.

## Review by Q25

I read Stacks `spaces-more-cohomology.tex`, section-fppf-etale-modules and lemma-review-quasi-coherent, tag 0DGN, especially (7) and the complete proof reducing to schemes. I then read `etale-cohomology.tex`, tag 0DEW, its setup, all seven assertions and proof. Its last affine-cover argument explicitly uses positive fppf cohomology vanishing on affine schemes. The new statement is that intermediate assertion with all objects introduced; it has neither a proof nor a proof sketch inside its statement. For its hypotheses I checked the underlying comparison 03DW in `descent.tex`: its topology list includes fppf and its affine-stage proof allows arbitrary quasi-coherent modules, with no Noetherian or finite-generation assumption. In particular the input is not just acyclicity for finite locally free modules. This is substantially stronger than anything obtainable by two or three lines from the existing underived equivalence, so a new lemma is justified.

Step 1 uses `prop-pur-kinjective-resolutions-exist` only for its explicit Grothendieck module-category assertion, then `lem-sp-grothendieck-enough-injectives` for existence of injective resolutions. Neither a definition of enough injectives nor a scheme-only theorem is being used to supply existence on a big ringed site. I read 07A5 and the existing statements. The statement of `lem-sfb-ringed-site-higher-image-cohomology-sheafification` explicitly covers module direct image given by restriction and requires no flat structural ring map; I checked 072W in sites-cohomology.tex. The statement of `lem-pe-ringed-site-derived-evaluation-slice` gives exactly derived module evaluation as abelian cohomology on the slice, without asserting that forgetting modules preserves injectives. I checked its sources 03FD (including the distinction between acyclicity and injectivity of underlying sheaves) and 03F3.

Step 2 uses the atlas clause of `def-trf-algebraic-space`, all needed parts (1), (3), (4) of `lem-sfb-space-fppf-covering-calculus`, and the actual statement of `lem-pc-fppf-dense-sheaf-equivalence`. The latter allows abelian-group values and small sites. I checked the scheme subcategory is fully faithful, each space has an fppf scheme covering, and both directions of the induced-topology condition by scheme-atlas refinement. The slice identification is literal composition of structure maps. This spells out the hypotheses of 0DFV rather than citing a sheaf equivalence without checking the topology.

Step 3 uses that precise equivalence and `lem-weil-pbc-site-sheaves-enough-injectives`, whose statement covers arbitrary small sites. The preservation of injectives and the equality of section complexes are written out, so there is no uncited claim about a special fppf restriction functor being exact or sending injectives to injectives. This is the elementary formal consequence of an additive equivalence: inverse equivalence transports the lifting problem. The terminal object U belongs to both sites. It is abelian injective resolutions that are transported here, consistently with step 1.

Step 4 uses `lem-sfb-space-module-pullback-quasicoherent` for u^*M, then the actual equivalence and arbitrary-morphism pullback comparison in `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`; no unsupported pushforward clause is used. The tensor-normalized composition is exactly what `def-sfb-space-module-tensor-composition` specifies. I checked that the formula on every T over U is the new node's F^a, including restriction along h, rather than only an equality at U. The new node then gives precisely the positive abelian cohomology vanishing on the big scheme fppf site. This avoids confusing small etale, big etale, and big fppf cohomology.

Step 5 uses the atlas definition and the enlarged etale model for arbitrary etale space objects, with `lem-pc-fppf-affine-open-cover` for an arbitrary affine open refinement. Its statement requires no quasi-compactness. The final zero-sheaf argument is proved from the sheafification universal property in `def-weil-presheaf-modules-sheafification`: every map out of P vanishes by separatedness on a cover, hence P^# is initial. It does not assume an unrecorded plus-construction model of sheafification. This argument is elementary after the preceding vanishing.

For edge cases I checked M=0, the identity scheme chart, non-finitely generated modules, infinitely many affine charts, and the empty space. The zero module gives zero coefficient sheaves throughout; the identity chart recovers exactly the affine fppf theorem; infinite charts use sheaf separatedness without a finite subcover; the empty covering over the empty space forces the zero section group. q=0 is deliberately excluded: for U=Spec(k) and F=O_U it equals k. No atlas is assumed affine or quasi-compact before refinement, and no intersections of affine opens are assumed affine.

I checked B through E of delivery-errors against these files: the new statement is self-contained, TeX is singly escaped, its source is the correct tag and label, all notions have statement dependencies, and no source forbidden by the route lock is used. All five proof steps are shorter than 2000 characters; none moves the item into a fresh restatement. I retained every inherited field. The quotes in citations.json were validated as literal substrings of the cited statements. Generic infrastructure from other units is declared in split_report.tool_uses; these tools supply resolutions, slice cohomology, and scheme/etale coefficient comparison, not a substitute proof of the six-functor unit. No mathematical statement dispute was found.

## Unfinished work

The new affine fppf acyclicity node is intentionally statement-only, as required for a one-level split. The item's assembly argument is complete. Delivery checks and push are recorded below once run.
