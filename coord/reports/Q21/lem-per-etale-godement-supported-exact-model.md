# Q21 stage-1 delivery: lem-per-etale-godement-supported-exact-model

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-godement-supported-exact-model.json`: item split into eleven proof steps; statement and statement dependencies preserved.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-point-product-acyclic.json`: one new statement-only unsplit lemma; Mathlib searches found only partial ingredients, no exact match.
- `citations.json`: verbatim cited statements for every step/node pair.

## Attachments

None. Searched the exact blueprint tag and Godement/skyscraper concepts in the entire project source. The closed topological Cech Godement exactness and germ-unit lemma cover only smaller ingredients, not this etale supported model and its coefficient/tensor clauses.

## WANTED

None. I read ILO Expose XVI Proposition 3.3.2 on printed p.245 (PDF p.251), which calls the Godement properties elementary and uses them to choose Gysin cocycles and coefficient-cone triangles. All Stacks sources used below are present.

## Problems found and corrected

The imported statement is retained exactly. Its source only sketches the elementary Godement input; the proof is therefore honestly marked agent-written. The existing Zariski/ringed-space Godement nodes cannot be cited as etale theorems. I did not infer acyclicity merely from surjectivity on Zariski opens, nor assume an infinite product commutes with arbitrary inverse image. The supported product identification is established on X through its actual kernel; closed support and the coefficient action then identify its sheaf on Z. Negative degrees are treated by a nonnegative injective complex and the K-injective Hom bijection, not by an uncited orthogonality claim. During writing I corrected doubled TeX escapes in the new text before delivery.

## Unfinished work

Nothing in the assigned split is left unfinished. The new node is deliberately unsplit, as required for one-level stage-1 work. It has an independent future proof: sheaf descent and the point adjunction are coordinatewise; exact stalks imply the right adjoint sends injective tuples to injectives; coordinatewise exact products applied to tuple injective resolutions prove evaluation acyclicity. This proof sketch is recorded here only, not in that statement-only node.

## Blueprint and search audit

Read the chapter sec-deligne-laumon-a1 and unit sk-p-dl-a1-perverse, and retained the ancestor route through lem-per-artin-gabber-affine-curve, proof Step 3, via the finite-coefficient regular-pair argument. This item is not the unit key statement, so no unit file is changed. The local technical proof realizes the ILO XVI 3.3.2 Godement input recorded in the ancestor place, without introducing a new purity route. No SGA source is used.

Whole-DAG and blueprint searches included Godement, skyscraper, point product, coinduced, evaluation acyclic, exact stalks, acyclic resolutions and the Stacks tags 00Y8, 04EQ, 05V8 and 01DU. The nearest-ancestor command returned lem-per-artin-gabber-affine-curve. Blueprint same_as is empty: none states this item or the new family-product lemma. Existing topological Godement/flasque nodes require a different site. Existing module-skyscraper-stalk-adjunction is for Zariski O_X-modules at topological points, not geometric etale points. Mathlib searches were made only through msearch.py and recorded from searches.jsonl after reading the hits. The relevant source Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean was read at the product definition and at lines 219--238; it gives the point adjunction, not the family-resolution/evaluation conclusion. Both semantic phrasings returned topological skyscraper or cohomology definitions, not the new theorem.

## Not duplicates

lem-per-etale-point-product-acyclic vs lem-trf-topos-complement-module-stalks: describes open/closed module recollement and exact point inverse images; it gives no product-of-point direct-image or evaluation-acyclic statement.
lem-per-etale-point-product-acyclic vs lem-trf-site-point-fibre: identifies the stalk with a neighbourhood colimit and proves its exactness; it says nothing about evaluation acyclicity of point products.
lem-per-etale-point-product-acyclic vs lem-trf-point-family-conservative: is a criterion for a family of set-valued stalks to reflect isomorphisms; the new lemma does not assume conservativity and concerns module point-product right adjoints.
lem-per-etale-point-product-acyclic vs lem-weil-pbc-sheafification-geometric-stalk: concerns abelian presheaf sheafification commuting with stalks, not products or their higher evaluation.
lem-per-etale-point-product-acyclic vs lem-weil-pbc-module-sheaves-enough-injectives: only gives embeddings of module sheaves into some injective sheaves; it does not identify injectives built from a family of modules or prove their evaluation acyclicity.
lem-per-etale-point-product-acyclic vs lem-weil-pbc-sets-sheafification-geometric-stalk: concerns set-valued sheafification and stalks, not module point-products or acyclicity.
lem-per-etale-point-product-acyclic vs lem-fix-geometric-stalk-topos-point: gives the single-point adjunction for sets and finite-limit preservation; the new statement additionally concerns arbitrary module families, sectionwise exactness, injective family resolutions and higher evaluation vanishing.
lem-per-etale-point-product-acyclic vs lem-cbc-proetale-sheafification-geometric-stalk: is the pro-etale abelian sheafification/stalk comparison; the new lemma is about ordinary etale module products and their evaluation.
lem-per-etale-point-product-acyclic vs lem-pur-module-restriction-kernel-comparison: compares module and abelian derived kernels of restriction on a site; it does not supply any geometric-point product resolution.
lem-per-etale-point-product-acyclic vs lem-weil-proetale-constant-sheaf-stalk: computes stalks of constant pro-etale sheaves; it does not treat etale point direct images or their products.

The new point-product lemma does not restate an item clause: it assumes no closed immersion, has no Godement iterate, differential, quasi-isomorphism, exceptional inverse image, coefficient change or line tensor. The item constructs and analyzes all of these in its own steps.

## Review by Q21

I read delivery-errors B through E in full and checked the actual node files against them. For the item I read ILO XVI 3.3.2, printed p.245. For the new lemma I read sites.tex 00Y8 (point-pushforward-sheaf), sites-modules.tex 04EQ (stalk-exact-modules), 05V8 (skyscraper-modules-exact), and the point/skyscraper discussion; the module injective existence source is 01DU, the one-point case giving injective module resolutions. I also read simplicial.tex 08NC/08ND, derived.tex 015E and 06XR, and etale-cohomology.tex 09XQ with its preceding support definition. These are the sources, not merely their titles.

For step 1 the new lemma says exactly that A is exact, B is its right adjoint and the unit is the germ map. The standard-adjunction node is stated for ordinary categories without abelian hypotheses, so it applies to opposite categories; the alternating-square cancellation is written out. For step 2 the extra codegeneracy is the counit at AT^qF, and the two triangle/naturality identities give dh+hd=1, including augmented degree -1. The given conservative family, not an unstated completeness hypothesis on all geometric points, detects vanishing.

For step 3 I read the entire support-adjunction statement. It supplies the isomorphism between the kernel and i_*i^!_0, not just the definition. The new product formula shows exactly which coordinates are discarded. A geometric point over Z factors uniquely through the closed immersion, so the surviving point family is correctly a family on Z. The R-linearity is checked coordinatewise. For step 4 the new node supplies the specific tuple injective resolution, its termwise injectivity and exactness on every evaluation, all needed by the argument; I do not use the acyclicity of an arbitrary flasque etale sheaf. Applying the established supported-coordinate formula to this actual resolution gives i^!_0- and v-acyclicity.

For step 5 I read the module closed-sheaf internal-adjunction node: it explicitly gives exact i_*, the module adjunction and preservation of injectives. Enough injectives holds for arbitrary rings and both schemes by the cited node. The bounded-below derived-adjunction statement supplies the specific counit normalization; the acyclicity theorem explicitly includes bounded-below complexes, and its hypotheses are verified by steps 2 and 4. The fixed definition of i^! is the right adjoint with this same counit.

For step 6 I checked the Ext-resolution node: its first argument is an arbitrary object of the abelian category, so it applies to i_*R_Z, and its second argument here is genuinely the sheaf F. Its nonnegative-degree restriction is respected. For negative m the additional cited injective-existence, bounded-below K-injective and derived-Hom nodes justify computation against i^!_0I; there is no degree-zero map because I^m=0. Step 7 uses the Ext node's explicit cocycle normalization and the canonical acyclic comparison, and checks the boundary/homotopy relation. It does not assert that arbitrary maps into a noninjective complex compute derived Hom without an acyclicity comparison.

For step 8 I verified stalk exactness on underlying abelian sheaves, which immediately gives exactness of module stalks; the new point-product statement is exact sectionwise, so finite-coefficient exactness does not require injective stalks. For step 9 all operations are the identical operations on underlying elements after scalar restriction. The two model counits are the same supported inclusion, so the derived comparison respects the specified counit; no claim that restriction preserves injectives is made. For steps 10 and 11 I checked the tensor map on pure tensors, its slice indexing, and its compatibility with germ insertion. On an etale trivialization of L the maps are identities. Support kernels and i_* therefore commute with this line tensor locally, and the final comparison is identified by its actual closed transpose, using the derived counit formula rather than an unnamed projection formula.

Small cases checked: X empty, the family P empty on the empty site, a redundant family with repeated points, R the zero ring, the zero sheaf, Z empty and Z=X, m<0, split coefficient sequences, a field spectrum, and a trivial line. The new lemma also permits a nonconservative or empty family on nonempty X: it asserts acyclicity and adjunction, not that an augmentation resolves every sheaf. A nontrivial etale line is handled on its trivializing cover without choosing a global basis. Nothing assumes regularity, invertibility of torsion, finite stalks or constructibility.

Each citation was checked against its statement; citations.json copies that statement verbatim for its step/node pair. All non-elementary inputs are cited nodes. The two/three-line coordinate, exactness, homotopy and adjunction computations remain item steps rather than artificial new nodes. The new lemma has no proof or proof dependencies. No step exceeds 2000 characters, and none hides a comparison behind the words standard, transport or obvious. Off-unit proof tools are declared in split_report.tool_uses with their purpose; they are foundational tools, not replacement unit routes.
