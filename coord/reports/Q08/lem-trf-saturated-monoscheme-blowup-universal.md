# Q08 stage-1 delivery: lem-trf-saturated-monoscheme-blowup-universal

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-saturated-monoscheme-blowup-universal.json`: item split into seven explicit steps; statement unchanged; no Mathlib match.
- Removed the proposed `dag/nodes/sec-trace-formula/lem-trf-affine-monoscheme-hom-universal.json` from the delivery: Q06 has now landed this input from its product-charts item. Steps 4 and 5 cite that existing node without modifying it.
- `citations.json`: one verbatim statement quotation for every node citation in every proof step. Full statements are quoted so the distinct uses of definitions and of localization compatibility can be read directly.

New nodes: 0. Mathlib leaves: 0. No Lean written or compiled.

## Attachments

None. Searched the exact item id and monoscheme/monoidal-space/saturated-blowup notions in `lean/WeilConjectures/`: no declaration states the item or the reused affine input. The ordinary scheme blowup universal property in `WeilConjectures/Blowup/BlowupUniversal.lean` concerns ring schemes, not monoschemes. The read-only `lean/Sheaf/AlgebraicGeometry/MonoschemeToricRealization.lean` supplies definitions and the prescribed chart property, not this universal-property theorem.

## WANTED

None. The ILO PDF is available and was read directly through pdftotext. Neither the item nor the affine input is a theorem about ring schemes, so assigning them a scheme-theoretic Stacks tag would be incorrect. Sources are the exact ILO lemma and paragraph numbers, with printed pages.

## Corrections and route

The imported item has no proof and needs no statement correction. Its route is the historical monoidal-resolution branch of `lem-trf-local-term-locality`, via the already split tower-comparison/coherence item. Read `GOAL.md`, the chapter and `sk-i-curve-zero` unit records, and the latest blueprint snapshot, main `7284bb09daf97437d544c51882b325f9c52cd345`. The latest locality proof uses the contracting-correspondence route and no longer contains the historical alteration argument. The item's inherited blueprint ancestry is retained and described honestly as historical; this delivery changes neither the unit nor that new route.

A tempting but invalid shortcut is to cite `lem-trf-affine-fan-hom-universal`: it requires a sharp source sheaf and a fine sharp target monoid. Those hypotheses are unavailable here. The returned delivery proposed the unsharpened version from ILO VIII Lemma 3.1.8(i), rather than its sharp variant (ii). That version now exists in the DAG from Q06 and is reused here. Likewise, generators in an unsharpened monoid differ by a unit, not necessarily by zero. The construction and uniqueness arguments retain those units.

During self-review I expanded the base-open restriction argument in step 6 and explicitly cited saturation/localization compatibility there. I also checked the recorded search query/result pairings against their captured outputs after parallel searches completed, and corrected the item append to use the explicit query order rather than completion order. No search result was invented.

## Repair of the returned delivery

The first required dry run failed against current base `8fd0f2768043809973c82cc00babe4644065f61d`: the proposed affine Hom node already exists and cannot be modified by this delivery. I compared the retained item with the current live item and rebased the split fields onto that current record. The statement, statement dependencies, ancestry and other inherited fields agree; the retained seven-step proof and search records are preserved. I also compared all 18 retained citation quotations with current statements. The three other cited statements are unchanged; the two affine Hom quotations needed replacement.

The return asks to resolve the new-node collision by renaming. Reading the landed node shows that creating the same theorem under another name would duplicate an existing input. I therefore removed the proposed new node and cite the existing `lem-trf-affine-monoscheme-hom-universal` without changing its file. Its statement gives exactly the unsharpened Hom bijection, injectivity, existence, and naturality used in steps 4 and 5. The extra point and localization formulas in our old proposal are not used by these steps, so no replacement node or new search is required. All 18 quotations have been regenerated verbatim from the current cited statements. The original searches and captured results are retained unchanged.

## Not duplicates

Removed Q08 proposal vs existing lem-trf-affine-monoscheme-hom-universal (Q06): both give the same unsharpened spectrum/global-sections bijection and naturality; the proposal additionally displayed its point/basic-open formulas. Those formulas are not used by the item, so the proposal is removed and the landed node is reused. No renamed duplicate is delivered. The following comparisons from the original review remain useful distinctions between the reused unsharpened input and the sharp inputs.

lem-trf-affine-monoscheme-hom-universal vs lem-trf-affine-fan-hom-universal: the existing theorem assumes sharp stalks and a fine sharp monoid and maps to the sharpened monoid spectrum; the unsharpened theorem permits units in both source and target and maps to the unsharpened spectrum. It cannot be specialized from the existing theorem.

lem-trf-affine-monoscheme-hom-universal vs lem-trf-affine-fan-canonical-section-rigidity: the existing statement supplies uniqueness for sharp fan maps and formulas killing units; the affine Hom statement supplies existence and uniqueness for arbitrary monoidal spaces with the unsharpened structure sheaf.

lem-trf-affine-monoscheme-hom-universal vs lem-trf-sharp-section-basic-chart-data: the existing statement is the sharp, zero-germ basic-open construction; it neither gives unsharpened section maps nor the unsharpened Hom bijection.

lem-trf-affine-monoscheme-hom-universal vs lem-trf-affine-fan-basic-map-local-lift: the existing statement glues an already specified sharp basic-open map and assumes sharp stalks. The unsharpened theorem takes an arbitrary monoid homomorphism and represents it with its units retained.

lem-trf-affine-monoscheme-hom-universal vs lem-trf-saturated-monoscheme-blowup-universal: the unsharpened theorem has no ideal, blowup, saturation or principalization hypothesis; it is an independent affine-spectrum representation theorem used after the fraction map has been constructed, not a clause of the item moved into a new node.

Also searched the whole DAG by monoid spectrum, monoscheme, local monoidal maps, unsharpened spectrum, ILO 3.1.8(i), and associated names, and ran `tools/blueprint_refs.py search` for monoscheme, monoid spectrum, saturation and local morphisms. No blueprint node states the affine input; the current created DAG node now does and is reused. Existing fine saturation and its localization formula are reused. No Stacks-tag duplicate pairs occur because these monoidal-space statements have no Stacks tags.

## Mathlib searches

The logged msearch commands and captured outputs are retained. The item has two semantic phrasings, LeanSearch, Loogle and Mathlib grep, as did the original proposed affine Hom node. Those original-node search outputs remain in the sandbox even though that proposal is now removed. Read the returned signatures: Γ-Spec adjunctions use commutative rings and locally ringed spaces; normalization and Proj use schemes; Submonoid.LocalizationMap and OreLocalization only lift homomorphisms of monoids after localization. None supplies the monoid-spectrum topological/sheaf morphism. The Loogle pattern mentioning MonoidalSpace reports an unknown identifier with no hits; it is recorded as that response, not treated as a theorem match. The grep returns local-ring and local-homomorphism declarations, not monoschemes. There are no Mathlib leaves and no unavailable services in the recorded delivery searches.

## Review by Q08

For this repair I reread all four current cited statements, ILO VIII 3.1.8(i) and 3.1.17--3.1.22, and the current blueprint locality statement and proof in `literature/blueprint/latest/`. The only changed cited statement is the landed affine Hom input. Its removal of our unused point/basic-open formulas does not affect any proof step: step 4 uses its bijection and naturality, and step 5 only injectivity for maps into a fine chart. All fineness and arbitrary-source hypotheses match. I checked the remaining three statements against their retained quotations and reread them for every use below. This is a substantive duplicate-removal and citation repair, with a current-base item record; it is not an unchanged re-push. The detailed earlier source and seven-step review below remains valid, with the affine input now reused.

I read ILO Exposé VIII 3.1.1--3.1.9 (printed pp.98--99) and 3.1.17--3.1.22 (printed p.101). For the affine Hom node I checked Lemma 3.1.8(i) and its proof, including its point formula as the inverse image of nonunits. The statement uses fine P so that the already defined spectrum/sheaf conventions apply; it places no sharpness or integrality condition on the source sheaf. The basic-open formula in the removed proposal used an actual unit inverse, with no illicit subtraction in a monoid; the retained split does not require that extra displayed formula in the reused statement. Its eventual proof is the source's construction: the nonunit inverse image is prime, the unit-germ locus is open, local inverses glue, the localization homomorphisms agree on basic overlaps, and locality determines both point and sheaf maps. This argument belongs here in the report; the unsplit node itself has no proof or proof dependencies.

I opened every cited node statement, specifically `def-trf-monoscheme-toric-realization`, `def-trf-fine-fan-blowup`, and `lem-trf-fine-monoid-finite-saturation`, and compared each assertion taken from them with its text. The affine Hom theorem is quoted verbatim from the current existing node. The seven steps have the following uses and hypothesis checks:

1. The monoscheme definition supplies unsharpened saturated charts and their gluing. The fine-fan definition supplies the underlying monoid, spectrum, ideal and saturation conventions, which are shared by monoschemes. Finite saturation states exactly that a finitely generated integral Q has fine saturated saturation and that saturation commutes with localization. Each Q_a lies inside P^gp and is generated by the generators of P and the finite differences b-a, hence meets those hypotheses. Its localization equality makes the actual blowup stalks saturated. I wrote out why a coherent ideal on an affine monoid spectrum has finitely many global generators, and why nonemptiness on each connected component rules out an empty chart ideal. Principalization itself is the elementary identity b=a+(b-a), not an additional lemma.

2. The two definitions give the sheaf, integral-stalk and saturated-stalk meanings. Stalkwise cancellation passes to sections by the sheaf axiom. I wrote the saturation argument for a difference s-t in the group completion of sections, including the equality after shrinking and the cancellation that makes the local representatives agree. This avoids assuming a false unconditional identification between group completion of sections and sections of the group-completion sheaf.

3. Only ideal generation, cancellation, germs and finiteness from the definitions are used. The generator t belongs to the pulled-back ideal, so t=h(a)+u for a chart generator a; since h(a) also belongs to t+M there is v with h(a)=t+v. Their sum is zero by cancellation, so u is a unit, rather than zero. There are only finitely many b, permitting a single neighborhood for all their divisibilities. This proves the open generator loci needed later.

4. The definitions supply Q_a and C_a, and finite saturation guarantees C_a is fine as required by the affine Hom theorem. No universal blowup property is assumed. The group-completion formula is defined on p-q, and saturation of the section monoid was already proved in step 2. The same ambient group shows uniqueness of this homomorphism. Only then is the unsharpened theorem applied to turn the homomorphism into a local point-and-sheaf morphism; its naturality identifies the composite with f.

5. The chart gluing and local-map definitions say exactly what is used. The elementary cancellation argument identifies the generator locus inside an e-chart with D(a-e), the prescribed overlap. Locality is essential: a unit image of a-e in the source forces a-e to be a unit in the target stalk. The affine Hom bijection then identifies the entire morphisms, not only their group maps. This is a full uniqueness argument and not a citation to the item being proved.

6. The definitions specify gluing by agreeing section tuples on open overlaps. For basic base restriction, the finite-saturation lemma gives (Q_a-S)^sat=C_a-S; I added this citation explicitly so compatibility with base restriction is not hidden. After that, local uniqueness proves agreement on source overlaps. I wrote how continuous maps and section homomorphisms glue, and why locality remains true on stalks. Global uniqueness follows on the same open cover. No scheme gluing result is misapplied to monoidal spaces.

7. Only the definition of local composition and the proved uniqueness are used. A restricted lift and a precomposed lift have the correct composite with pi, so they equal the constructed lifts. The local uniqueness argument never needed the finite-cover hypothesis on the restricted open. Empty sources have unique maps. No hidden naturality theorem is assumed.

Edge cases checked: P={0}; P a group (the monoid spectrum is one point and every nonempty ideal is the whole monoid); unit ideal on a nonsaturated P, for which the blowup is saturation rather than necessarily the identity; principal ideals, whose charts give P^sat; E={a}; redundant generators; nonzero units so that generators need only be associates; empty Y and empty M; disconnected objects with a nonempty ideal on every component. The affine Hom theorem also works for empty T, whose global section monoid is terminal. For a nontrivial group P it retains arbitrary maps into the unit sections, confirming that its unsharpened content cannot be recovered by forgetting units.

Against delivery-errors B--E: every object and convention is introduced, the reused affine Hom statement has no proof sketch or proof dependencies, source numbers and printed pages were checked against the PDF, and single-backslash TeX is encoded by JSON normally. No unsupported tag is used. Each non-elementary operation is either a cited statement or is written out as cancellation, the definition of group completion, or the sheaf axiom. All seven steps are below 2000 characters; none packages a separate standard lemma or comparison as an unproved phrase. There is no new node restating a clause of the item, and no dependency on the existing fan-blowup lift or tower comparison that could introduce a cycle. The statement and its hypotheses were preserved exactly. The previous delivery passed server review_split; the required new dry run will check this repaired split against the current DAG.

## Unfinished work

None at this split level. The affine Hom input is an existing statement-only DAG node and remains available for its own stage-1 split; this delivery creates no nodes.
