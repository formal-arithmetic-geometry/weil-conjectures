## Files written

- dag/nodes/sec-trace-formula/lem-trf-fine-monoid-local-smooth-charts.json: item, statement, split; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-monoid-spectrum-hom-universal.json: one new statement-only node, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every dependency at every item step.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and monoid spectra, monoschemes, Kato fans, smooth monoid maps and related terms. The returned smooth localizations concern rings, and the spectrum adjunctions concern locally ringed spaces; none states this item. The Sheaf interfaces are not claimed as finished project proofs.

## WANTED

None. The ILO source is present. No Stacks tag states the monoidal-space spectrum universal property or this smoothness notion. Source citations therefore specify ILO VIII, not an invented Stacks tag. No SGA source is used.

## Errors and changes

The imported statement is unchanged. The item had no proof. Its existing searches have been retained and additional actual searches are recorded. The added node is Lemma 3.1.8(i), needed to identify maps of ordinary monoid spectra, rather than the sharp-only 3.1.8(ii) already present in the DAG. I do not use ILO's assertion that arbitrary monoscheme smoothness is equivalent to smoothness after sharpening: the proof here only sharpens a given product decomposition. In particular there is no appeal to the torsion-free unit-splitting node, whose extra hypotheses would be inappropriate here.

The current latest blueprint ancestor lem-trf-local-term-locality has been read in literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/. Its proof now uses contracting correspondences. The item belongs to its historical monoidal-resolution branch already recorded in blueprint.from, and this delivery keeps that provenance and does not change the ancestor, chapter or unit. Chapter sec-trace-formula and unit sk-i-curve-zero were read, as were the three levels in SETUP.md.

## Not duplicates

lem-trf-monoid-spectrum-hom-universal vs lem-trf-affine-fan-hom-universal: the new node is the unsharpened spectrum with ordinary monoid sheaf and arbitrary source stalks (ILO VIII 3.1.8(i)); the existing node assumes sharp P and sharp source stalks and targets a sharpened spectrum (3.1.8(ii)). It cannot supply the ordinary spectrum universal property when units occur, for example for P=Z.

lem-trf-monoid-spectrum-hom-universal vs lem-trf-affine-fan-basic-map-local-lift: the existing lemma glues an already supplied compatible family of sharpened localization maps and assumes sharp source stalks; the new node is the unrestricted ordinary-spectrum representing property, with its inverse and naturality.

lem-trf-monoid-spectrum-hom-universal vs lem-trf-affine-fan-canonical-section-rigidity: that lemma is uniqueness only for maps to a sharp spectrum; the new node supplies existence, inverse, and naturality for the ordinary structure sheaf.

lem-trf-monoid-spectrum-hom-universal vs lem-trf-strict-fan-chart-local-comparison: the existing statement compares strict log-scheme fan charts; it does not state the spectrum representing property on arbitrary monoid sheaves.

Other overlapping facts are reused. lem-trf-fine-fan-point-localization is cited for the sharp neighborhood clause. lem-trf-monoid-prime-minimal-neighborhood is cited for its explicit face and denominator formula. lem-trf-monoscheme-smooth-local-charts was read but not cited: it contains the forward monoscheme clause and a further ring realization conclusion, not the localization and converse/fan clauses needed here; using the existing forward clause as a black box would conceal the argument this item is supposed to carry.

Before creating the new node I searched the entire DAG for 3.1.8, unsharpened universal properties, monoid spectra and global sections, and ran blueprint_refs.py search for monoscheme, fine monoid and monoid spectrum (all returned no blueprint matches). blueprint_refs.py ancestor identifies lem-trf-local-term-locality. Lean source searches gave no matching declaration. Mathlib searches through msearch.py used leanfinder twice, leansearch, loogle and grep. All returned types were read: GammaSpec adjunctions have CommRingCat and locally ringed spaces; the strongest candidate source Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean:333 explicitly has that domain. It is not a generalization to monoids. No search is recorded as run without its logged invocation. Earlier item's records are preserved as instructed.

## Review by Q53

I read the actual ILO PDF via its extracted text, Expose VIII 3.1.1--3.1.16, printed pp.98--100: 3.1.2 for denominators, 3.1.4 and 3.1.10(ii) for neighborhoods, 3.1.8(i) for the one new node, 3.1.14 with its proof for the localization argument, and 3.1.15--3.1.16 for the smooth-chart assertions. For the fan details the source says they are left to the reader, so step 5 writes the quotient-by-units computation and step 6 invokes the exact existing sharp universal-property and localization-section statements. No additional torsion assumption was inserted.

I opened and read the statement of every cited node, including both definition nodes, prime-minimal-neighborhood, fine-fan-point-localization, affine-fan-hom-universal and affine-fan-localization-sections. Step 1 uses the localization, fine and unit definitions in def-trf-fine-fan-blowup; it proves the finite-denominator reduction using a finite generating list and inverse formulas. Step 2 uses that same localness definition, not a definition cited for a hidden exactness theorem: it explicitly proves that locality makes p a unit and computes the localized free factor by v+kn. It supplies the new ranks r-t and s+t. Steps 1, 2 and 5 are marked elementary because their entire arguments are direct submonoid or coordinate calculations with inverses and quotients, with no external structural theorem invoked.

Step 3 uses the exact smallest-open and P_b=P-F conclusions of prime-minimal-neighborhood, the ordinary structure-sheaf prescription of the two definitions, and the new ordinary-spectrum bijection for the two inverse maps. The prime's face is the complement of the actual chart prime. The section-to-stalk map is an isomorphism because this is the smallest neighborhood, not because an arbitrary affine neighborhood has that property. The universal property identifies both continuous maps and sheaf maps, including the inverse comparison, and makes the identification independent of the chosen chart.

Step 4 uses the smooth-stalk definition from monoscheme-toric-realization and the new node's ordinary-spectrum bijection and explicit stalk formula. It restricts by continuity on generalizations and then uses section-to-stalk identifications; it does not silently replace a sheaf map by a stalk map. For the converse, the source and target localizations are at an actual point and its image, so the localness hypothesis needed in step 2 holds. It proves the converse at every point of every chart; the neighborhoods Y_y cover by construction.

Step 5 computes the units and their quotient in a displayed direct product. It does not use an arbitrary sharpening splitting (which can fail without stronger hypotheses). Step 6 uses exactly the statements of fine-fan-point-localization (smallest neighborhood and section/stalk isomorphism), affine-fan-hom-universal (maps determined by canonical sections and natural bijection), and affine-fan-localization-sections (stalks and restrictions are sharpened localizations). These statements actually supply all the identifications used; a purely fully faithful or definition-only citation would not have sufficed. Ordinary prime contraction gives a local map before quotienting, so step 5 applies. The cited nodes have no dependency path back to the item; this is also checked by the server dry run.

I tested empty generating lists and the zero monoid (b=0), all/group-only monoids (one-point spectrum, arbitrary torsion), r=0, s=0, n=0 and all free coordinates inverted (t=r). Inverting a vector with positive coordinates gives exactly integral coordinates on its support, without a saturation assumption. For P=Z or Z/2 the new universal property retains units and the ordinary sheaf; a sharp-only replacement would lose those data. For sharp fan stalks the unit quotient discards precisely the lattice factor. The empty space has no points to check and the covering condition is vacuous. All new-node objects and the local morphism notion are introduced in its statement. The new node has no proof or proof dependencies; it is a strictly smaller general representing property, not a renamed localization or chart clause of the item. All steps are shorter than 2000 characters. I checked delivery-errors B--E against the files: no invented tags, weakened hypotheses, inline hidden standard lemma, unsourced non-elementary step, or unstated comparison remains.

## What could not be finished

Nothing in this stage-1 split. The one new statement-only node is intentionally queued for its own future split. No Lean was written, and no compiler, Lake or local DAG/preflight check was run.
