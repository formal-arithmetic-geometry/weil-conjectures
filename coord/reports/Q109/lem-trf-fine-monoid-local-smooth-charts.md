## Worker report

Stage 2 statement delivery, not a repetition of Q53's stage-1 split. The ledger's
2026-10-23 11:15 merge is stage 1: the current item has no lean record, is split,
and occurs in the stage-2 queue. No repair note reopens a previously stated item.

The new module Sheaf.AlgebraicGeometry.FineMonoidLocalSmoothCharts states all clauses
of the node as eight named theorems. Every new proof is sorry; there are no new
notions, definitions, helper choices, axioms, or changes to the mathematical node statement.
Sources read directly: ILO Travaux de Gabber, Exposé VIII, printed pp.98--100,
Remarks 3.1.4(iii), 3.1.10(ii), Lemma 3.1.14, 3.1.13--3.1.15 and Remark 3.1.16.
The PDF's text was inspected at these exact places, including the localization proof.

Hypothesis and clause correspondence (names below are in AlgebraicGeometry):

- Fine integral commutative monoids are the dependency's FineFan.IsFine, the conjunction
  of Monoid.FG and injectivity of the canonical map to the Grothendieck group. All monoids
  use multiplicative notation; 1 renders additive 0. All universes and variables are bound.
- A local map is IsLocalHom φ. Its smooth product decomposition is r s : ℕ, a MulEquiv
  e from P × Multiplicative (Fin r → ℕ) × Multiplicative (Fin s → ℤ), and the equation
  he : ∀ p, e (p,1,1) = φ p. These are the hypotheses of
  FineFan.smooth_localization_product. The product is right-associated, as in the
  recorded Monoscheme.Hom.IsSmooth definition.
- Arbitrary localizations P', Q' are expressed by S, T : Submonoid, monoid homomorphisms
  a, b, and S.IsLocalizationMap a, T.IsLocalizationMap b. These are Mathlib's full
  localization universal-property predicates, not arbitrary maps or just localization-away.
  hcomm : φ'.comp a = b.comp φ says that the map extends φ. IsLocalHom φ' expresses
  exactly the further localness hypothesis. The conclusion gives finite r', s', e'
  extending φ'. It adds no torsion or saturation hypothesis.
- FineFan.smooth_sharp_localization_product expresses the fan localization clause:
  P and Q are sharp, the initial map extends P × N^r, a and b are arbitrary ordinary
  localizations, and e' identifies Associates Q' with Associates P' × N^r'.
  The equation on e' extends precisely FineFan.sharpenMap φ'. Associates is the
  existing unit quotient, and there is no lattice component after sharpening.
- Monoscheme.exists_smallest_stalk_chart quantifies over the recorded Monoscheme.Fine
  and each x. It gives an AffineOpen with coordinate monoid the actual FineFan.stalk,
  hx : x ∈ openSet, membership iff z ⤳ x, and containment in every open neighbourhood
  of x. These render the set of generalizations and the smallest-open clause.
  The AffineOpen.iso identifies restricted sheafed spaces, so it includes the ordinary
  structure sheaf. The last equation fixes its section-to-germ map: pulling back the
  canonical affine section p and taking its germ equals the restriction stalk map on p.
  This is the canonical stalk chart, not an arbitrary abstract isomorphism. Fineness
  of the coordinate stalk is included as asserted by the description as a fine model.
- FineFan.exists_smallest_stalk_chart gives the identical clauses using the recorded
  sharp FineFan.affine and FineFan.AffineOpen; the existing Fan.sharp condition supplies
  sharp stalks, and this affine model has the sharpened sheaf.
- Monoscheme.smooth_smallest_product_chart has the exact f.IsSmooth hypothesis and
  every y. Its cx coordinate monoid is P = stalk at f(y), with its germ normalization.
  Its cy coordinate monoid is P × N^r × Z^s. The two generalization equalities say the
  opens are X_x and Y_y. The existential affine arrow a is required to satisfy
  Monoscheme.IsAffineMap of the explicit p ↦ (p,1,1) inclusion. This fixes both prime
  contraction and numerator germs. The equation cy.inclusion ≫ f.map = a ≫ cx.inclusion
  states the entire restricted map, including sheaf components, under these charts.
- Monoscheme.smooth_of_product_charts gives the converse for an arbitrary cover:
  every y belongs to some cy with a fine P, cx, and the product chart and commuting
  equality above. Its conclusion is exactly the recorded f.IsSmooth. It does not
  assume that these converse charts were already smallest neighbourhoods.
- FineFan.smooth_smallest_product_chart and FineFan.smooth_of_product_charts render
  the same forward and converse assertions for fans. They use P × N^r, the sharp
  affine model, its canonical target normalization, and FineFan.IsAffineMap of p ↦ (p,1).
  The converse's coordinate P is sharp as required by the fan clause.
- There is no IsTorsionFree hypothesis anywhere. Natural ranks include zero; no
  inhabitedness hypothesis is imposed on any space.

Dependency declarations read in full with their docstrings:

- Sheaf.AlgebraicGeometry.FineFanBlowup: FineFan.IsFine, IsSharp, spectrumSheaf,
  affine, stalk, germ, stalkMap, IsLocalMorphism, Fan, Hom, Hom.IsSmooth,
  IsAffineMap, AffineOpen and AffineOpen.inclusion. The selected record's
  SmoothFunctorialDesingularization was also read; the node records the entire
  module's declaration list, so this item uses its relevant monoid/fan declarations.
- Sheaf.AlgebraicGeometry.MonoschemeToricRealization: Monoscheme.Fine, Chart, Hom,
  Hom.IsSmooth, affine, affineSection, affineGerm, IsAffineMap, AffineOpen and inclusion.
- Mathlib.GroupTheory.MonoidLocalization.Basic: Submonoid.IsLocalizationMap, with
  map_units, surj, and exists_of_eq, and Submonoid.LocalizationMap.toMonoidHom.
The affine-fan universal-property and localization-section theorem nodes are proof
dependencies only; neither supplies a notion used in these eight statements.
Their declarations were read for the proof plan, but they are not imported or repaired
in this delivery. The proof plan and proof_deps remain unchanged.

Edge cases read against the source before writing: r=s=0 is the identity product;
localizing at units (including the empty list of denominators) changes no free coordinate;
localizing every natural coordinate converts the whole natural factor to a lattice;
sharpening then kills that lattice. A finite torsion group in the base is permitted.
Empty monoschemes and fans have vacuous point clauses, and the converse covers may be
empty. At a generic point the smallest neighbourhood and its group stalk are retained,
while at a closed point the whole affine model may be the smallest neighbourhood.
No global finite-cover hypothesis beyond the recorded Monoscheme.Fine is introduced.

Searches made for an exact existing statement or notion:

- msearch.py leanfinder, query "Smooth fine monoid maps remain products with free monoids
  and lattices after localizations; smallest affine neighborhoods of monoschemes are
  spectra of their stalks": eight results about ordinary schemes, including
  Scheme.local_affine, IsAffineOpen.isLocalization_stalk', and IsSmooth.exists_isStandardSmooth.
  None has monoidal spaces or their product chart assertion.
- msearch.py leansearch, query "Fine monoschemes smooth morphisms affine monoid product
  charts": eight results, all scheme smoothness infrastructure, no matching statement.
- msearch.py loogle "MonoidHom, LocalizationMap, IsLocalHom": unknown LocalizationMap,
  no hit. Retried with the actual qualified names "Submonoid.IsLocalizationMap, IsLocalHom":
  zero hits. The localization predicate was read directly from Mathlib's source.
- msearch.py grep "Monoscheme|FineFan|smooth.*monoid": three hits, all formally smooth
  ring-localization results in RingTheory/Smooth/Basic.lean and Fiber.lean, no match.
- rg on lean/WeilConjectures for FineFan, Monoscheme and the item id: no matches.
- rg on lean/Sheaf for smooth monoid localization and smallest neighbourhoods found the
  existing dependency definitions and StrictFanChartLocalComparison.PointLocalization.
  The latter is chart data for the separate strict-log comparison theorem, not this
  statement; no copy of it is introduced. It was read to check the germ normalization.
- rg in Mathlib, WeilConjectures and Sheaf for all eight proposed theorem names:
  no match. The AffineFanHomUniversal and AffineFanLocalizationSections results were
  read as proof dependencies, not imported or rewritten as new theorems.

Validation before the return: the saved five-file packet passed deliver2.py --no-push.
Validation of the repaired three-file packet is recorded below.
No mathematical statement was corrected and no STATEMENT-DISPUTED flag applies.

## Dependency modules

- def-trf-fine-fan-blowup: live and --source both confirm the recorded module is a
  legacy non-module. A required module-mode consumer is rejected at import with
  "cannot import non-`module` Sheaf.AlgebraicGeometry.FineFanBlowup from `module`".
  Preserve the file's existing declarations, definitions, signatures and proofs;
  add module, public imports and an exposed public section. The dependency node
  changes only lean, with an explanatory note and the original selected declaration.
- def-trf-monoscheme-toric-realization: the same legacy-interface repair is necessary
  for the recorded monoscheme notions. The full mathematical file is preserved.

The first source read and the --source server reads confirmed the required dependency
interface failures were not caused by an outdated local checkout.

## Repair of return L (immutable head 618a9a43261a)

H2 repaired: removed lem-trf-affine-fan-hom-universal and
lem-trf-affine-fan-localization-sections from stmt_deps, restoring the base list exactly.
Removed both plain imports from FineMonoidLocalSmoothCharts.lean. Dropped both
AffineFanHomUniversal.lean and AffineFanLocalizationSections.lean and their node
copies from the packet, so this delivery no longer changes those modules or lean records.
The eight theorem statements, proofs and docstrings are unchanged. Both accepted
module-mode repairs, FineFanBlowup and MonoschemeToricRealization, are unchanged.
Compared the saved packet with current main sources: the two retained dependency modules
only add module/public-import/exposed-section syntax, and their nodes only change lean.
The mathematical node statement, proof and proof_deps are unchanged.

Repair validation: scompile.py compiled all three retained delivery modules separately
in dependency order against the live published library and private dependency overlays.
All completed without errors or warnings. The item still has exactly eight named theorems
with sorry proofs, its recorded primary signature matches the file verbatim, and every
retained node differs from current main only in lean. All Lean lines fit 100 columns.
The repaired deliver2.py --no-push check is run before pushing.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
