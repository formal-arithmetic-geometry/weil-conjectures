## Worker report

Q139 states `lem-amb-compact-support-site-comparison-open` in
`Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen`.
The earlier N3 merge (ledger 2026-10-17 14:59) was a stage-1 split: the current
node is `split` and has no Lean record. It does not supersede this stage-2 work.
The natural maps and isomorphisms have real definitions; the statement proofs
remain `sorry`. No natural-language statement, proof plan, or existing dependency
edge was changed.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Finite commutative A | `(A : Type u) [CommRing A] [Finite A]`; the published fixed-scalar coordinates use `ModuleCat (ULift A)` |
| Noetherian X and S | `[IsNoetherian X] [IsNoetherian S]` |
| f and its compactification j,r | `{f : X ⟶ S} (c : Compactification f)`; `c.i`, `c.g`, `c.comm`, and their bundled open/proper instances |
| Noetherian compactification | `[IsNoetherian c.Z]` |
| Ordinary bounded-below etale/pro-etale module categories | `DerivedCategory.Plus (Sheaf ... (ModuleCat ...))`; no completed or constructible subcategory |
| Chosen etale compact-support candidate | `Etale.rightDerivedLowerShriekOfCompactificationPlus ... c` |
| Chosen pro-etale compact-support expression | `ProEtale.rightDerivedLowerShriekOfCompactificationPlus ... c` |
| Canonical site inverse image | `(comparisonUpperStar ... T).mapDerivedCategoryPlus` |
| Canonical J is an isomorphism | `(compactSupportSiteComparisonPlus (ULift A) c).app L` is an `Iso`; its hom is used in the equation |
| J is specifically the composite of the proper and open site comparisons | Its definition uses `fixedComparisonDirectImageMatePlus` and `compactSupportSiteOpenIsoPlus`, the latter descended from `openImmersionLowerShriekComparisonUpperStarIso` |
| Every open u and its pullback square | `[IsOpenImmersion u] (sq : IsPullback v f' f u)`; the arbitrary pullback presentation includes the literal fibre product |
| Restricted compactification | `c.ofIsPullback sq`; its two cartesian squares are `c.isPullback_g_ofIsPullback sq` and `c.isPullback_i_ofIsPullback sq` |
| C et | `compactSupportEtaleExchangePlus A sq c`: `Etale.baseChange` followed by derived inverse of `Etale.openImmersionLowerShriekBaseChangeMap` |
| C pro | `compactSupportProEtaleExchangePlus A sq c`: the derived adjunction mate of `upperStarCompIso`, followed by the derived inverse of `sfFixedOpenExtensionBaseChange` |
| Open-restriction equation | `compactSupportSiteComparison_open`; both `fixedComparisonPullbackPlus ... u` and `... v` are displayed rather than silently identifying endpoints |
| Natural in L | J is a natural isomorphism and both exchanges are natural transformations. The component equation quantifies over every `L : DerivedCategory.Plus ...` and hence is an equality of these natural transformations |
| Actual direct-image counits | First conjunct of `compactSupportSiteComparison_open_counits`, the explicit counit equation for `fixedComparisonDirectImageMatePlus A c.g` |
| Actual extension evaluation counits | Second conjunct of `compactSupportSiteComparison_open_counits`, using the descended `openImmersionLowerShriekUpperStarAdjunction` on both sites |
| Normalization for the restricted compactification too | Apply that same universally quantified counit theorem to `c.ofIsPullback sq`; its Noetherian hypotheses follow from open restriction |
| No assertion for arbitrary unbounded pro-etale inputs | The open-restriction theorem is on D+ and its only input is an etale L, pulled to the pro-etale site |

The coefficient presentation is the published one, not a new module category.
`finiteCoefficientEtaleRealization` and `finiteCoefficientRealization` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` identify fixed-scalar sheaves with
the module sheaves of the two recorded coefficient ring sheaves. The recorded
`finiteCoefficientDerivedComparison` is precisely comparison followed by this
realization, termwise descended. For the intrinsic constant ring presentation,
`Scheme.sfIntrinsicModuleEquivalence`, in
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`, defines the recorded
`sfIntrinsicExtensionByZero` by conjugating the fixed-scalar open extension.
`Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`, imported by the
open-exchange dependency, fixes the direct-image comparison on constant scalar
sections and K-injective representatives. Thus use of fixed coordinates preserves
both the specified operations and their mate normalization. The `ULift` has the
published small-site size (`Scheme.{u}`, site objects in u+1, morphisms in u);
it imposes no equality of these two site universes and does not restrict finite rings.

Dependency declarations read and used:

- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement`
  and its category; the underlying `Compactification` and base-change construction
  are used, with no need to assume a refinement or compactification independence.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, with Mathlib `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the module categories and canonical
  realization/derived comparison named above, read together with their docstrings.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`, and the underlying `comparisonUpperStar`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactificationPlus` and ambient compatibility.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`, its exactness and the upper-star adjunction.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `Etale.exactDerivedBaseChangeMap`,
  whose mate formula restricts to the `Etale.baseChange` used here.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `Etale.etaleLowerShriekBaseChangeMap`. The arbitrary-square open specialization is
  the published `Etale.openImmersionLowerShriekBaseChangeMap`, with its invertibility
  theorem in `...OpenImmersion.BaseChangeSquare`. Both are the same conjugate of
  the direct-image exchange, with the inverse direction used in C.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, including the counit formula.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero` and `sfIntrinsicModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  the recorded constant-section coefficient comparison, module adjunction, and
  `proEtaleConstantRingDerivedPullback`; the fixed-coordinate realization of these
  operations is supplied by the imported `SfIntrinsicRealizationTransport`.
- `Sheaf.AlgebraicGeometry.SfFiniteOpenExtensionBaseChange`:
  `sfFixedOpenExtensionBaseChange` and `sfFixedOpenExtensionBaseChange_isIso`.
- The two repaired dependency modules below supply the named canonical proper and
  compact-support comparisons; their signatures and construction formulas are retained.

The source was read locally in `literature/stacks-project/proetale.tex`,
`lemma-morphism-comparison` (09A6) and `lemma-jshriek-comparison` (09AF), including
both proofs. The first supplies the actual qcqs mate; the second fixes the open
comparison by adjunction. The seven existing proof steps are carried in the theorem
docstring, including the displayed order of the two pastings and the triangle-identity
argument for the open evaluation counit.

Edge cases checked: the zero ring, the zero complex, empty X, empty base open,
identity base open, and the identity compactification. No nontriviality, nonempty
scheme, positive cohomological degree, or constructibility condition is imposed.
The inverse open exchange has the correct direction: beta goes from j'_!v* to w*j_!,
so C uses beta inverse. The proper exchange need not be an isomorphism to state the
equation. The equation uses the same bounded-below L on both sites. No compactification
independence or arbitrary unbounded comparison is claimed.

Searches performed with msearch.py for Q139 and this item:

- LeanFinder: `The canonical comparison of etale and proetale compactly supported
  direct image commutes with restriction to an open subscheme`: eight hits about
  scheme restriction, including `Scheme.Hom.map_appLE` and `Modules.restrictFunctorComp`;
  none states the item.
- Loogle: `CategoryTheory.mateEquiv`: twelve generic mate identities. They give the
  canonical map construction, not the geometric statement.
- Mathlib grep, AlgebraicGeometry: `compact.*[Cc]omparison|[Cc]omparison.*[Ss]hriek`:
  zero hits.
- LeanSearch: `The canonical etale proetale compact support comparison commutes with
  open restriction and adjunction counits`: eight hits on restriction counits and
  generic topological counits; none states the item.
- Source and side-library rg for compact-support/comparison vocabulary located the
  canonical J module, the fixed canonical direct-image mate module, and the open
  base-change interface. Their full sources were read. The first two had incompatible
  legacy/finite imports, repaired below rather than replaced by arbitrary maps.
- The source grep for the exact item id had no hit. The upstream name table,
  Mathlib, source library and side library had no hit for the new exchange/theorem names.

## Dependency modules

`lem-weil-pbc-comparison-direct-image-canonical-mate` is repaired **in its existing module**
`Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`. The saved replacement module
`CompactSupportDirectImageMate` has been removed. The four declarations named in the
return now have exactly one owning module; consumers import and reuse that original
module. Comparison with the current published source (`scompile.py --source`) and the
read-only source confirms that all signatures, docstrings, construction bodies and
postponed proofs are byte-identical after the imports. Only the import interface is
repaired: the legacy derived pro-etale family is replaced by the compatible published
finite-coefficient derived family, retaining the exact `rightDerivedFunctorPlusBaseChange`
construction, qcqs invertibility and counit normalization. No declaration is renamed.

`lem-sf-class-compact-support-comparison` is likewise repaired in its original module,
`Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`; the saved replacement
module `FiniteCompactSupportSiteComparison` has been removed. Its original legacy
lower-shriek import collided with the finite family. The existing two comparison
signatures and the specified canonical proper mate are retained. The auxiliary
`compactSupportSiteOpenIsoPlus` remains the literal termwise descent of the published
open comparison, as in the saved packet, avoiding the incompatible proper-open umbrella.
The main item imports this original comparison module, which imports the original
mate module. Both dependency records identify those original module paths, so the
repair introduces no second owning module for either set of comparison declarations.
The three added statement dependencies of the saved packet are retained unchanged.

Additional dependency-record repair:
`lem-cbc-proetale-extension-zero-base-change` now records the exact existing
`sfFixedDerivedOpenExtensionBaseChangeIso` interface in
`Sheaf.AlgebraicGeometry.SfFiniteOpenExtensionBaseChange` (`existing: true`).
The old `StrictTower.singleBeta` is stated in intrinsic ring-sheaf module coordinates,
whereas the canonical J interface uses fixed-scalar sheaves. The published replacement
is the identical ordinary unbounded open-base-change isomorphism in these coordinates,
with its inverse explicitly the same unit-normalized adjunction conjugate. Its underlying
`sfFixedOpenExtensionBaseChange` and invertibility theorem are included in the record,
so the exact maps used in C are now recorded dependency declarations.


## Second reading by Q139

This is the author's second reading; the dispatcher explicitly forbids starting
another agent, and the maintainer supplies the independent review. I reopened the
node, all three modules and the source lemmas. The map under study is the canonical
mate composite, not the upstream comparison that uses a bare Nonempty choice.
I checked source/target and direction of all four factors in the restriction equation:
the u comparison is inverted before nu_U(C et), while the v comparison is inverted
after C pro; these place both paths in exactly the same Hom set. The cartesian
square uses the restricted compactification, not an unrelated choice. The original
Noetherian hypotheses and finite coefficients are retained, and no extra condition
on L appears. Both counit kinds are explicitly stated, and the theorem is applicable
to the restricted compactification as well. The initial stale-dispatch diagnosis was
corrected: the N3 split supplies the proof plan, not a stage-2 statement. The incompatible
imports were replaced by the compatible published family while retaining the maps.
For this return, I additionally checked declaration ownership against the current base: the
mate and compact-support comparisons are now delivered as import-interface repairs to their
original modules, and the item imports those modules. The four mate declarations are
identical to the originals after imports; no duplicate or renamed mate remains in the packet.

Import compatibility note: the recorded proof-only
`SupportComparisonPullbackCoherence` and upstream legacy
`ProEtale.BaseChange.SmoothBaseChange` cannot be combined with the finite family
without duplicate pro-etale operation declarations. The canonical pullback
comparison used in their equations is already the identical
`comparisonUpperStarCompUpperStarIso` descended in `fixedComparisonPullbackPlus`.
Their proof steps are retained explicitly in the docstring; their incompatible
umbrella imports are not silently used to choose different maps. No proof has
been filled.

Verification: all three delivered modules and the existing-declaration probe passed
the required scompile.py invocation through deliver2.py. The first preflight found
a signature-record formatting mismatch (`noncomputable def` versus the parser's
`def`); the record now starts at the declaration keyword exactly as required.
No Lean statement or definition changed for that repair.

## Returned delivery repair

The immutable returned head `c8708414e407` and the saved packet assigned the four
`fixedComparison*` declarations to `CompactSupportDirectImageMate`, although their
original owner `FixedComparisonDirectImageMate` already existed. The initial required
saved-packet dry run passed compilation and preflight (commit `40eeb66348`); the explicit
ownership self-check still found the return's duplicate declarations. This repair removes
the replacement module and updates its consumer to import the original module. Its import
interface is repaired in place under §1(B), with the original declarations unchanged.
The analogous compact-support comparison repair also uses its original owning module.
The item statement, theorem signatures, map formulas, proof plan, hypotheses and edge cases
are retained from the saved packet. No new node or statement correction is introduced.

Repair verification: `scompile.py Q139 lem-amb-compact-support-site-comparison-open`
compiled all three delivered modules separately in dependency order, including the
consumer importing both repaired original modules. The server returned exit code 0,
no errors and no warnings. The longest reported single-file compile was 34.7 seconds.
The local packet audit also checked that every recorded signature matches its file,
all Lean lines are at most 100 characters, every module disables auto-implicit variables,
node changes are confined to the authorized fields, and each delivered declaration name
has exactly one owning module. The original mate source is unchanged after the imports.

The repaired delivery dry run passed compilation and maintainer preflight as
`3f6b24a9eb`. It staged the original `FixedComparisonDirectImageMate` and
`CanonicalCompactSupportSiteComparison` module paths, the item module, four node
records and this report. The wrapper preserved a concurrently updated maintainer
`reviewed_lean` field on the compact-support dependency; that field is not part of
the worker's changes.

## Returned delivery repair

The returned immutable head removed the broad import family from
`FixedComparisonDirectImageMate`. `CanonicalCompactSupportSiteComparison` uses
`Etale.rightDerivedLowerShriekOfCompactification`,
`Etale.rightDerivedLowerShriekOfCompactificationPlus`, and
`Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility`, all owned by
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`. I added that module as a
direct public import of the consumer, so its declarations remain available when
the mate module's transitive imports are reduced. No definition, signature, or
node statement changed.

## Maintainer review fix (NT-cc-Q139-3dd16f3fd)

The delivered `CanonicalCompactSupportSiteComparison` added `compactSupportSiteOpenIsoPlus`,
a literal copy (same type, same body) of the existing `properOpenSiteExtensionIso` in
`Sheaf.Paper.ProEtaleProperOpenComparison` (one definition per notion, H4). The stated
reason, an import collision with that module, no longer holds on the base: the base
version of the module, which imports `Sheaf.Paper.ProEtaleProperOpenComparison`, compiles
together with the item. The fix removes the copy, restores the public import of
`Sheaf.Paper.ProEtaleProperOpenComparison`, and uses `properOpenSiteExtensionIso` as the
open factor of `compactSupportSiteComparisonPlus` and in the second conjunct of
`compactSupportSiteComparison_open_counits`. The two maps are equal by definition, so no
map, signature or recorded statement changes, and the item's `lean.statement` is still
verbatim. `lem-sf-class-compact-support-comparison` therefore no longer records
`compactSupportSiteOpenIsoPlus`. Its open factor is the published helper of
`lem-weil-pbc-proper-open-comparison-proetale`, as on the base.

Compile check (`nt_compile.py --json`, three modules in dependency order): exit 0, no
errors. The same check passed for seven direct importers of the two repaired dependency
modules: ProperExceptionalOpenBaseChange, ProperOpenComparisonSiteNormalization,
ProperOpenSiteTransport, CompactSupportExchangeTransport, SiteComparisonEdgeSection,
ExceptionalMateSiteComparison and BoundedSiteAdjunctionTranspose. Four other importers
fail in the overlay with the base versions too, because of duplicate legacy and finite
pro-etale imports. Those failures were already present, and the delivery neither causes
nor changes them.
