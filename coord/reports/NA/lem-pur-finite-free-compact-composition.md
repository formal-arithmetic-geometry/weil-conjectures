## Worker report

The module states `AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition`.
Its proof is `sorry`; every definition has real data. It also supplies only endpoint adapters
for already recorded scalar, compact-support, composition, refinement and site maps.
This repair adds one existing-definition ownership node and corrects dependency ownership.
There are no dependency modules or statement corrections.

Hypotheses and clauses, in the node's order:

- The finite-field datum k = algebraic closure of F_q is `D : FiniteFieldDatum`; the prime
  coefficient characteristic and its inequality are `[Fact l.Prime]` and `_hl : l ≠ D.p`.
- The finite coefficient field E is the explicit field/algebra/finite-dimensional binders.
  `n : ℕ+` means precisely n >= 1. `t : Stage l E` retains the actual upper field and its
  embedding of E. `a : Arrow (baseStage n) t` retains the field map over E; `_level` sets the
  two base-uniformizer exponents equal. Thus the source is O_E/(varpi_E^n) and the target is
  O_L/(image(varpi_E)^n). Stage.parameter and Stage.ideal keep ramification: the target is
  not O_L/(varpi_L^n). The unit and ramification ideal equality, and finite freeness, are
  the first two clauses of finite_free_coefficient_extension, not additional hypotheses.
  Stages use the existing chosen uniformizers; changing one by a unit gives the same ideal.
- All three schemes have explicit `Over (Spec D.k)` structures, separatedness, locally
  finite type and quasi-compactness of their structure maps. Both maps are over that base
  and are separated, locally finite type and quasi-compact. These are exactly separated
  finite-type k-schemes and morphisms, not proper or smooth maps.
- `pro : Bool` quantifies over both ordinary small sites, using `Sites.D`, `Sites.scalar`
  and `Sites.Ctf` from FiniteFreeCoefficientExtension. `false` is etale and `true` is pro-etale.
  The site object/morphism universes stay u+1/u; coefficient fields are allowed in u+1,
  with no equality imposed on site universes. Smaller fields are represented by ULift.
- `K` and `_hK : Sites.Ctf ... K` give precisely the bounded constructible finite-Tor
  domain. The property uses finite-value etale constructibility and ordered Tor intervals;
  on the pro-etale side it is the published constructibleFiniteTor property.
- `c`, `d`, `e` are arbitrary compactifications of f, g and their composite, with no
  compatibility, cartesianness or density assumption. `support` selects the recorded
  ordinary Rp_* j_! on each site.
- `coefficientMap false` is exactly ExceptionalCoefficients.compactSupportMap: the
  proper scalarMate at j_!K followed by Rp_* of openIso. scalarMate is the B-adjunction
  counit transpose with the normalized scalarPullbackIso, and openIso is the balancing
  comparison from the open adjunction. `coefficientMap true` uses the inverse scalar
  Hom adjunction applied to P_A of the scalar unit followed by compactSupportRestrictionIso.
  This is precisely compactSupportCoefficientComparison evaluated on the fixed scalar
  left adjoints; its published factorization and proper-counit/open-unit identities
  identify the same constituents. No arbitrary morphism or isomorphism is chosen.
- `IsIso (coefficientMap ... c K)` states invertibility. The following universally
  quantified K', v equation is naturality on the full constructible finite-Tor domain.
  Since f and c are arbitrary, this supplies every h and every chosen compactification.
- The two existential conjuncts supply bounded-below etale witnesses for K and S_XK,
  so the subsequent universal equations are not assertions on potentially empty witness
  types. They add no assumptions. For the etale case the witness is simply a bounded-below
  presentation; for the pro-etale case it is realization by the actual comparison functor.
- `composition` uses etaleComposition, or coherenceProEtaleCompositor on the pro-etale
  realization, conjugated by the retained witness. etaleComposition only inserts the
  published D-plus inclusion comparisons around coherenceEtaleCompositor. The latter
  uses exactly the canonical proper/open normalized compositor, not a new comparison.
- The first equation under `∀ L α N β` is
  S_Z(alpha_A) followed by c_gf = c_g followed by P_g,B(c_f) followed by alpha_B.
  Lean's `≫` reads in the opposite written order from the paper's function composition.
  Its source is S_Z P_g,A P_f,A K and its target is P_gf,B S_X K. All homs are in D(B).
- `refinement` uses the inverse of the existing etale refinement isomorphism and
  properTransportRefinement on the pro-etale realization. For `r : c'.Refinement c`
  both directions are from P^{c'} to P^c. The final equation is exactly
  S(r_A) ≫ c^c = c^{c'} ≫ r_B. The quantification covers every proper refinement;
  common-refinement and transitive comparisons are the published coherent comparisons.
- `SiteCompatibility` explicitly identifies the actual pro-etale coefficient arrow with
  the transported etale arrow. It inserts compactSupportSiteComparison and scalarSite
  at both ends, and allows every bounded presentation N and comparison gamma of S(L).
  Together with the specified site-coherent geometric comparisons this states the
  ordinary/pro-etale compatibility, rather than merely asserting similar equations on
  two unrelated presentations. On arbitrary realizations the α and β conjugations keep
  the same actual maps. Identity and arbitrary-isomorphic-witness cases are included.
- No smoothness, orientation, or trace hypothesis or conclusion appears.

Dependency declarations read and imported:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `lem-coef-finite-free-extension`: `Sheaf.Paper.FiniteFreeCoefficientExtension`, `WeilConjectures.FiniteFreeCoefficients.finite_free_coefficient_extension`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `lem-sf-proetale-constructible-origin`: `Sheaf.Paper.ProEtaleConstructibleOrigin`, `AlgebraicGeometry.ProEtale.constructible_proEtale_origin`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `lem-coef-finite-direct-image`: `Sheaf.Paper.FiniteCoefficientDirectImage`, `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_isIso`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
- `lem-amb-etale-compact-comparisons`: `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`, `AlgebraicGeometry.Etale.etaleCompactSupport_refinementComparison_eq`.
- `thm-sf-comp-composition`: `Sheaf.Paper.CanonicalOriginCompactSupportComposition`, `AlgebraicGeometry.ProEtale.originComposition`.
- `def-per-exceptional-coefficient-maps`: `Sheaf.Paper.ExceptionalCoefficientComparison`, `AlgebraicGeometry.Etale.ExceptionalCoefficients.compactSupportMap` and `openIso`.
- `lem-sf-compact-support-restriction-of-scalars`: `Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`, `AlgebraicGeometry.ProEtale.compactSupportRestrictionIso` (the fixed-ModuleCat presentation of this node, built using the named invertibility theorems).
- `def-coef-finite-coefficient-stages`: `Sheaf.Paper.FiniteCoefficientAdjointComparisons`, `AlgebraicGeometry.FiniteCoefficientAdjoints.Stage`, `baseStage`, `Arrow`, `Arrow.ringMap`.
- `def-pur-chosen-compactification-compositors`: `Sheaf.Paper.CompactSupportSiteCoherence`, `AlgebraicGeometry.ProEtale.coherenceEtaleCompositor`, `coherenceCompactificationChange`, `coherenceProEtaleCompositor`.
- `def-sf-compact-support-site-comparison-construction`: `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`, `AlgebraicGeometry.ProEtale.compactSupportSiteComparison`.
- `def-sf-refinement-comparison-isomorphism`: `Sheaf.Paper.RefinementComparisonIsomorphism`, `AlgebraicGeometry.ProEtale.refinementComparisonIsomorphism`.

The added statement dependencies name the concrete construction owners. In particular,
the exceptional tensorIso/unitIso choices and finite_coefficient_adjoint_comparisons are
not used. compactSupportSiteCoherence remains a proof dependency, not a statement
prerequisite for its three plain helper definitions. The pro-etale restriction comparison
is cited through its own theorem node, since its asIso construction uses the named
open/proper invertibility theorems. The old etale coefficient-change import carrier is
replaced by the actual fixed-scalar restriction module; no declaration from that carrier
is used. All original base statement dependencies remain in order. These ownership
corrections repair the returned packet rather than claim a mathematical statement change.

Edge cases checked: E=L and identity coefficient embedding; n=1; ramification e>1
(the target exponent is en, never n in the upper uniformizer); empty X; K=0;
f or g identity; solely proper or solely open factors; identity refinement and arbitrary
non-Cartesian proper refinements. None adds a hypothesis. Both site cases retain every
morphism of the ambient B-linear derived categories, not just liftable maps.
Witness conjugation includes α=identity and any other retained origin isomorphism.

Searches:

- msearch leanfinder, "finite free coefficient extension compact support composition refinement":
  8 unrelated compact support/finite support results; no statement match.
- msearch loogle, "finiteCoefficientChangeDirectImageMap finiteDirectImageComposition": no
  indexed result (project identifiers unknown to the Mathlib search service).
- msearch loogle, "Module.Free, Module.Finite": 12 finite-module results, including
  Module.finBasis and finrank lemmas; none states compact-support coefficient coherence.
- msearch grep, "compactSupportMap|finite.free.*compact|compact.*coefficient" in
  CategoryTheory: no Mathlib result.
- msearch leansearch, "Finite free change of coefficients commutes with composition and proper
  refinement of compactly supported derived pushforwards of etale sheaves": 8 ordinary
  pushforward-composition and free-pullback results. They do not include derived compact
  support, coefficient mates or refinement squares.
- rg on WeilConjectures and Sheaf found the proper/open maps, coefficient comparison,
  etale composition and pro-etale site-coherence interfaces used above. No existing
  declaration states this entire finite-free composition/refinement theorem.
- rg on Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json found no collision
  with the new namespace or theorem name.

Source read: the current main-20261015 transport proof, Steps 1 and 3, and the full
item proof's eight steps. The theorem docstring gives the whole natural-language proof.
No STATEMENT-DISPUTED condition or source error was found.

Validation: scompile.py compiled the sandbox probe and the final library module separately
against the live server build, both without errors or warnings (8.1 and 8.3 seconds).
The dry run and delivery are recorded by the delivery wrapper.

## Repair of returned head 0606f675dfda

1. Cite def-coef-finite-coefficient-stages for Stage, baseStage, Arrow and ringMap.
2. Cite def-per-exceptional-coefficient-maps for compactSupportMap and openIso; neither
   tensorIso nor unitIso, nor their existence theorems, occurs in the item construction.
3. Add def-pur-chosen-compactification-compositors with existing:true, owning the three
   concrete definitions in Sheaf.Paper.CompactSupportSiteCoherence. The theorem of that
   module is only a proof dependency. No copied definition or new postponed theorem.
4. Cite lem-sf-compact-support-restriction-of-scalars for compactSupportRestrictionIso,
   whose data use named isomorphism theorems, and cite the already landed
   def-sf-compact-support-site-comparison-construction for compactSupportSiteComparison.
   Replace the unused EtaleCompactSupportCoefficientChange import with the direct
   CompactSupportRestrictionOfScalars import and make the site-construction import public.

Compared the retained packet against current main: main has no lean record for the item
and has the original 15 statement dependencies. The retained packet matches the returned
review's dependency additions; the saved delivery log identifies 0606f675df. The theorem
signature and helper bodies are retained verbatim, and the review's accepted clause and
edge-case correspondence above remains valid. The automatic unchanged-packet dry run
passed at 2200988ce8 before these required H2 repairs; this is not offered as the repair.

## New nodes

`def-pur-chosen-compactification-compositors` records the existing etale compositor,
pro-etale common-refinement change and pro-etale compositor at an etale-origin witness.
The source is transport Steps 1/3, with the exact normalized formulas read from the
site-coherence construction, proof Steps 4--6. The etale composite compares c,d to the
chosen compactifications, uses the canonical compositor, then compares to e. The
pro-etale change is the inverse first common-refinement leg followed by the second.
The pro-etale compositor inserts that change and the canonical intermediate site
comparison around originComposition. The existing:true binding lists all three names;
no coherence theorem is assumed just to obtain their data. Finite A, quasi-compact f/g,
arbitrary chosen compactifications and every bounded-below L match the existing
signatures. Identity compactifications, the zero object, empty schemes and identity
common-refinement legs are admitted without additional hypotheses.

Repair searches used msearch.py leansearch (canonical chosen-compactification etale and
pro-etale composition/common-refinement maps): eight topological compact-support and
scheme-property results, no match; leanfinder (compact support chosen compactification
composition common refinement comparison etale pro etale): eight affine-transition-limit
or ordinary site results, no match; grep in Mathlib CategoryTheory for the three names
and compactSupport.*Compositor: zero hits. Direct rg in WeilConjectures/Sheaf locates
only the published three definitions in CompactSupportSiteCoherence. DAG search and
blueprint_refs.py search compact-support locate the theorem owner but no definition
owner of these three. The exact msearch output records are in the new node.

## Repair self-check by NA

This is the dispatcher's worker self-check, not a claimed independent second reader.
The maintainer supplies the independent review. Checked the node and Lean file again:
all finite-field, prime, field-extension, positive-level, over-base, separated finite-type,
compactification and constructible finite-Tor binders are unchanged. The naturality,
invertibility, origin witnesses, composition equation, every proper-refinement equation
and the explicit site-comparison square are unchanged. The new definition node asserts
only the existing three composites, with the same objects and no extra coherence clause.
The lean.statement signature is still verbatim. JSON changes to the item are only lean
and stmt_deps. The four returned ownership faults are each addressed above.

Repair validation: scompile.py compiled the final module against the live server build
without errors or warnings (sandbox probe 7.9 s, library module 7.1 s). The new node
is existing:true and binds the published definitions without introducing a module.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
