## Worker report

The module `Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` states
`AlgebraicGeometry.ProEtale.CondensedRing.adicProperLocalizingAdjunctionComparison`.
Its sole postponed proof is `by sorry`. The node's mathematical statement, proof,
and proof dependencies are unchanged. Four new definition nodes record the canonical refinement component, the canonical
derived identity normalization, and the two explicit-size interfaces. The main
theorem signature is unchanged from the reviewed packet. Both existing dependency
records are retained exactly as on the live branch; neither is overwritten.

Hypotheses and ambient objects, clause by clause:

- The single explicit universe `u` is used by `k`, `Scheme`, and `Profinite`.
  Coefficients are the existing condensed abelian sheaves in `Ab.{u+1}`.
  The sheaf and its specified `MonObj` are passed to the existing coefficient
  certificate; `[IsCommMonObj Λ]` supplies commutativity.
- `ℓ : ℕ` and `[Fact ℓ.Prime]` give the prime. `k : Type u`, `[Field k]`,
  `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]` render precisely
  positive characteristic different from ℓ. A field has positive characteristic
  exactly when its characteristic is prime. Algebraic closedness is not assumed.
- `Z Y : Over (Spec (.of k))` and `g : Z ⟶ Y` are schemes and a morphism over k.
  For each structure map, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`
  are exactly separated finite type. `[IsProper g.left]` is properness of g.
- `hΛ : IsEllAdicCoefficient ℓ Λ inferInstance` is the recorded three-constructor
  certificate, including the multiplication index. Its `algebraicClosure`
  constructor uses `Profinite.padicAlgClRingObj`, with finite-subextension-valued
  sections. There is no replacement by all continuous Qlbar-valued maps.
- `condensedRingObj Λ T.left` is Λ_T. All object properties are on the existing
  ordinary `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T.left) Ab)
  (condensedRingObj Λ T.left))`. Neither bounded category changes the ambient
  derived localization, coefficient multiplication, or morphisms.

Conclusions, clause by clause:

- Existential `hB` gives B_T=C_T for T=Z,Y, as equality of object properties.
  B_T is the recorded `boundedConstructible`, using the existing stratified
  `IsConstructibleModuleObject` cohomology. C_T is exactly
  `constantModelBoundedConstructible Λ T.left ⊓ finiteTorAmplitude _`.
  Thus the finite constant local-model requirement and finite Tor requirement
  are both present, rather than silently identifying two constructibility notions.
- Existential `hL` gives L_T=H_T as object properties. L_T is the recorded
  `boundedConstructibleLocalizingClosure`. H_T is the specialization
  `finiteTorLocalizingClosureOfSize.{u+1}`, whose definition is the existing
  generic `localizingClosureOfSize` applied to exactly C_T. Both hulls therefore
  use the same ambient category and coproducts indexed in u+1.
- `ObjectProperty.ιOfLE (hL T hT).le` sends an object to the same ambient object
  and a morphism to the same ambient morphism. The two functor equalities through
  `.ι` explicitly preserve the full ambient inclusions. The next clause supplies
  only membership `hC : C_T ≤ H_T` and equates the two composites B_T→H_T,
  expressing compatibility of the bounded-to-hull inclusions. Reverse hull maps
  use `(hL ...).ge`, again the identity on ambient data.
- `ellAdicLocalizingLowerStar Λ ℓ g hΛ` is exactly the dependency's canonical
  restriction F_g of actual ambient total derived pushforward. It is not an
  arbitrary functor satisfying a preservation predicate.
- The universal membership witness `h` only permits restricting the actual
  `rightDerivedLowerShriekOfCompactification Λ (compactificationOverField g)`
  to H_Z,H_Y. The functor `finiteTorLocalizingLowerShriekOfSize` is exactly that
  restriction, formed by `ObjectProperty.lift`. No new compactification is chosen.
- `J` and `a : ... ⊣ J` are the supplied adjunction on H_Z,H_Y. Universally
  quantifying this supplied data avoids choosing or replacing its right adjoint.
  Conjugation with `ιOfLE (hL ...).le/.ge` writes it on L_Z,L_Y.
- Existential `e` is a natural isomorphism from this transported compact-support
  functor to F_g. Its normalization is explicit: for every common dense boundary
  refinement d with projections r₁ to the chosen compactification and r₂ to the
  identity compactification,
  `e_M ≫ identityComparison.inv_M ≫ refinementComponent(r₂,M)
   = refinementComponent(r₁,M)` in the ambient derived category.
  Here `identityComparison` is the existing
  `isoWhiskerRight (derivedOpenImmersionLowerShriekId ...) Rg_*` followed by
  `Functor.leftUnitor`. The refinement components are exactly the recorded
  canonical open-adjunction/derived-compositor maps. Thus e is characterized by
  the proper compactification comparison, not an unspecified natural isomorphism.
  The `qc` argument only certifies the chosen open as a boundary-category object;
  it exists because the open in a compactification of a proper g is proper
  (`Compactification.isProper_openImmersion`), hence quasi-compact. All such proof
  witnesses are quantified; proof irrelevance prevents any dependence on them.
  Common dense refinements exist by the recorded compactification framework.
- Existential `b` is the resulting adjunction F_g⊣J on L, with J expressed under
  the same identity identifications. For all M,N and f:F_g M→N, the final equality
  is exactly `b.homEquiv M N f = a.homEquiv ... (e_M ≫ f)`, expressed on ambient
  arrows via `.hom` and `ObjectProperty.homMk`. The inclusions are fully faithful,
  so this is also equality of the corresponding full-subcategory arrows.
  `Adjunction.homEquiv` already includes bijectivity and naturality in both objects.
  Diagrammatic composition `e_M ≫ f` is precisely f∘e_M in the node.
- None of these definitions or hypotheses imposes derived completeness.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: the over-field binders and
  `CondensedRing.compactificationOverField` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  its docstring and full signature fix the same Nagata compactification. The
  `Compactification.overObj`, `overI`, `overG`, `overI_overG` interfaces were read
  in `WeilConjectures.Compactification.Over`.
- `def-sfb-adic-coefficient-certificate`: `CondensedRing.IsEllAdicCoefficient` in
  `Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient`; all three constructors read.
- `sk-def-sfb-qlbar-condensed`: `Profinite.padicAlgClCondensedRing` and underlying
  `padicAlgClRingObj` in `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.
- `sk-def-sfb-module-derived-pushpull`: the recorded
  `moduleObjectDerivedPushforward` in `Sheaf.Paper.CondensedModuleDerivedPushpull`
  is publicly imported. Its body is the existing total `rightDerivedFunctor` of
  `lowerStar`; this is the same ambient Rg_* used by F_g.
- `sk-def-sfb-bounded-constructible`: its recorded
  `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly retains
  the original internal-module interface; the statement uses that exact
  `AlgebraicGeometry.ProEtale.boundedConstructible`, not the auxiliary discrete
  coefficient specialization. Its complete definition and membership theorem were
  read in `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
- `def-sfb-constructible-module`: `IsConstructibleModuleObject` and
  `IsLocallyFinitelyPresented` in `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`.
- `sk-def-sfb-constructible`: `constantModelBoundedConstructible`,
  `IsConstantModelConstructible`, `HasFiniteConstantLocalModel`, and
  `ConstantModelConstructibleFiniteTor` in `Sheaf.Paper.CondensedConstantConstructibility`.
- `def-sfb-bounded-constructible-localizing-closure`:
  `boundedConstructibleLocalizingClosure` and `boundedConstructibleToLocalizing` in
  `Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure`.
- `sk-def-localizing-closure`: existing `localizingClosureOfSize` in
  `Sheaf.Paper.LocalizingAdmissibleCoefficients`, specialized by the new definition
  node below. The old `localizingClosureProEtale` definition was also read.
- `lem-sfb-adic-proper-localizing-pushforward`: `ellAdicLocalizingLowerStar` in
  `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward`; its full body is
  the existing lift of inclusion followed by actual ambient Rg_*.
- `sk-prop-sf-existence`: `exists_localizingExceptionalAdjoint` and
  `localizingLowerShriek` in `Sheaf.Paper.LocalizingExceptionalAdjoint`, publicly
  imported directly by the main module, with its live theorem record unchanged. The original witness-rich
  signature and the actual compactification restriction were read in full.
- New `def-sfb-compactification-refinement-component` records the existing plain
  `compactificationRefinementComponent` in `Sheaf.Paper.CompactificationCoherenceCocycle`.
  Its signature and body at line 66 were read. The item does not cite the coherence
  theorem node as the definition of this component and does not use its existential φ.
  The component's definition dependencies are `def-sf-comp-refinement-data`
  (`refinementDerivedLowerStarComp`, `localizingRefinementMap`),
  `def-sfb-module-derived-lower-shriek-compactification`
  (`rightDerivedLowerShriekOfCompactification`), and `det-nagata-definition-refinement`
  (`BoundaryCompactification`, `DenseBoundaryCompactification`). Their complete
  signatures, docstrings, and defining bodies were read in the recorded modules.
- New `def-sfb-derived-open-lower-shriek-id` records the existing
  `derivedOpenImmersionLowerShriekId`, together with `openImmersionLowerShriekId`,
  in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek`.
  The former applies `mapDerivedCategoryNatIso` to the latter and composes with
  `mapDerivedCategoryIdIso`. The latter is the unique left-adjoint comparison for
  the canonical pullback identity normalization. Both full signatures and bodies
  at lines 59–68 were read.

Proof-only imports follow the five DAG proof steps: Mathlib's Noetherian permanence
and quasi-separatedness, `Sheaf.Paper.AdicConstructibilityPredicateComparison`,
`Sheaf.Paper.LocalizingClosureCtfEqualsBc`, `Sheaf.Paper.ProperExceptionalRestriction`,
and `Mathlib.CategoryTheory.Adjunction.Basic` (`ofNatIsoLeft` and its Hom formula).
The source proof files `det-existence-restriction.proof.md` and
`sk-cor-existence-ii-restriction.proof.md` were read directly, as were the relevant
recorded declarations. No new proof is supplied in this stage.

Edge cases checked: empty source or target schemes and zero derived objects are
admitted; no nonemptiness binder is added. Integral torsion objects are included
by finite Tor amplitude (a degree-zero torsion module may have amplitude [-1,0]);
no flatness or rationality assumption replaces finite Tor amplitude. The identity
proper morphism and a nondense chosen compactification are included: normalization
uses a common dense refinement, without assuming either compared compactification
is dense. Arbitrary integers and shifts remain admitted by the ordinary derived
object predicates. No algebraic-closedness of k or equality of site object and
morphism universes is imposed. The indexing universe is u+1 on both sides; there
is no restriction to countable sums. For J any supplied right adjoint, its exact
underlying ambient functor remains the one transported in b.

Searches before introducing the interfaces:

- `msearch.py ... leanfinder` with query "Adic proper pushforward identifies bounded
  constructible and finite Tor localizing hulls and transports the compact support
  adjunction": eight hits, including ordinary `Scheme.Modules.pushforward` and
  `SheafOfModules.pushforwardPushforwardAdj`; none states this comparison.
- `msearch.py ... leansearch` with query "Localizing closure of finite Tor constructible
  complexes agrees with bounded constructible complexes for adic coefficients":
  eight hits, mostly ring adic completion and topological constructibility; no match.
- `msearch.py ... loogle` with query
  `CategoryTheory.ObjectProperty.fullSubcategoryCongr, CategoryTheory.Adjunction.ofNatIsoLeft`:
  zero hits. Direct source inspection finds the genuine generic `ofNatIsoLeft` and
  `homEquiv_ofNatIsoLeft_apply`, already recorded as the proof dependency; these do
  not state the geometric hull comparison.
- `msearch.py ... grep` query `fullSubcategoryCongr|equivalenceOf|ofEq` in
  `CategoryTheory/ObjectProperty`: zero hits. Direct Mathlib source search finds
  `ObjectProperty.ιOfLE`, its full-faithfulness and `ιOfLECompιIso`, which are reused.
- `rg` across `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for `adicProperLocalizingAdjunction`, `localizingClosureProEtaleOfSize`, and this
  item's id found no existing statement. Broader searches for adic comparisons,
  localizing hulls and proper compactification comparisons found the dependencies
  listed above, which are reused. Searches for `localizingLowerShriek` found the
  existing restriction with fixed old hulls, not the needed indexing interface.
- The two new definition names were checked against the project and Mathlib source;
  neither existed. They specialize existing definitions; no new mathematical notion
  or second definition of constructibility, a derived functor, or a generic hull is
  introduced. Searches for proper identity comparisons located the existing
  `derivedOpenImmersionLowerShriekId`, used directly in the main statement.

No STATEMENT-DISPUTED flag or source-based statement correction is needed.

## New nodes

`def-sfb-compactification-refinement-component` is an `existing: true` binding to
`AlgebraicGeometry.ProEtale.CondensedRing.compactificationRefinementComponent`
in `Sheaf.Paper.CompactificationCoherenceCocycle`. Its source is the canonical
compactification comparison used in part (1) of
`sk-cor-existence-ii-restriction.proof.md`, with the component formula read in
`CompactificationCoherenceCocycle.lean:66`. It records exactly Rp_* of the canonical
open-adjunction map, then the inverse compositor, then the structural equality.
The node cites the three definition nodes named in the return. The arrow goes
from the target compactification to the refining one; density is not needed.
No theorem or invertibility claim is included in this definition node.

`def-sfb-derived-open-lower-shriek-id` is an `existing: true` binding to
`AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId`
in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek`.
It also owns the companion underived `openImmersionLowerShriekId`. Its source is
part (1) of the same blueprint proof, the sentence j=id and j_!=id. The definition
specifies the actual unique-adjoint comparison followed by exact levelwise derivation
and the derived identity comparison. It uses the existing extension-by-zero and
derived-category definition nodes. No arbitrary identity isomorphism is substituted.

`def-sfb-finite-tor-localizing-closure-of-size` owns
`Sheaf.Paper.FiniteTorLocalizingClosureOfSize` and its sole definition
`AlgebraicGeometry.ProEtale.finiteTorLocalizingClosureOfSize`. Its source is
`sk-def-localizing-closure/_section.md`, the intersection with the fixed direct-sum
index universe made explicit. The generic `localizingClosureOfSize` already exists;
this is its specialization to exactly the existing constant-model bounded
constructible finite-Tor object property. The new definition keeps w independent
and the item specializes it to u+1. The old `sk-def-localizing-closure` record is
unchanged. No alternate constructibility or ambient derived category is defined.

`def-sfb-finite-tor-localizing-lower-shriek-of-size` owns
`Sheaf.Paper.FiniteTorLocalizingLowerShriekOfSize` and its sole definition
`AlgebraicGeometry.ProEtale.CondensedRing.finiteTorLocalizingLowerShriekOfSize`.
Its source is the displayed compact-support functor in `sk-prop-sf-existence/_section.md`.
The definition is `ObjectProperty.lift` of the actual compactification composite,
on the preceding explicit-size hulls, using the supplied membership proof only.
It defines neither an adjoint nor an existence theorem. The old `sk-prop-sf-existence`
record remains `existing: true` on `exists_localizingExceptionalAdjoint`.

For each of these four nodes the recorded LeanSearch, LeanFinder and Mathlib grep
queries were run again during this repair; `mathlib_searches` preserves the actual
hit counts and returned names from `searches.jsonl`. Each semantic search returned
eight hits, none the specific definition. The four Mathlib grep queries returned
zero hits. Additional `rg` searches of `lean/WeilConjectures`, `lean/Sheaf`,
`dag/lean_names_upstream.json` and `dag/nodes` found the two canonical definitions
at the locations above, without a definition node owning either. They found no
existing explicit-size specialization. Blueprint searches for "refinement component",
"identity extension by zero", "extension by zero along the identity", and
"specified coproduct universe" returned zero nodes; "localizing closure" returned
22 general or theorem nodes, including the original generic closure definition,
with no separate explicit-size specialization. The source definitions are reused,
not copied. `blueprint_refs.py ancestor` returns None for this item, as its own
blueprint metadata already records: the new nodes inherit that null ancestor and
prepend the item to its existing via chain. Each new node's place identifies the
precise proper-comparison clause it serves.

## Returned findings repaired

H2 and the mechanical ownership finding: removed the added theorem node
`det-sf-comp-coherence-cocycle` from the item's statement dependencies. Added the
new definition node owning the exact existing refinement component, with all three
requested definition dependencies. Added the node owning both identity-normalization
definitions. Both are cited directly by the item. The existing canonical-map modules
are imported and are not copied or edited.

H13: removed the sandbox override of `sk-prop-sf-existence`; the live
`existing: true` theorem binding is preserved. The size-specific restriction is now
owned by its own definition node, cited by the item. Also followed the advisory:
the size-specific closure now has a definition node of its own and the override of
`sk-def-localizing-closure` is removed. Their Lean bodies are unchanged. Main-module
imports now name the live existence module directly; the helper module imports only
the ambient lower-shriek definition it needs, instead of that theorem module.

## Second reading by Q120

Author's consistency check, not an independent review: re-read the item, all three
files, and all four new definition nodes after repairing the returned findings. Each geometric and coefficient hypothesis is explicit; B=C and L=H use the
same ambient object type; the two inclusion equations and bounded inclusion square
are present; the fixed compactification and actual Rg_* are used; the canonical
refinement normalization determines e; and the final Hom equality applies a to
h∘e with the original J. The initial conditional scheme selector required
unavailable decidable equality, so it was replaced by uniform witnesses `hB` and
`hL` for the two schemes. The identity boundary object's quasi-compactness now uses
the explicit identity-morphism instance, avoiding typeclass reduction through an
opaque compactification. These are elaboration repairs, with no mathematical
statement change. The independent review is the maintainer's, as required by the
dispatch brief.

The new refinement node matches each factor of `compactificationRefinementComponent`:
`localizingRefinementMap`, inverse `refinementDerivedLowerStarComp`, and the
`eqToIso` for `hom_g`. The identity node matches the two defining expressions in
the upstream source; both work for an empty scheme and zero objects. The closure
node matches the exact generator intersection and free universe w. The restriction
node matches both `.obj` and `.map` of the existing ambient composite and has only
a preservation proof argument. Both size definitions have real data and no postponed
proofs. The generic localizing and Brown-existence nodes are unchanged on the base.
This author check is not presented as an independent review; the maintainer performs
that review under the dispatcher brief.

The initial saved packet passed the requested dry run at 67c9ba2ad04. That mechanical
pass did not resolve the independent return, so the ownership repairs above were
performed before redelivery. Final compile and dry-run outcomes are recorded below.

Final repair validation (2026-10-22): all three delivered modules compiled cleanly
through `scompile.py`, individually and in dependency order, against the live
published build. Final library compilations took 16.7 s, 12.2 s, and 13.0 s,
respectively. No compiler errors or additional warnings were reported. Local
packet comparison confirmed that only `lean` and `stmt_deps` change on the item,
that the original statement/proof/proof_deps are identical, and that there is one
`sorry` in the theorem and none in either helper. The two existing canonical-map
bindings introduce no new Lean declarations.
