## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSupportPlusAdjunction` constructs the
ordinary bounded-below closed-support right adjoint and its fixed adjunction.
All seven declarations contain actual data. No theorem, axiom or `sorry` is added.
The item's node is copied with only its `lean` field changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite commutative coefficient ring is `A : Type (u + 1)` with
  `[CommRing A] [Finite A]`. This is the existing etale coefficient size
  convention and includes the zero ring; finiteness is retained although the
  construction works more generally.
- The schemes are `{Z T : Scheme.{u}}`; the closed immersion is
  `(i : Z ⟶ T) [IsClosedImmersion i]`.
- The open complement is the actual open subset `(Set.range i.base)ᶜ`, with
  openness supplied by `IsClosedImmersion.isClosedEmbedding`. Its inclusion is
  `(closedSupportOpenComplement i).ι`. This is constructed from `i`, so no
  extra choice of complement or hypothesis is imposed.
- The categories are exactly `_root_.DerivedCategory.Plus (Sheaf
  T.smallEtaleTopology (ModuleCat.{u + 1} A))` and the same category for `Z`,
  as recorded by `def-weil-pbc-derived-categories`. They are ordinary derived
  categories of all module sheaves, without constructibility, torsion,
  dimension, regularity, characteristic or Noetherian restrictions.
- The left functor is the recorded bounded-below right derived direct image
  `rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) i`. Its definition is
  `(lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus`.
- `closedSupportPlus A i` is the actual
  `(closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorPlus`,
  where `j` is the canonical complementary open inclusion. In the published
  source, `closedUpperShriek` is `sectionsWithSupport ⋙ upperStar`, and
  `sectionsWithSupport` has objects `kernel (η_j.app N)` and morphisms the
  canonical `kernel.map`. Thus it is precisely `i⁻¹ ker(F → j_*j⁻¹F)` with
  the induced module structure, not another right-adjoint functor chosen
  from a bare existence assertion. Mathlib's derived functor is a left Kan
  extension, with its comparison unit and uniqueness property, and is
  computed on bounded-below injective complexes.
- `closedSupportPlusAdjunction A i` derives the published
  `lowerStarClosedUpperShriekAdjunction`. Its underived Hom bijection
  factors maps through the support kernel, applies the canonical closed
  unit and full faithfulness, with the inverse given by pushforward,
  inverse closed unit and kernel inclusion. This is already constructed
  for arbitrary Grothendieck abelian coefficients, so the specialization to
  `ModuleCat A` has genuinely linear maps. No new scalar-lift theorem is
  needed. `Adjunction.derivedPlus` derives this actual adjunction;
  `ofNatIsoLeft` transports its left side from exact termwise direct image
  to right derived direct image using
  `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm`. This is the
  derived-functor universal comparison, rather than an arbitrary isomorphism.
- `closedSupportPlusUnit` and `closedSupportPlusCounit` are literally `.unit`
  and `.counit` of that fixed adjunction. The triangle identities and natural
  Hom bijections are part of the reused `Adjunction` data.
- `closedSupportDirectImagePlusCommShift` transports the existing termwise
  exact-functor shift structure along that same universal comparison.
  `closedSupportPlusCommShift` uses this precise structure in a local
  `letI` and applies `Adjunction.rightAdjointCommShift` to the fixed
  adjunction. It supplies all shift isomorphisms, zero/addition coherence,
  and the mate normalization for the actual unit and counit, rather than
  accepting unspecified shift data. The named structures can be installed
  by a consumer with `letI`; no global competing instance is installed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` and its closed embedding field.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  the recorded category encoding; the actual categories here use Mathlib's
  `DerivedCategory.Plus` on the recorded etale module-sheaf category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStarLowerStarAdjunction`.
  The recorded `rightDerivedLowerStarPlus` actually lives in the public
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` module;
  that module is imported explicitly.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`, the recorded
  unbounded existence interface, imported as required. The construction
  here uses the stronger explicit upstream construction, not a choice from
  this existential interface.
- `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`:
  `supportedKernel`, `supportedClosedInverseImage`,
  `supportedKernel_closedAdjunction`. These are the recorded abelian-sheaf
  notion and adjunction. The module imports the already published generic
  coefficient version in
  `WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek`:
  `sectionsWithSupport`, `closedUpperShriek`,
  `lowerStarClosedUpperShriekHomEquiv`, and
  `lowerStarClosedUpperShriekAdjunction`. We reuse that existing module
  specialization instead of duplicating a support kernel for modules.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `CategoryTheory.Adjunction.derivedPlus`. The canonical unit and counit
  are characterized on bounded-below complexes by its `_unit_app_fac` and
  `_counit_app_fac` declarations.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `CategoryTheory.Functor.rightDerivedFunctorPlus` and its unit and
  `IsRightDerivedFunctor` instance, the recorded injective derivation node.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`:
  `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`, fixing agreement
  with exact direct image by the universal comparison.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryPlus` and its `CommShift` structure, induced from
  exact termwise functors.
- `Mathlib.CategoryTheory.Shift.Adjunction`:
  `Adjunction.rightAdjointCommShift`, `commShift_of_leftAdjoint` and
  `CommShift.compatibilityUnit_right`/`compatibilityUnit_unique_right`.
  `Mathlib.CategoryTheory.Shift.CommShift`: `Functor.CommShift.ofIso`.
- Recorded proof imports are retained: `Sheaf.CategoryTheory.RingedSiteModules`
  (`ringedSiteModules`), `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
  (`Scheme.etaleModule_enoughInjectives`), Mathlib's injective derivability
  and K-injective Hom modules, exact derived functor module, and the upstream
  `RightDerivedFunctor.Comp` (`Adjunction.preservesKInjectiveComplexes`) and
  `HomotopyCategory.Adjunction` (`Adjunction.mapHomotopyCategory`). The
  construction uses the published Grothendieck-abelian module-valued sheaf
  instances to supply enough injectives in this encoding, rather than
  constructing a second category from the older constant-ring-sheaf encoding.

Edge cases checked before writing: `Z` empty gives the right adjoint into the
zero closed category; `Z = T` has empty open complement and the support functor
identifies with the identity; the zero coefficient ring gives zero module
categories. Nonreduced closed subschemes are allowed because the sheaf
adjunction uses the small etale site, not reduced scheme data. There is no
uniform lower bound imposed: each input in `D⁺` has its own bound and the
termwise additive supported functor preserves the zero terms below that bound.
All integer shifts, including zero and negative shifts, are covered by
`CommShift ℤ`. The source and target coefficient/sheaf universes follow the
recorded `u + 1` convention without equating independent site universes.

Searches made with the prescribed `msearch.py Q18 <item>` wrapper:

- LeanFinder: "bounded below derived closed support right adjoint to direct
  image of a closed immersion of schemes with finite ring coefficients".
  Eight hits, including `Scheme.kerAdjunction`, module pushforward right
  adjoints, and closed immersion definitions; none is this bounded-below
  supported derived adjunction with fixed mate shifts.
- Loogle: `CategoryTheory.Adjunction.rightAdjointCommShift`.
  Three hits: the shift structure construction, compatibility theorem and
  comparison-isomorphism formula. Reused the construction directly.
- Mathlib grep: `closedSupportPlus|closedUpperShriek|sectionsWithSupport`.
  Zero hits.
- LeanSearch: "Right derived sections supported on a closed subscheme are
  right adjoint to exact direct image on bounded below derived categories
  of etale module sheaves". Eight hits about ordinary module pushforward,
  pullback and adjunctions; none gives this specialized construction.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `closedSupportPlus|closedSupportPlusAdjunction`, and the required item-id
  search in `lean/WeilConjectures`: no active occurrence. Searches for
  `closedUpperShriek` found the explicit generic supported construction and
  the unbounded adjunction described above. Searches for
  `rightDerivedFunctorPlus`/`derivedPlus` found the generic bounded-below
  adjunction API. Those building blocks are reused; there is no existing
  specialized `D⁺` definition with the requested complete fixed data.

Source checked: local Stacks `etale-cohomology.tex` at the supported-sheaf
construction immediately before `lemma-sections-with-support-acyclic` and its
proof (Tag 09XQ); current `literature/blueprint/latest/blueprint/` proof of
`lem-exc-closed-ambient`. Read the resolved Q84 repair note and its route
record. This delivery reconstructs only the re-admitted finite-coefficient
interface. It restores no old deleted module or discarded Artin-Gabber route,
uses no SGA source, and adds no statement change or new DAG node.

Validation: `scompile.py` compiled this module in sandbox and library mode.
The first pass reported only class-definition reducibility warnings; both
named shift structures were marked `@[instance_reducible]` and the second
pass compiled cleanly (12.0 s sandbox, 2.4 s library). All variables and
universes are explicitly bound; `autoImplicit` is false. No unresolved fault
or disputed statement was found.

## Second reading by Q18

This is the same worker's second pass, with both the node and file open;
the dispatcher forbids starting another agent, and the maintainer supplies
independent review after delivery. No independent reviewer is claimed here.

Rechecked the finite commutative ring, both schemes, closed immersion,
canonical open complement, ordinary `D⁺` categories, the recorded derived
direct image, supported-kernel construction, fixed adjunction, its exact
unit and counit, and all shift comparisons against the node. In particular,
`closedSupportPlus` is `R⁺` of an explicit functor, and the adjunction is the
derived actual supported Hom bijection. The left comparison's orientation
is `mapDerivedCategoryPlus ≅ rightDerivedFunctorPlus`, as needed by
`ofNatIsoLeft`. The shift structure uses that same comparison, and its mate
uses that same adjunction. No unspecified functor, arbitrary isomorphism,
additional boundedness assumption or missing shift clause was found.
The only changes during checking were the two instance-reducibility
attributes and explicit proof-plan imports; the mathematical statement was
unchanged. Helper definitions belong to this node's construction and are
all listed in `lean.declarations`, with source/blueprint docstrings.
