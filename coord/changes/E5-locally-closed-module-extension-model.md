# AlgebraicGeometry.Scheme.LocallyClosedCoefficients, LocallyClosedCoefficientImmersion, and normalization fields

## Reason

The fixed construction and its geometric comparison obligations must import the coefficient parameter definitions without importing the theorem being proved. Move only these definitions into the new data module, preserving their names, universes, attributes, signatures and bodies verbatim. The item publicly reexports that module. LocallyClosedExtensionData and its existing declarations remain in the item. Their open, closed, and binary normalization proof fields now use transparent named predicates with definitionally identical formulas. This avoids expensive kernel conversion through concrete sheaf functors; it changes no binder, mathematical statement, or data field. New model instances have new names and live in their own module. No source-library file is edited.

## Old

In lean/Sheaf/AlgebraicGeometry/LocallyClosedModuleExtensionCoherence.lean:

```lean
/-- A Noetherian scheme with an arbitrary commutative coefficient sheaf; a bundle of
parameters for the coherence assertion, not an additional hypothesis on coefficients.
Source: Stacks, Tags 01OV and 09A5
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure LocallyClosedCoefficients where
  scheme : Scheme.{u}
  locallyNoetherian : IsLocallyNoetherian scheme
  compact : CompactSpace scheme
  ring : Sheaf (ProEt.topology scheme) CommRingCat.{u + 1}

attribute [instance] LocallyClosedCoefficients.locallyNoetherian
  LocallyClosedCoefficients.compact

/-- A locally closed immersion with its inverse-image coefficient identification.
Taking the source ring literally to be inverse image is the special case `Iso.refl`;
allowing its identified presentation permits composition without silently equating rings.
Source: Stacks, Tags 01IO and 03D2
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure LocallyClosedCoefficientImmersion (S X : LocallyClosedCoefficients.{u}) where
  hom : S.scheme ⟶ X.scheme
  immersion : IsImmersion hom
  coefficient : (proEtaleSheafInverseImage hom CommRingCat.{u + 1}).obj X.ring ≅ S.ring

attribute [instance] LocallyClosedCoefficientImmersion.immersion

namespace LocallyClosedCoefficientImmersion

/-- Identity with the actual identity inverse-image comparison.
Source: Stacks, Tag 09A5 (blueprint: lem-sfb-locally-closed-extension-coherence). -/
def identity (X : LocallyClosedCoefficients.{u}) : LocallyClosedCoefficientImmersion X X where
  hom := 𝟙 X.scheme
  immersion := inferInstance
  coefficient := (proEtaleRingInverseImageId X.scheme).app X.ring

/-- Composition with the actual composition of inverse-image coefficient identifications.
Source: Stacks, Tags 02V0 and 03D8
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def comp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    LocallyClosedCoefficientImmersion T X where
  hom := b.hom ≫ a.hom
  immersion := inferInstance
  coefficient := proEtaleRingCompositeCoefficients b.hom a.hom X.ring S.ring T.ring
    a.coefficient b.coefficient

/-- Exact inverse image with the specified inverse-image coefficients.
Source: Stacks, Tag 03D2 (blueprint: lem-sfb-locally-closed-extension-coherence). -/
abbrev pull {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModulePullback a.hom X.ring S.ring a.coefficient

/-- Actual direct image with action through the coefficient adjunction unit.
Source: Stacks, Tag 03D3 (blueprint: lem-sfb-locally-closed-extension-coherence). -/
abbrev push {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModuleDirectImage a.hom X.ring S.ring a.coefficient

/-- The canonical inverse-image composition, fixed by the sectionwise fibre-product map.
Source: Stacks, Tag 03D8 (blueprint: lem-sfb-locally-closed-extension-coherence). -/
def pullComp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    (a.comp b).pull ≅ a.pull ⋙ b.pull :=
  exchangeModuleComposition b.hom a.hom X.ring S.ring T.ring a.coefficient b.coefficient

end LocallyClosedCoefficientImmersion

```

The original extension-data and coherence declarations are:

```lean
/-- Witnesses for the exact module extensions in the assertion. The open adjunction and
closed counit normalize restriction. The coefficients of every arrow are inverse images.
Source: Stacks, Tags 09AA, 09BM, 09BN, 03DI and 03DJ
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure LocallyClosedExtensionData where
  extension : ∀ {S X : LocallyClosedCoefficients.{u}}, LocallyClosedCoefficientImmersion S X →
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  additive : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (extension a).Additive
  finiteLimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteLimits (extension a)
  finiteColimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteColimits (extension a)
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), extension a ⋙ a.pull ≅ 𝟭 _
  openAdjunction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsOpenImmersion a.hom),
    extension a ⊣ a.pull
  openNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsOpenImmersion a.hom)
    (M : proEtaleRingModules S.scheme S.ring),
    (openAdjunction a ha).unit.app M ≫ (restriction a).hom.app M = 𝟙 M
  closedComparison : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsClosedImmersion a.hom),
    extension a ≅ a.push
  closedNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsClosedImmersion a.hom)
    (M : proEtaleRingModules S.scheme S.ring),
    (restriction a).hom.app M = a.pull.map ((closedComparison a ha).hom.app M) ≫
      (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit.app M
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    extension b ⋙ extension a ≅ extension (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u},
    extension (.identity X) ≅ 𝟭 (proEtaleRingModules X.scheme X.ring)

attribute [instance] LocallyClosedExtensionData.additive LocallyClosedExtensionData.finiteLimits
  LocallyClosedExtensionData.finiteColimits

namespace LocallyClosedExtensionData

/-- The actual termwise extension on the ordinary unbounded derived categories.
Source: Stacks, Tags 015F and 05RU
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
abbrev derived (E : LocallyClosedExtensionData.{u}) {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) := (E.extension a).mapDerivedCategory

/-- The specified closed-then-open factorization of extension. Its open factor is the
left adjoint to actual inverse image from `openAdjunction`, hence the sheafified
extension-by-zero presheaf; its closed factor is actual direct image.
Source: Stacks, Tags 03DI, 09AA and 09BN
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def closedOpenFactorization (E : LocallyClosedExtensionData.{u})
    {S V X : LocallyClosedCoefficients.{u}} (v : LocallyClosedCoefficientImmersion V X)
    (c : LocallyClosedCoefficientImmersion S V) (hc : IsClosedImmersion c.hom)
    (_hv : IsOpenImmersion v.hom) :
    E.extension (v.comp c) ≅ c.push ⋙ E.extension v :=
  (E.gamma v c).symm ≪≫ Functor.isoWhiskerRight (E.closedComparison c hc) (E.extension v)

/-- The specified opposite factorization, with open followed by closed. This uses
exactly the same normalized composition comparison, including the mixed case.
Source: Stacks, Tags 02V0 and 09AH
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def openClosedFactorization (E : LocallyClosedExtensionData.{u})
    {S Z X : LocallyClosedCoefficients.{u}} (i : LocallyClosedCoefficientImmersion Z X)
    (j : LocallyClosedCoefficientImmersion S Z) (hi : IsClosedImmersion i.hom)
    (_hj : IsOpenImmersion j.hom) :
    E.extension (i.comp j) ≅ E.extension j ⋙ i.push :=
  (E.gamma i j).symm ≪≫ Functor.isoWhiskerLeft (E.extension j) (E.closedComparison i hi)

/-- Comparison of any two closed-then-open factorizations with the same composite
coefficient identification. In a coherent system its restriction is the identity,
and it is the unique isomorphism with that normalization by `Coherent.homBijection`.
Source: Stacks, Tags 02V0 and 09AH, the intersection-and-shrinking argument
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def factorizationComparison (E : LocallyClosedExtensionData.{u})
    {S V V' X : LocallyClosedCoefficients.{u}} (v : LocallyClosedCoefficientImmersion V X)
    (c : LocallyClosedCoefficientImmersion S V) (v' : LocallyClosedCoefficientImmersion V' X)
    (c' : LocallyClosedCoefficientImmersion S V')
    (hc : IsClosedImmersion c.hom) (hv : IsOpenImmersion v.hom)
    (hc' : IsClosedImmersion c'.hom) (hv' : IsOpenImmersion v'.hom)
    (h : v.comp c = v'.comp c') :
    c.push ⋙ E.extension v ≅ c'.push ⋙ E.extension v' :=
  (E.closedOpenFactorization v c hc hv).symm ≪≫ eqToIso (congrArg E.extension h) ≪≫
    E.closedOpenFactorization v' c' hc' hv'

/-- Normalized comparison laws on module sheaves. The two factorization orders follow
by composing `gamma` with `closedComparison` and the open adjunction; normalization
and the Hom bijection make the comparison between any two factorizations unique.
Source: Stacks, Tags 02V0 and 09AH, composite consequence described in the node proof
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure Coherent (E : LocallyClosedExtensionData.{u}) : Prop where
  full : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (E.extension a).Full
  faithful : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), (E.extension a).Faithful
  homBijection : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (M N : proEtaleRingModules S.scheme S.ring),
    Function.Bijective (fun f : (E.extension a).obj M ⟶ (E.extension a).obj N ↦
      (E.restriction a).inv.app M ≫ a.pull.map f ≫ (E.restriction a).hom.app N)
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring),
    (a.comp b).pull.map ((E.gamma a b).hom.app M) ≫ (E.restriction (a.comp b)).hom.app M =
      (a.pullComp b).hom.app ((E.extension a).obj ((E.extension b).obj M)) ≫
        b.pull.map ((E.restriction a).hom.app ((E.extension b).obj M)) ≫
          (E.restriction b).hom.app M
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      E.gamma a (.identity S) ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerRight (E.identity S) (E.extension a) ≪≫
          Functor.leftUnitor (E.extension a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.gamma (.identity X) a ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerLeft (E.extension a) (E.identity X) ≪≫
          Functor.rightUnitor (E.extension a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.gamma b d) (E.extension a) ≪≫ E.gamma a (b.comp d) =
        Functor.associator (E.extension d) (E.extension b) (E.extension a) ≪≫
          Functor.isoWhiskerLeft (E.extension d) (E.gamma a b) ≪≫ E.gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.extension h)

/-- The normalized composition laws for an exact extension system. Full faithfulness
and the restriction Hom bijection are consequences of the separate open and closed
adjunctions and a closed/open factorization, and are proved in the importing module.

Source: Stacks, Tags 02V0 and 09AH, the shrinking and support-reconstruction argument
(blueprint: lem-sfb-locally-closed-module-extension-coherence). -/
structure NormalizedComposition (E : LocallyClosedExtensionData.{u}) : Prop where
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring),
    (a.comp b).pull.map ((E.gamma a b).hom.app M) ≫ (E.restriction (a.comp b)).hom.app M =
      (a.pullComp b).hom.app ((E.extension a).obj ((E.extension b).obj M)) ≫
        b.pull.map ((E.restriction a).hom.app ((E.extension b).obj M)) ≫
          (E.restriction b).hom.app M
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      E.gamma a (.identity S) ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerRight (E.identity S) (E.extension a) ≪≫
          Functor.leftUnitor (E.extension a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.gamma (.identity X) a ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerLeft (E.extension a) (E.identity X) ≪≫
          Functor.rightUnitor (E.extension a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.gamma b d) (E.extension a) ≪≫ E.gamma a (b.comp d) =
        Functor.associator (E.extension d) (E.extension b) (E.extension a) ≪≫
          Functor.isoWhiskerLeft (E.extension d) (E.gamma a b) ≪≫ E.gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.extension h)

end LocallyClosedExtensionData
```

## New

The exact block above now occurs in lean/Sheaf/AlgebraicGeometry/LocallyClosedModuleExtensionData.lean. The original module contains:

```lean
public import Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionData
```

Every declaration in the Old block is unchanged. The new fixed model is modelExtension: actual closed direct image followed by the constructed exact open extension. Its modelRestriction uses the inverse open unit and actual closed counit. Its modelExtension and modelRestriction definitions are irreducible to keep assembly from unfolding their constructions. Their API is provided by named exactness and full-faithfulness instances.

The new model uses `ModelPresentation` with an equality to the explicit closed-then-open
functor. Its nonemptiness theorem is proved by that composite and reflexivity, so its
selected data is determined by a proved equality. `modelExtension_eq` transfers the
properties and restriction comparison without kernel unfolding of sheaf object data.

The same extension-data and coherence declarations, with the normalization formulas named:

```lean
/-- Witnesses for the exact module extensions in the assertion. The open adjunction and
closed counit normalize restriction. The coefficients of every arrow are inverse images.
Source: Stacks, Tags 09AA, 09BM, 09BN, 03DI and 03DJ
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure LocallyClosedExtensionData where
  extension : ∀ {S X : LocallyClosedCoefficients.{u}}, LocallyClosedCoefficientImmersion S X →
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  additive : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (extension a).Additive
  finiteLimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteLimits (extension a)
  finiteColimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteColimits (extension a)
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), extension a ⋙ a.pull ≅ 𝟭 _
  openAdjunction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsOpenImmersion a.hom),
    extension a ⊣ a.pull
  openNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsOpenImmersion a.hom),
    LocallyClosedOpenNormalization (extension a) a.pull (restriction a) (openAdjunction a ha)
  closedComparison : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsClosedImmersion a.hom),
    extension a ≅ a.push
  closedNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsClosedImmersion a.hom),
    LocallyClosedClosedNormalization (extension a) a.push a.pull (restriction a)
      (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit
      (closedComparison a ha)
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    extension b ⋙ extension a ≅ extension (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u},
    extension (.identity X) ≅ 𝟭 (proEtaleRingModules X.scheme X.ring)

attribute [instance] LocallyClosedExtensionData.additive LocallyClosedExtensionData.finiteLimits
  LocallyClosedExtensionData.finiteColimits

namespace LocallyClosedExtensionData

/-- The actual termwise extension on the ordinary unbounded derived categories.
Source: Stacks, Tags 015F and 05RU
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
abbrev derived (E : LocallyClosedExtensionData.{u}) {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) := (E.extension a).mapDerivedCategory

/-- The specified closed-then-open factorization of extension. Its open factor is the
left adjoint to actual inverse image from `openAdjunction`, hence the sheafified
extension-by-zero presheaf; its closed factor is actual direct image.
Source: Stacks, Tags 03DI, 09AA and 09BN
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def closedOpenFactorization (E : LocallyClosedExtensionData.{u})
    {S V X : LocallyClosedCoefficients.{u}} (v : LocallyClosedCoefficientImmersion V X)
    (c : LocallyClosedCoefficientImmersion S V) (hc : IsClosedImmersion c.hom)
    (_hv : IsOpenImmersion v.hom) :
    E.extension (v.comp c) ≅ c.push ⋙ E.extension v :=
  (E.gamma v c).symm ≪≫ Functor.isoWhiskerRight (E.closedComparison c hc) (E.extension v)

/-- The specified opposite factorization, with open followed by closed. This uses
exactly the same normalized composition comparison, including the mixed case.
Source: Stacks, Tags 02V0 and 09AH
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def openClosedFactorization (E : LocallyClosedExtensionData.{u})
    {S Z X : LocallyClosedCoefficients.{u}} (i : LocallyClosedCoefficientImmersion Z X)
    (j : LocallyClosedCoefficientImmersion S Z) (hi : IsClosedImmersion i.hom)
    (_hj : IsOpenImmersion j.hom) :
    E.extension (i.comp j) ≅ E.extension j ⋙ i.push :=
  (E.gamma i j).symm ≪≫ Functor.isoWhiskerLeft (E.extension j) (E.closedComparison i hi)

/-- Comparison of any two closed-then-open factorizations with the same composite
coefficient identification. In a coherent system its restriction is the identity,
and it is the unique isomorphism with that normalization by `Coherent.homBijection`.
Source: Stacks, Tags 02V0 and 09AH, the intersection-and-shrinking argument
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def factorizationComparison (E : LocallyClosedExtensionData.{u})
    {S V V' X : LocallyClosedCoefficients.{u}} (v : LocallyClosedCoefficientImmersion V X)
    (c : LocallyClosedCoefficientImmersion S V) (v' : LocallyClosedCoefficientImmersion V' X)
    (c' : LocallyClosedCoefficientImmersion S V')
    (hc : IsClosedImmersion c.hom) (hv : IsOpenImmersion v.hom)
    (hc' : IsClosedImmersion c'.hom) (hv' : IsOpenImmersion v'.hom)
    (h : v.comp c = v'.comp c') :
    c.push ⋙ E.extension v ≅ c'.push ⋙ E.extension v' :=
  (E.closedOpenFactorization v c hc hv).symm ≪≫ eqToIso (congrArg E.extension h) ≪≫
    E.closedOpenFactorization v' c' hc' hv'

/-- Normalized comparison laws on module sheaves. The two factorization orders follow
by composing `gamma` with `closedComparison` and the open adjunction; normalization
and the Hom bijection make the comparison between any two factorizations unique.
Source: Stacks, Tags 02V0 and 09AH, composite consequence described in the node proof
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure Coherent (E : LocallyClosedExtensionData.{u}) : Prop where
  full : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (E.extension a).Full
  faithful : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), (E.extension a).Faithful
  homBijection : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (M N : proEtaleRingModules S.scheme S.ring),
    Function.Bijective (fun f : (E.extension a).obj M ⟶ (E.extension a).obj N ↦
      (E.restriction a).inv.app M ≫ a.pull.map f ≫ (E.restriction a).hom.app N)
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    LocallyClosedBinaryNormalization (E.extension a) (E.extension b) a.pull b.pull
      (a.comp b).pull (E.extension (a.comp b)) (E.restriction a) (E.restriction b)
      (E.restriction (a.comp b)) (a.pullComp b) (E.gamma a b)
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      E.gamma a (.identity S) ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerRight (E.identity S) (E.extension a) ≪≫
          Functor.leftUnitor (E.extension a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.gamma (.identity X) a ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerLeft (E.extension a) (E.identity X) ≪≫
          Functor.rightUnitor (E.extension a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.gamma b d) (E.extension a) ≪≫ E.gamma a (b.comp d) =
        Functor.associator (E.extension d) (E.extension b) (E.extension a) ≪≫
          Functor.isoWhiskerLeft (E.extension d) (E.gamma a b) ≪≫ E.gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.extension h)

/-- The normalized composition laws for an exact extension system. Full faithfulness
and the restriction Hom bijection are consequences of the separate open and closed
adjunctions and a closed/open factorization, and are proved in the importing module.

Source: Stacks, Tags 02V0 and 09AH, the shrinking and support-reconstruction argument
(blueprint: lem-sfb-locally-closed-module-extension-coherence). -/
structure NormalizedComposition (E : LocallyClosedExtensionData.{u}) : Prop where
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    LocallyClosedBinaryNormalization (E.extension a) (E.extension b) a.pull b.pull
      (a.comp b).pull (E.extension (a.comp b)) (E.restriction a) (E.restriction b)
      (E.restriction (a.comp b)) (a.pullComp b) (E.gamma a b)
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      E.gamma a (.identity S) ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerRight (E.identity S) (E.extension a) ≪≫
          Functor.leftUnitor (E.extension a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.gamma (.identity X) a ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerLeft (E.extension a) (E.identity X) ≪≫
          Functor.rightUnitor (E.extension a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.gamma b d) (E.extension a) ≪≫ E.gamma a (b.comp d) =
        Functor.associator (E.extension d) (E.extension b) (E.extension a) ≪≫
          Functor.isoWhiskerLeft (E.extension d) (E.gamma a b) ≪≫ E.gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.extension h)

end LocallyClosedExtensionData
```

The four transparent predicates `LocallyClosedOpenNormalization`,
`LocallyClosedClosedNormalization`, `LocallyClosedObjectNormalization`, and
`LocallyClosedBinaryNormalization` expand to the original unit, counit, objectwise
restriction, and binary restriction equations. Their definitions normalize only
`Functor.comp_obj` and `Functor.id_obj`. They introduce no hypothesis or data choice. `LocallyClosedCompositeRestrictionMap` is
the same explicit threefold composite on the right of the binary equation, named over
abstract functors so its source type is computed before specialization.

The normalization formulas and composite are defined as follows:

```lean
/-- The specified open unit is inverse to restriction.
Source: Stacks, Tags 03DI and 09BN
(blueprint: def-sfb-locally-closed-module-extension-data). -/
def LocallyClosedOpenNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (adj : F ⊣ L) : Prop :=
  ∀ M, dsimp% only [Functor.comp_obj, Functor.id_obj]
    adj.unit.app M ≫ r.hom.app M = 𝟙 M

/-- Restriction agrees with the specified closed counit after comparison.
Source: Stacks, Tag 09AA
(blueprint: def-sfb-locally-closed-module-extension-data). -/
def LocallyClosedClosedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C) (e : F ≅ P) : Prop :=
  ∀ M, dsimp% only [Functor.comp_obj, Functor.id_obj]
    r.hom.app M = L.map (e.hom.app M) ≫ d.app M

/-- The composite of the two restriction comparisons and inverse-image composition.
Source: Stacks, Tags 02V0 and 09AH
(blueprint: def-sfb-locally-closed-module-extension-data). -/
def LocallyClosedCompositeRestrictionMap
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb) (M : A) :
    Lab.obj (Ea.obj (Eb.obj M)) ⟶ M :=
  c.hom.app (Ea.obj (Eb.obj M)) ≫ Lb.map (ra.hom.app (Eb.obj M)) ≫ rb.hom.app M

/-- An objectwise comparison has a specified restriction.
Source: Stacks, Tags 02V0 and 09AH
(blueprint: def-sfb-locally-closed-module-extension-data). -/
def LocallyClosedObjectNormalization
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D) (L : D ⥤ C)
    (r : H ⋙ L ≅ 𝟭 C) {A : D} {M : C} (t : L.obj A ⟶ M) (e : A ≅ H.obj M) : Prop :=
  dsimp% only [Functor.comp_obj, Functor.id_obj]
    L.map e.hom ≫ r.hom.app M = t

/-- A natural binary comparison has the composite restriction normalization.
Source: Stacks, Tags 02V0 and 09AH
(blueprint: def-sfb-locally-closed-module-extension-data). -/
def LocallyClosedBinaryNormalization
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (H : A ⥤ C) (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A)
    (rh : H ⋙ Lab ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb) (e : Eb ⋙ Ea ≅ H) : Prop :=
  ∀ M, dsimp% only [Functor.comp_obj, Functor.id_obj]
    Lab.map (e.hom.app M) ≫ rh.hom.app M =
      LocallyClosedCompositeRestrictionMap Ea Eb La Lb Lab ra rb c M

```

`lean/Challenge.lean` and every target declaration are unchanged. The normalized
proof-field types are definitionally equal to their original types; the coefficient
parameter bodies are copied verbatim. No target receives a new mathematical hypothesis
or a different interpretation through this extraction.

## Users

The table includes every transitive downstream module returned by tools/downstream.py, hence includes all declaration users. All original public imports remain; parameter definitions and attributes are reexported verbatim. Thus none of these consumers needs an adaptation and none of its statements changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.KFlatBifunctorTensorHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Algebra.Homology.RingedForgetTensorTransposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceCentredChartConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceChartRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportCharacterization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportRows | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportStrict | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.EtaleScalarFlatModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.FrobeniusContractionScalarPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.NativeAdicAffineOpenZeroStratification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.SpP1BaseChangeOfNormalized | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.SpP1RationalPointChern | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.CategoryTheory.ConstantCoefficientScalarExtensionPresentations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.ConstantFieldRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.ConstantFieldRestrictionStalk | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.GeometricConstituentOrbit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.PoweredGeometricPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.PoweredGeometricPullbackStalk | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.SemisimpleFrobeniusOrbitDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.SimpleLisseSupportModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleScalarSectionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AcyclicFlatProperCoefficientModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicClosureScalarCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicCommonStageFibreTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicCommonStageFibreZeroMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicCommonStageHeartExactness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicFiniteRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicFiniteScalarCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicNormalizedFibreCommonStageData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityFiniteTensorComponents | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicPurityTwistRestrictionComponents | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicReindexingCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicReindexingHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdmissibleCupCoefficientPassages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | C1 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalDncCoordinateIdentity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalDncNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalPowerCoefficient | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalPresentedBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalRawTransposePower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalRestrictedTransposes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalSectionCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineDiagonalTransposePower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpacePurityCompositionMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpacePurityCoordinateInvariance | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpacePurityOrderedBlocks | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | E3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AllStageCtfPullbackUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BarrettIndRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BasicOperationCoefficientCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BasicOperationReductionAndEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryFiniteEvaluationRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryFiniteSiteData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryFiniteSiteRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryFiniteTorDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundedFlatCoefficientSiteSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundedSiteExchangeTransposes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BoundedSiteTensorTransposes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CanonicalTateComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CartierSupportedComparisonSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartDncNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartDncSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalFiltrationDiagramFibres | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalFiltrationExactDiagram | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | T6 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseCommonDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseFiniteOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRealizationLocalSpectrum | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRealizationPunctualPurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalWeilFiltrationTransportData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenStrictSystemSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClosedEmbeddingPerfectEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClosedScalarDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClosedSectionCompactOrigin | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClosedSectionCompactOriginData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClosedSectionSourceNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefDualizingClosedChart | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefFiniteHomSiteDescent | C5 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefFiniteSiteHomTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefSupportPointSectionsComparisonExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefSupportPointSectionsModelExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientDualizingOpenAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientDualizingOpenTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientTensorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStagePerfectEvaluationDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStagePointReturn | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactExchangeOperationCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportCoefficientExchangeInvertible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportCoefficientModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportCompletedProjectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportCompletedScalarArrow | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportExchangeDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportFiniteScalarMateNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportLimitEquationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportNormalizedScalarDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportPathReductionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportProjectionCoefficientChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | S3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportProjectionFiniteStages | T1 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportProjectionFormula | C3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | T2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportProjectionRightUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportRationalScalarIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportRealizationIdentity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportReductionAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportScalarShiftStructures | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportScalarShiftWitness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportSiteExchangeSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | M7 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportStrictScalarMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | X9 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportSystemTransposeNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportTermHomFinite | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportTotalLimitRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportTowerReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationBProjectionReduction | A3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationCompletedRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationFiniteProjectionModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationOpenLimit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationProjectionInverse | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationPushLimit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationScalarData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactificationStrictRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ComparisonImageClosedSectionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompleteIntegralConstantRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompleteProjectionReductionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompletedContinuousHomHypotheses | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompletedPullbackFractionDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompletedScalarAssociatorLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompletedScalarExactLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompositionComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CompositionTensorMate | G8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteOpenScalarTensorSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteProjectionCoefficientCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteProjectionFactorizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteProjectionReductionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteProperScalarTensorSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConcreteSupportScalarIsomorphism | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedTateIntegralTower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CondensedTateIntegralTowerData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantCompletedOrdinaryAssociativity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantCompletedScalarAssociativity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionCyclicSheetPartition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | U6 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionReturnData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionSheetTensorSplitting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionWeilHeartData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantScalarTowerAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstantScalarTowerMates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleCoefficientSiteSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientStages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalCompositorData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalLeftRefinements | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleExceptionalRefinementMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleLeftCompositorCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousAlgClFiniteStageDevissage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousAlgClProperScalarComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousAlgclScalarExtensionConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousQbarConstructibleGenerators | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousQbarNormalizedSheafFiltration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateAdjunctionComposition | E4 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateLineAdjunction | G9 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateSectionProductRecursion | Z6 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateSupportedProductRecursion | N1 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateTowerCompactTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateTowerExceptionalCompositors | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateTowerNormalizationFusion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CtfCoefficientStageSelectors | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | B7 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DerivedHomSubstitutionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DerivedScalarRestrictionPullbackMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DerivedTensorRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalAffineCounitRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalAffineIntegrationSiteSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalAffineRankZeroActual | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalAffineTraceMapAgreement | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalAffineTraceSiteData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalBaseSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientFamilyExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCoefficientUniformizerReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCompletedDiagramRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCompletedFrame | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalCompletedPushSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalFiniteRootMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalIntegralRootMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalNonTorsionBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalOrdinaryChartLift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalOrdinaryOverlap | R3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalQuotientBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTracePresentationExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTraceResultExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTraceSingleFaithful | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalTraceSources | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DiagonalUniformizerAnnihilator | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DifferenceFirstInputRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DifferenceSecondInputRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DirectImageHomEvaluationSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualizingClosedSite | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualizingCocycleSourceEtale | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualizingCompositionCoefficientMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualizingPrimitiveOpenRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleBrownCoefficientCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleBrownEvaluationMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleBrownGeometricComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleBrownLevelComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleBrownOpenSingletonEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleBrownProjectionRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleBrownProperSingletonEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleBrownSupportTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCoefficientProperCoproducts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCofinalSupportComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCofinalSupportRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCompactScalarBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCompactScalarCoherence | S2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCompositeEComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleDerivedScalarTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleDirectImageScalarComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | Y3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleLisseHomReduction | E8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleMiddleTensorAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleOpenScalarExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleOpenScalarExchangeSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleOriginScalarProjectionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleProEtaleCompactScalarSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleProEtaleScalarCounitTransposes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleProEtaleScalarMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleProEtaleScalarMateData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleProEtaleScalarPullbackCube | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleProperCoefficientTensorUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleQuotientTensorProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleScalarPullbackIdentityNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleScalarPullbackTensorCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleScalarPullbackUnitCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSingleCoefficientProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSumCoefficientComputation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSumScalarRepresentative | T4 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemBrownConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemCoefficientProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemCofinalData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemDerivedTensorEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemEvaluationBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemImageTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemProjectionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemProjectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemProjectionEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemProjectionExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemProjectionPresentationCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemQuotientNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemScalarMateCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleSystemTensorEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleTensorSourceTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EtaleTowerBrownAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EvenLineBinaryProductNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EvenLineCoordinateIntertwining | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EvenTateLineSelfSymmetry | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExactProperOpenProjectionMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalCoefficientLeftUnitCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalCoefficientMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalCoefficientUnitCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalFieldDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalFiniteIntrinsicBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalFiniteOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalFiniteScalarMates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalProOriginExactLinear | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalProperOpenOriginComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalSiteOriginComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalSystemInterfaces | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExceptionalSystemTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FdPullbackWeilReturnSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemComparison | M9 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemComponents | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldExceptionalSystemLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldProjectionOpenSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldProjectionOriginWitnesses | W8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldProjectionProperSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldProjectionRefinementSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldProjectionSystemData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldProjectionSystemSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldProjectionTensorConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekCompositionCoefficientSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekCompositionIntegralComponent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekCompositionIntegralNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekCompositionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemCocycle | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemMixed | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldShriekSystemTransitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientAdjointData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientHomChange | K1 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientIntrinsicChainTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientKFlatReflection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientSiteTensorNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientSiteTensorPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactSiteCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | F4 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFieldClosedSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFieldSheafScalarExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteForwardCompactifiedSwap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteForwardProductCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeCompactComposition | P8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeCompactSupportData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeDerivedScalarCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeHomEvaluationCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeHomLocalCalculation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeScalarCalculusData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeScalarDerivedComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeScalarDerivedTensorModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteFreeScalarTensorCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteHomDomainCalculus | E4 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteIdentityCompositionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteKernelConstructibleLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteLevelProjectionFactors | C2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteMateDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteOrientationReduction | E3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePointCounitUnitNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePointReconstructedEvaluationSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProductOpenRestrictionPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProductOrdinaryNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProjectionCompactificationSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProjectionPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteRingRelativeScalarComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSiteTowerPaste | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSiteWordRefinement | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteStageNormalizedAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteStageNormalizedChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteStageNormalizedCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSupportCompositorCoefficient | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSupportCompositorExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTateScalarSourceData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTateScalarSourceExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | V3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorSignedReduction | J2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | Y7 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTorStability | Z7 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTripleProductDefinitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTwistRootTrivialization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteWindow | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FreeInsertionCompactSupportCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | R9 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusSquareExchange | V4 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | F1 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GenericRetractSupportGluing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeometricGeneratorProjectionDevissage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeometricOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GermReparametrizationDerivedDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.HigherIdentityCompositionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IdentityCoefficientTransportData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IdentityOpenSystemEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralClosedSupportNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | C6 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralCompositionCoefficientSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralConstructibleReductionHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralDirectImageTowerData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralExceptionalInverseImage | J2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralFiniteScalarModelDefinitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralFiniteScalarPerfectModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralFiniteTopologicalPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralHomPresentationEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralLissePullbackNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralOpenEmptyPullbackVanishing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralOpenSupportNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralProjectionRefinementSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralPullbackAugmentationAmbient | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralReductionUnderlyingDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralSupportFunctorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralSupportLatticeReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralSupportNormalizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralTowerCompactificationCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralTowerGeometryLimits | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegralTowerPullTensorConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntegrationTransposeScalarMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | P9 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | W5 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.KummerStratumScalarMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.KummerStratumScalarMateDetection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LevelwiseNormalizedStrictSystems | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LineCounitComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LineKummerFieldRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LineZeroClassExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLatticeChoiceExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLatticeLisseDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLatticeSingleComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLocalizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLocalizationExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLocalizationLocalFreeness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLocalizationRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseLocalizationSlices | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusStepCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyClosedHomGenerator | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyClosedInternalAdjunctionIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyClosedOrdinaryComparisonIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyClosedPairingCancellation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyFiniteCoefficientRingRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.LocallyProjectiveCoefficientHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MateOpenCompactSupportExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MateOpenProperRestrictionIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MateOpenProperSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MateOpenRestrictionMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCompactSupportExchangeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupCoefficientData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeClosedTransposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeConstantSupportModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeEncodingDerivedOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeForgetConstructibleCriterion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeGeometricTensorComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeModuleConstructibilityComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeReductionCounitKFlat | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeScalarRestrictionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilClosedForgetful | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilClosedModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilFreeCoproduct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilHeartProperties | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilInductionSummands | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilProperNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilRowHomComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NativeWeilTensorTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedCommonCoefficientLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedEtaleComparisonComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedEtaleRestrictionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedPullbackCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedPullbackNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedPullbackObjects | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedRationalLeftLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedRingRefinementLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedSupportEtalePresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedTateTensorTower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.NormalizedVectorPurityScalarReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenScalarCounitSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenWeilCarrierRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenWeilCoefficientFibres | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenWeilFiniteStageFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenWeilGeometricFibres | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OpenWeilPunctualSpectrum | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OperationCoefficientActionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedAffineComparisonNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedAffineLineTransposeNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedAffineTransposeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedAffineTransposeSuccessor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedIntegrationComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrdinaryScalarBalancingLevel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrdinaryScalarReductionGenerators | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationCoordinateBoundaryPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationCoordinateModelBoundary | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationLocalResidue | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientationPerfectLines | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.OriginalScalarMateShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.P1CounitScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.P1KummerChernScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.P1KummerDerivedScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.P1KummerScalarEndpointComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.P1KummerScalarEndpointExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.P1KummerScalarEndpoints | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.P1KummerTraceSiteTransport | W8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.P1SplittingScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PairingData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodMixedSupportCupProduct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodReconstructionCommonStageData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | Y8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PodReconstructionScalarRealizations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | G7 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointIdentitySupportNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointPullbackConeLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointQuotientTowerHomotopy | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointRootLimitCyclotomicAction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointScalarPunctualSpectrum | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSignedCyclotomicAction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSignedCyclotomicActionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSignedCyclotomicScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemInsertionComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemRoosComparisonAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemRoosRestrictionAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemRoosTransportData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemRoosTransportRepresentative | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTateCommonStageCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTateDerivedComparisonCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTateFiberCanonicalComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTateFiberComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTateFiniteSectionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTateNormalizedSectionGenerators | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTransportResolutionCancellation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointWeilAlgebraicFlag | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointWeilHeartFlagData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductCompositionCoordinateComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductExchangeCoordinateDefinitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductHorizontalExchangeFactorization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductOpenAdjunctionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductOpenCounitNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductOpenSupportNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProductOpenTensorProjectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionCompactificationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionFactorCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionPurityAgreement | X3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionReductionWitnessedFlatDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionScalarSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionTensorCoefficientCocycles | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | J8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | R3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperAlgClComparisonDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperCoefficientDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperCoefficientDescentData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperCompactCoefficientActionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperCompactIntegralComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperCompactRationalFunctorComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperIntegralScalarSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperOpenCoefficientRefinement | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperRationalScalarSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperSupportCoefficientAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperSupportFiniteAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperSystemEvaluationTransitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurEtaleScalarMateProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurIntegralReductionUniformTor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurKFlatOpenModelMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurKFlatOpenProjectionModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityAffineLineOrientationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityCompositionComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PuritySectionBaseComparisonLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PuritySectionEtaleRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PuritySectionFibreSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PuritySectionNormalizedSpecialization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PuritySectionRestrictionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.QcqsCompactSupportFiniteComparison | X6 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.QcqsCompactSupportNormalizedLift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | B4 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalAffineTensorCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalAmbientPullComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalAmbientPullModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalBalancedFreePullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalContinuousComparisonCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalContinuousFiltrationModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalContinuousPullbackTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalCoverReflectsIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalEvaluationCover | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalPullSingleComputation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalRealizationHomTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalReturnBlockPower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalScalarBalancedLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalSmoothPurityCanonical | U7 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalStratumPullbackData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalStratumPullbackModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RealSheafSections | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RealWeights | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReconstructedBrownMateLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReconstructedPairRefinementData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReconstructedRefinementCommon | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReductionOpenEtaleOrigin | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RefinementCoefficientMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeKunnethClosedFibre | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeKunnethConstructions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeProductCoefficientFactorSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeProductFactorSquaresCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeProductFactors | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeProductProperCompatibilityCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SbcDatumExchangeComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarCompositeMateAdjunct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarFibreCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarFibreComponentData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarFibreComponents | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarFibreNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarHomPresentationEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarIteratedMatesAdjunct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarLimitConstraintShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarPullbackComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarPullbackIsoExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarPullbackIsoUniqueness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarPullbackRepresentativeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarReductionTowerBalancing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarSourceCounitUniversal | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarTargetCounitUniversal | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ScalarTensorPullbackNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionCompactSourceExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionCompactSourceMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionSourceEtaleExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionSourceProExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionSourceProExchangeConstantSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionSourceProExchangeTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionSupportedComparisonIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionSupportedProExchangeIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SectionsRationalModelComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearCommonOrdinaryCubes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearCommonRefinementCubes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearCommonSupportCubes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | K3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearExchangeCubeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearExchangeReindexing | U2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearRationalOrdinaryCubes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearRationalRefinementCubes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SemilinearRationalSupportCubes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfBcCompletedMateDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfCompletedExchangeTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfExactLocalizationTriangle | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfFieldMateDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfIntegralClosedKernelRoos | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfIntegralKernelRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfIntegralLocalizationConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfIntegralOpenKernelCompactSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfNormalizedCommonStageDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfNormalizedRecollementScalarCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfNormalizedRecollementTriangles | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfOpenClosedTriangleData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfPackageCommonStageTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfPositiveFiniteLocalizationConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfProEtaleProjectionFormula | D2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfQbarLocalizationExactDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfQbarLocalizationFiniteCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfQbarLocalizationFiniteData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SfRecollementRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ShiftedCoefficientLinesInvertible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityScalarExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerChartData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SourceSectionStalkConeComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StratifiedFiniteProjectiveTor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StrictDirectImageMixedUnitData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StrictEtaleExceptionalAdjointInterfaces | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StrictMixedFiniteEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StrictMixedScalarSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StrictMixedSystemModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.StrictScalarMateShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedCartierDerivedPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedCoefficientHomNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedProjectiveChernComparison | X2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SupportedTriangleMateIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompactSupportData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompactSupportEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompactSupportProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompactSupportRestrictionCocycle | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompactSupportRestrictionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompactSupportRestrictionEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompactSupportTransitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompatibleCompositorData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompatibleCompositorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompositorFiniteWordEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemOpenRestrictionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemOperationExchangeRealization | V2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemProjectionChangeCompatibility | X7 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | H9 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemProjectionFormulaMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemProjectionTriangleCompatibility | B3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemProperRestrictionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemRestrictionFiniteNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemScalarBasisDistributivity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemScalarProjectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemScalarRefinementRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemScalarTensorConstituents | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemTensorPresentationCoreExistence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemTensorPresentationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.SystemTensorSemilinearRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TamePairProperGenerators | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorExchangeCtfDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorHomCoefficientTransposes | P3 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorMateBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerNormalizationPreservation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1CtfData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1DiagonalTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1KernelScalarData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1LevelCtfModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1ProperCtf | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1SingleLevelTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1TriangleFactorization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1TriangleWords | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerP1UniformPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TowerUniformEtaleDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceStalkCompositorTowerData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceStalkTowerDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TraceStrictStalkTowers | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwConventions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistFrobeniusScalar | T8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackReductionTower | X2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorIntegrationSiteComparison | P2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VectorTraceScalarDescent | S8 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierPairingThreeTransposes | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | T2 | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilGeometricFiberProperties | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilGeometricHomConstructibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilIndOpenRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilIndOpenRepresentability | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilIndProperHigherRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilIndProperOpenHigher | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WfTateTwist | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlFrameworkQuotientAugmentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlImmersionRestrictionAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlImmersionWeilLocalData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlOpenExtensionAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlWeilPullCompositorEquivariance | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.DncCoefficientTransportData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.MixedBaseChange | C8 | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtensionCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ReductionExceptionalChart | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ReductionExceptionalConservativity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ReductionExceptionalObjects | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ReductionExceptionalRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.ScalarSectionCompositor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.SectionScalarBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | R4 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | H4 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | S1 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CanonicalOpenReductionIsIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CanonicalReductionPullComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CartesianCompactSupportCompositor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefDualizingConstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefDualizingSiteMates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefPairingCompactificationModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefPairingFrameNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefPairingHomRepresentativeComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefQbarVerdierCore | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefQbarVerdierData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefQbarVerdierDualizing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefQbarVerdierExceptional | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefScalarReductionExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairingData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefficientDualizingClosedAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CoefficientUnitNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompactSupportRefinementBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedOpenCartesianIdentity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedProjectionExchangeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedProjectionExchangeDomains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedProjectionExchangePaths | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedProjectionExchangeSystem | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedTensorShiftAddOnGood | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ConstructibleReductionGood | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.DetSfCompBaseChangeDefs | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.DualizingOpenMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleHomComparisonModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleHomThickLocus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleHomTransposeExact | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleOpenExtensionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleOpenKFlat | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleOpenMixedTensorScalar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleOpenScalarCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleOpenTensor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleOpenTensorDefs | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.EtaleRestrictionCompositor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteCoefficientVerdierData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteDualizingAffineRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteDualizingData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteDualizingScalarRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteExceptionalData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteExceptionalDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteFreeComparisonTransitivity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteFreeImageComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteIntrinsicBidualComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteOpenCartesianCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteReductionCompletionUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteVerdierCoefficientDiagrams | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FiniteVerdierProEtaleLeftTor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport | G1 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | H1 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.GeneratorReductionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralBasicRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompactSupportPreservation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | S4 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompactificationRealizationData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralCompatibleComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralDualizingFiniteBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralDualizingMappingLimit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralDualizingRoosModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | X5 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalLimitConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralFiniteHomEstimate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralKernelContractions | D4 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | Y6 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralNormalizedFamily | Z5 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralOpenMateNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralOperationShiftData | X6 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralProperTowerTransition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralReductionPullbackModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralSupportRealizationComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralSupportTowerNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralSystemCompositorAssociativity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralTensorLeftShiftUnique | A8 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralTensorRightShiftExt | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralTensorRightShiftUnique | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralTensorShiftProperties | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ListedCoefficientCtf | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ListedCoefficientMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ListedScalarCoefficientMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenBaseChangeReductionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenDvrRingedIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenFactorCoherenceData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenFactorExchangeRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenFactorOpenRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenFactorProjectionRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenInterchangeReductionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenNormalizedProductCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenProjectionCompletedSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenProjectionOrdinaryRoos | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenProjectionRestrictionNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenReconstructionEffectivity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenReductionMateLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenTensorQuotientCochains | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenTensorQuotientData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenTensorQuotientGeometry | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OpenTensorReductionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OrdinaryOpenReductionMate | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.OrdinaryProperOpenInvertibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.PrimitiveCompletionEffectivity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.PrimitiveQuotientAugmentations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionTower | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProEtale.IntegralRestrictionPullbackTowerSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | E2 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProperOpenLambdaReductionSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ProperSupportStepBounds | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.PullQuotientAugmentationOnGood | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalDualizingIdentification | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalExceptionalIdentifications | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalHomIdentifications | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalOperationsData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalVerdierComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalVerdierDatum | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalVerdierExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalVerdierModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RationalVerdierUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.RefinementProjectionCounit | T3 | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarDenseRefinementSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarDirectImageElementaryCases | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarDirectImageMateCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixAdmissibleThickness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixCanonicalExtensionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixCtfGenerators | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixDefinitions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixDerivedPullbackNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixFiniteGeneration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixGeometry | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixHeartLatticeExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixImmersionComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixLisseTowerComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixNonfiniteGeneration | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixNormalizedImmersion | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixOpenComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixPerfectExtension | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ShortWordCompletionIsomorphism | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ShortWordIntegralDomain | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.StructuralReductionWordSubstitution | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SystemProperOpenSupport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SystemPushCompositionLaws | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SystemPushIdentityPullUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SystemTensorLeftShiftUnique | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SystemTensorRightShiftUnique | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TensorQuotientAugmentationOnGood | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.ThreeCellCompositor | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TriangleProjectionCompositorContraction | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SmoothPurity.OrdinaryProductTransposeData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SmoothPurity.OrdinaryTripleLeftComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.SmoothPurity.OrdinaryTripleRightComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Targets.AffineSpaceRationalLine | R3 | Unchanged; verbatim public reexport. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.TraceFormula.PointConeLiftsChainNaturality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.DerivedHomSingleResolution | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeBasicComparisons | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeCompactificationModelComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeCompatibleTowerCalculation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeDerivedHomComparison | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeImmersionHeartLocalization | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeInjectiveAdjunctionModel | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeOpenProperForgetting | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeOpenProperInterchange | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativePullbackStarPreservation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.ProperSheafFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Unchanged; verbatim public reexport. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged; verbatim public reexport. |
| TargetsCheck | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Constituent | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Punctual | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.PoincareDuality.AdicReconstruction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitDualDatum | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodConstruction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodExistence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseSheafEquivalence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.CoefficientReduction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicSystem | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundedConstructibleUpperShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersion | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersionSheaf | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeStalk | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnit | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitDerived | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitRefinement | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImageReduction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralConstructible | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralVerdier | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberAlgClosed | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberRational | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalOperations | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteStage | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Remarks | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexVerdierDual | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicAbIdentification | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantSheafLeg | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.EtaleBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionSMulUpperStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafBasis | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStageMap | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeApproximation | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIdentification | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIntegrality | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeKernel | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeScalarLinear | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeSemilinear | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeTensorBijective | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerShriekFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantBounded | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFiniteness | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFinitenessStratum | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissage | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissageRegular | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisse | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisseComponents | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarScalar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLisse | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperTwistedLattice | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.AdicBaseChangeTower | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.AdicSmoothBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleTwoColimit | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleTwoColimitTStructure | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalars | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsComp | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsConstructible | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ScalarExtensionConstructible | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CoefficientSetup | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchangeComparison | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.BaseChange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.CompactFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Constructible | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriekBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.OpenImmersion | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Projection | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.ProjectionPullback | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.RestrictScalarsMate | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplex | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplexFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplexTrace | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.UpperStarCoherence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.WeilDatum | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeAlgClosed | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeComplete | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeRational | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormulaBounded | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TraceScalarExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaAdic | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaField | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionCoherence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjection | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjectionComparison | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjectionIso | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.Statement | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Main | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Product | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierFunctions | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierIsotypic | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierMul | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierPlane | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrivialization | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.BaseChangeField.Cohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.BaseChangeField.Comparison | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.BoundaryStalkFrobenius | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.BoundaryStalkSpecialization | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.BoundaryStrictHenselization | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ClosedLowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstant | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstantExt | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyNonneg | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyProEtale | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyResolution | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologySequence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CompactSupportAdicConstant | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.DerivedHom | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientForget | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientFrobeniusTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientKaroubian | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientTateTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientTransition | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientTriangulated | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FiniteEtale | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FiniteLeray | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FiniteLowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FinitePointCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierBaseLinear | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierFirstFormula | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.AffinePlaneAdd | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.ConvolutionKernel | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.KernelComposition | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.Reflection | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisseComm | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierStalkFibre | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.FrobeniusTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.GlobalSectionsUpperStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.HigherLowerStarZero | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.IhomCurry | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.IhomLisse.CompWeil | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.IhomLisse.SwapWeil | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.IntegralCoefficientCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Isotypic | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.IsotypicPullback | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LisseExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.LowerStarTriangulated | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.ExtensionByZero | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ProperBaseChange | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.ShiftedSheaf | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.SplitTorsor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkRationalPoint | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkStrictlyHenselian | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StalkTensorTrace | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TensorHomAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TorsorPairing | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TraceCupAdicConstant | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TraceFunction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.UpperStarLowerStar | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.VerdierDual | X5 | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged; verbatim public reexport. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Unchanged; verbatim public reexport. |

Consumer validation: the three unchanged direct importers compile against the packet
(31.3 s, 4.8 s and 8.9 s respectively); all six packet modules compile cleanly in at most
12.0 s. No consumer adaptation is needed.

## Status

landed 20261026T065537-L-3071508 2026-10-26 (merge of deliver/E5/Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence)
