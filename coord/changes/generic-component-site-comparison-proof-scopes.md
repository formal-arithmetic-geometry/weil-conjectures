# AlgebraicGeometry.Scheme.ProEt.generic_component_site_comparison

## Reason

The proof uses local transparency controls for the chosen component data and explicit
component coordinates. The static preflight classifies these attribute commands as an
interface change and requests this record. No existing definition, declaration signature,
public import, or target is changed. The private continuity theorem is registered with
`attribute [local instance]`, so it adds no global instance. The independent reader should
verify these scopes and the unchanged public interface.

## Old

The existing theorem signature, verbatim:

```lean
theorem generic_component_site_comparison
    (X : Scheme.{u}) [IsAffine X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ X)
    (U : X.ProEt) [IsAffine U.left]
    (hind : RingHom.IndEtaleAcrossUniverses U.hom.appTop.hom) :
    letI : IsAffineHom (show U.left ⟶ X from U.hom) :=
      isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
    letI : IsAffineHom η := isAffineHom_of_isAffine η
    letI : IsAffine (pullback U.hom η) :=
      instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
    let V : Scheme := pullback U.hom η
    let S : Profinite.{u} := Scheme.ProEt.componentProfinite U.left
    let Sη : Profinite.{u} := Scheme.ProEt.componentProfinite V
    let r : C(Sη, S) :=
      ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
        (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
    (genericComponentProjection V).inverse.IsEquivalence ∧
      Nonempty ((coherentTopology Profinite.{u}).overMapPullback
          (Type (u + 1)) (ConcreteCategory.ofHom r : Sη ⟶ S) ⋙
        (genericComponentProjection V).inverse ≅
          (genericComponentProjection U.left).inverse ⋙
            Scheme.proEtaleSheafInverseImage (pullback.fst U.hom η) (Type (u + 1))) ∧
      Nonempty ((coherentTopology Profinite.{u}).overPullback (Type (u + 1)) Sη ⋙
          (genericComponentProjection V).inverse ≅
        AlgebraicGeometry.ProEtale.profinitePointSetSchemeInverseImage (Spec (.of Ω)) ⋙
          Scheme.proEtaleSheafInverseImage (pullback.snd U.hom η) (Type (u + 1))) 
```

Its proof was `by sorry`. The module had no local transparency attributes or private helpers.

## New

The identical theorem signature, verbatim:

```lean
theorem generic_component_site_comparison
    (X : Scheme.{u}) [IsAffine X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (.of Ω) ⟶ X)
    (U : X.ProEt) [IsAffine U.left]
    (hind : RingHom.IndEtaleAcrossUniverses U.hom.appTop.hom) :
    letI : IsAffineHom (show U.left ⟶ X from U.hom) :=
      isAffineHom_of_isAffine (show U.left ⟶ X from U.hom)
    letI : IsAffineHom η := isAffineHom_of_isAffine η
    letI : IsAffine (pullback U.hom η) :=
      instIsAffinePullbackSchemeOfIsAffineHom_1 (show U.left ⟶ X from U.hom) η
    let V : Scheme := pullback U.hom η
    let S : Profinite.{u} := Scheme.ProEt.componentProfinite U.left
    let Sη : Profinite.{u} := Scheme.ProEt.componentProfinite V
    let r : C(Sη, S) :=
      ⟨(pullback.fst U.hom η).continuous.connectedComponentsMap,
        (pullback.fst U.hom η).continuous.connectedComponentsMap_continuous⟩
    (genericComponentProjection V).inverse.IsEquivalence ∧
      Nonempty ((coherentTopology Profinite.{u}).overMapPullback
          (Type (u + 1)) (ConcreteCategory.ofHom r : Sη ⟶ S) ⋙
        (genericComponentProjection V).inverse ≅
          (genericComponentProjection U.left).inverse ⋙
            Scheme.proEtaleSheafInverseImage (pullback.fst U.hom η) (Type (u + 1))) ∧
      Nonempty ((coherentTopology Profinite.{u}).overPullback (Type (u + 1)) Sη ⋙
          (genericComponentProjection V).inverse ≅
        AlgebraicGeometry.ProEtale.profinitePointSetSchemeInverseImage (Spec (.of Ω)) ⋙
          Scheme.proEtaleSheafInverseImage (pullback.snd U.hom η) (Type (u + 1))) 
```

Its proof is complete, using proved private helpers. The three existing public imports
are unchanged; all new imports are private proof imports. Local controls are:

```lean
attribute [local irreducible] genericComponentProjection genericComponentFunctor
attribute [local irreducible] componentProjection componentStructure componentFiberHomeo
attribute [local irreducible] componentComponentsHomeo
attribute [local instance] explicitContinuous
```

The new private isomorphism definitions `genericExplicitIso`, `componentBaseChangeIso`,
`genericRestrictionIso`, `genericBaseChangeIso`, `absoluteComponentIso`, and
`genericAbsoluteIso` carry `@[irreducible]`; none appears in a public signature or
public definition. File options only guide elaboration of this proof. No data definition
has been modified and no definition contains a hole.

## Users

`tools/downstream.py` lists the following twelve downstream modules. Its `--uses
 generic_component_site_comparison` query finds the item and
`Sheaf.AlgebraicGeometry.GenericFiberComponentsSection` only. Since the theorem type,
public imports and existing definitions are identical, each existing consumer has the
same statement and proof interface, with no adaptation needed. No consumer source is
included in this packet. Claim holders are those read when writing this record.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.ContinuousQbarConstructibleGenerators | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.ContinuousQbarLisseHeartClosure | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Identical public signature and imports; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Identical public signature and imports; no adaptation. |

## Status

landed 20261024T191614-L-442750 2026-10-24 (merge of deliver/W5/Sheaf.AlgebraicGeometry.GenericComponentSiteComparison)
