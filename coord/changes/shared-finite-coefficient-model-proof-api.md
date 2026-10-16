# Shared finite coefficient model proof API

## Reason

The returned delivery duplicated six private theorems. Both original parent modules
reach the support-gluing item, so importing either from that item would create a cycle.
Extract the existing proofs into one lower dependency and let all three consumers reuse
them with nonpublic `import all`. The two adapted source modules are unclaimed.
No existing public theorem, definition, target, universe, comparison morphism, or visibility
changes. The new shared module exposes finiteBoundedTriangulated as its node declaration.
The removed declarations were private and have no external source users; their proofs and
types are retained in the shared module. The private `factors` definition moves with its API.

## Old

The following are the exact source declaration headers (the original section binders
remain unchanged in each adapted parent).

```lean
-- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
private def factors (K : D) : Prop

-- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
private lemma factors_iso {K L : D} (e : K ≅ L) (h : factors c K) : factors c L

-- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
private def shiftFactors : ObjectProperty D

-- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
private lemma shiftFactors_of_hom_colimit
    {A : Type*} [Category A] {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (S : D)
    (h : ∀ n : ℤ, IsIso (colimit.desc _
      ((Q ⋙ shiftFunctor D n ⋙ preadditiveCoyoneda.obj (Opposite.op S)).mapCocone
        (colimit.cocone N)))) :
    shiftFactors (Q.mapCocone (colimit.cocone N)) S

-- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
private lemma factors_of_colimit_cocone
    {A : Type*} [Category A] {J : Type*} [Category J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (c : Cocone N) (hc : IsColimit c) (K : D)
    (h : factors (Q.mapCocone (colimit.cocone N)) K) : factors (Q.mapCocone c) K

-- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
private lemma bounded_tri_of_serre {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (hker : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsConstructibleModuleObject R M → IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧ IsConstructibleModuleObject R (cokernel f))
    (hext : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    (boundedConstructible R).IsTriangulated

-- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
private lemma finiteBoundedTriangulated (E : FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated

-- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
private lemma single_bounded_constructible
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : IsConstructibleModuleObject R M) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj M)

-- Sheaf.Paper.CondensedFlatCoefficientCalculus
private noncomputable abbrev derivedComp (e : F ⋙ G ≅ FG) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ FG.mapDerivedCategory

-- Sheaf.Paper.CondensedFlatCoefficientCalculus
private noncomputable abbrev transportComp (a : F ≅ F') (b : G ≅ G') (c : FG ≅ FG')
    (e : F' ⋙ G' ≅ FG') : F ⋙ G ≅ FG

-- Sheaf.Paper.CondensedFlatCoefficientCalculus
private lemma leftComp_transport (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    (F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso e =
      transportComp F.leftDerivedFunctorIsoMapDerivedCategory
        G.leftDerivedFunctorIsoMapDerivedCategory FG.leftDerivedFunctorIsoMapDerivedCategory
        (derivedComp e)

-- Sheaf.Paper.CondensedFlatCoefficientCalculus
private lemma leftComp_shift (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    let := CommShift.ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift ((F.leftDerivedFunctorCompIso G).symm ≪≫
      (F ⋙ G).leftDerivedFunctorNatIso e).hom ℤ
```

## New

The headers below have one home in `Sheaf.Paper.CondensedFiniteModelProofAPI`.
The generic derived composition and transport definitions are extracted with their
full generality. The private shift-factorization property moves with its continuity
lemma so that it too has only one proof. Only `finiteBoundedTriangulated` becomes
public in the new module; all existing public interfaces are unchanged.

```lean
private def factors (K : D) : Prop

private lemma factors_iso {K L : D} (e : K ≅ L) (h : factors c K) : factors c L

private def shiftFactors : ObjectProperty D

private lemma shiftFactors_of_hom_colimit
    {A : Type*} [Category A] {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (S : D)
    (h : ∀ n : ℤ, IsIso (colimit.desc _
      ((Q ⋙ shiftFunctor D n ⋙ preadditiveCoyoneda.obj (Opposite.op S)).mapCocone
        (colimit.cocone N)))) :
    shiftFactors (Q.mapCocone (colimit.cocone N)) S

private lemma factors_of_colimit_cocone
    {A : Type*} [Category A] {J : Type*} [Category J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (c : Cocone N) (hc : IsColimit c) (K : D)
    (h : factors (Q.mapCocone (colimit.cocone N)) K) : factors (Q.mapCocone c) K

private noncomputable abbrev derivedComp (e : F ⋙ G ≅ FG) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ FG.mapDerivedCategory

private noncomputable abbrev transportComp (a : F ≅ F') (b : G ≅ G') (c : FG ≅ FG')
    (e : F' ⋙ G' ≅ FG') : F ⋙ G ≅ FG

private lemma leftComp_transport (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    (F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso e =
      transportComp F.leftDerivedFunctorIsoMapDerivedCategory
        G.leftDerivedFunctorIsoMapDerivedCategory FG.leftDerivedFunctorIsoMapDerivedCategory
        (derivedComp e)

private lemma leftComp_shift (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    let := CommShift.ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift ((F.leftDerivedFunctorCompIso G).symm ≪≫
      (F ⋙ G).leftDerivedFunctorNatIso e).hom ℤ

private lemma bounded_tri_of_serre {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (hker : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : M ⟶ N),
      IsConstructibleModuleObject R M → IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧ IsConstructibleModuleObject R (cokernel f))
    (hext : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    (boundedConstructible R).IsTriangulated

lemma finiteBoundedTriangulated (E : FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated

private lemma single_bounded_constructible
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : IsConstructibleModuleObject R M) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj M)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | no source use of the moved private helpers; public interface unchanged |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | private helpers extracted; import shared proof API; public statements unchanged |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | no source use of the moved private helpers; public interface unchanged |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | no source use of the moved private helpers; public interface unchanged |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | no source use of the moved private helpers; public interface unchanged |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | no source use of the moved private helpers; public interface unchanged |
| TargetsCheck | unclaimed | no source use of the moved private helpers; public interface unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | no source use of the moved private helpers; public interface unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | no source use of the moved private helpers; public interface unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | private helpers extracted; import shared proof API; public statements unchanged |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | reuse the shared private helpers |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | new cycle-free home of the shared proofs |

Direct name searches and `tools/downstream.py --uses` show that each removed private
helper is used only within its original parent. No library module imports either parent
with `import all`; no external user requires adaptation. The gluing item and all its
public statements remain unchanged. Unit records and target statements are untouched.

## Status

landed 20261016T072032-L-914019 2026-10-16 (merge of deliver/G1/Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing)
