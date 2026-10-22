# AlgebraicGeometry.Scheme.finiteField_lisse_internalHom

## Reason

Preflight requires this record for the added instance and attribute commands in
`Sheaf.Paper.FiniteFieldLisseInternalHom`. The mathematical statement, the existing
public instance, both public definitions and all eight public imports are unchanged.
The new private helpers prove finite-free evaluation, exact Hom and the natural
cohomology comparison. All seven added instance declarations are explicitly private
and proved. No other Lean module is edited.

The imported bounded-evaluation module provides very general private instances for
colimits, total complexes and finite biproducts. Removing their instance registrations
avoids searching these broad instances when constructing the more specific sheaf
comparison. These three declarations are imported with `import all`; the removal is
not marked local, and this record explicitly includes that command. They are private
helpers of a Sheaf module, not adopted source-library attributes. All other added
attribute commands are explicitly local: they select the ordinary derived category
or control unfolding of already constructed comparison functors. The additional
namespace, variable, notation and transparency commands only support elaboration of
the proved private development. No public notation or simp rule is added.

## Old

The public theorem signature, verbatim:

```lean
theorem finiteField_lisse_internalHom
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (A : Type u) [Field A] [Finite A] :
    (∀ (L : proEtaleRingModules S (proEtaleConstantRing S A)),
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
        (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) L →
      ∀ (a b : ℤ), a ≤ b →
      ∀ (N : DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A))),
        (∀ r : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ r).obj N)) →
        (∀ r : ℤ, r < a ∨ b < r →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) r).obj N)) →
        ∀ r : ℤ,
          IsConstructibleProEtaleModuleSheaf S A
            ((finiteFieldInternalHomCohomology S A r).obj (op L, N)) ∧
          (r < a ∨ b < r →
            IsZero ((finiteFieldInternalHomCohomology S A r).obj (op L, N)))) ∧
    ∀ r : ℤ, Nonempty (
      (ObjectProperty.ι (fun P :
          (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
            DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ↦
        IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
          (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) P.1.unop ∧
        (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2))) ⋙
            finiteFieldInternalHomCohomology S A r ≅
      (ObjectProperty.ι (fun P :
          (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
            DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ↦
        IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
          (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) P.1.unop ∧
        (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2))) ⋙
            finiteFieldDualTensorCohomology S A r)
```

The seven private instances and the attribute commands listed below were absent.
The original file already had `set_option autoImplicit false` and
`open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory`.

## New

The public theorem has exactly the same signature shown under Old. Its proof is
complete, with no new admitted theorem. The existing public definitions and their
bodies are also verbatim unchanged. The added instance declarations are:

```lean
private instance (S : Scheme.{u}) (A : Type u) [CommRing A] (U : S.ProEt) :
    (modelPresheafFunctor S A U).Additive where
  map_add {X Y f g} := by ext; rfl

private instance sheafificationAdditive_ff
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R₀ : Cᵒᵖ ⥤ RingCat.{u + 1}} {R : Sheaf J RingCat.{u + 1}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}] :
    (_root_.PresheafOfModules.sheafification.{u + 1} α).Additive := by
  let L := _root_.PresheafOfModules.sheafification.{u + 1} α
  have : PreservesBinaryBiproducts L :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  exact Functor.additive_of_preservesBinaryBiproducts L

private instance (S : Scheme.{u}) (A : Type u) [CommRing A] (U : S.ProEt) :
    (modelSheafFunctor S A U).Additive := by
  dsimp only [modelSheafFunctor]
  infer_instance

private instance homAdditive (L : (SheafOfModules.{u + 1} 𝓡)ᵒᵖ) :
    ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj L).Additive := by
  let F := (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj L
  have : PreservesLimitsOfSize.{0, 0} F :=
    (SheafOfModules.tensorHomAdjunction_kfg R L.unop).rightAdjoint_preservesLimits
  exact Functor.additive_of_preserves_binary_products F

private instance finiteLocalSystemFree (S : Scheme.{u}) (A : Type u) [Field A]
    (L : (finiteLocalSystemProperty S A).FullSubcategory) : L.obj.IsFiniteLocallyFree :=
  finiteModelsLocallyFree S A L.obj L.property

private instance finiteLocalSystemHomLimits (S : Scheme.{u}) (A : Type u) [Field A]
    (L : (finiteLocalSystemProperty S A).FullSubcategory) :
    PreservesFiniteLimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
        (proEtaleConstantRing S A)).obj (op L.obj)) :=
  finiteLocallyFreeHomLimits S A L.obj

private instance finiteLocalSystemHomColimits (S : Scheme.{u}) (A : Type u) [Field A]
    (L : (finiteLocalSystemProperty S A).FullSubcategory) :
    PreservesFiniteColimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
        (proEtaleConstantRing S A)).obj (op L.obj)) := by
  have := finiteLocallyFreeHomColimits S A L.obj
  infer_instance
```

The added attribute commands, in file order, are:

```lean
attribute [-instance] CategoryTheory.RingedSiteBoundedEvaluation.smallColimits
  CategoryTheory.RingedSiteBoundedEvaluation.hasTotal
  CategoryTheory.RingedSiteBoundedEvaluation.finiteBiproducts
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] singleHomComplexGenericIso_ff
attribute [local irreducible] derivedInternalHomOfUniverses
attribute [local irreducible] DerivedCategory.homologyFunctor SheafOfModules.homFunctor
attribute [local semireducible] SheafOfModules.homFunctor
attribute [local irreducible] finiteFieldInternalHomCohomology
```

The file also uses private/local notation for the underlying ring sheaf, scoped
`backward.isDefEq.respectTransparency` options and explicit universe variables for
the generic categorical arguments. No public declaration is added.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteFieldLisseInternalHom --uses
finiteField_lisse_internalHom finiteFieldInternalHomCohomology
finiteFieldDualTensorCohomology` reports zero downstream modules in the current
checkout and only the assigned module as a textual user of these declarations.
The DAG attachment and unit realization are retained: zero current importers is not
used to withdraw this item. No consumer adaptation is required, and no target
statement or definition changes its meaning.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FiniteFieldLisseInternalHom` | A5 | One proof hole closed; proved private helpers and elaboration commands added; public signatures and definitions unchanged. |

## Status

landed 20261022T022939-L-765237 2026-10-22 (merge of deliver/A5/Sheaf.Paper.FiniteFieldLisseInternalHom)
