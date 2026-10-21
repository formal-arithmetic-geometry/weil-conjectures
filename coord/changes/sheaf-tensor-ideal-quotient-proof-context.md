# CategoryTheory.RingedSiteIdeal.sheaf_tensor_ideal_quotient

## Reason

Module: `Sheaf.Paper.SheafTensorIdealQuotient`.
The proof adds private helper constructions and a module-level variable context and
transparency option for elaborating the existing sheaf tensor and restriction-of-scalars
interfaces. Server preflight requires a change record for these commands even though
the public theorem statement and original public imports remain unchanged. Six helper
properties are proved as private lemmas and registered only as local instances.
No public instance is added. The removed local-section import was a private proof import.

## Old

The existing module context was:

```lean
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteIdeal
set_option autoImplicit false
```

The theorem signature was:

```lean
theorem sheaf_tensor_ideal_quotient
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    ∃ (a : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        quotientTensor I F ≅ moduleQuotient I F)
      (uMap : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        F ⟶ quotientTensor I F)
      (Q : ∀ (I : RingedSiteIdeal R) (_ : SheafOfModules.{u} (siteModuleRings R)),
        SheafOfModules.{u} (siteModuleRings (ringQuotient I)))
      (e : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        (SheafOfModules.RingedTensor.restriction (ringProjection I)).obj (Q I F) ≅
          moduleQuotient I F),
      ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
      Presheaf.IsSheaf J (localProduct I F).toPresheafOfModules.presheaf ∧
      (∀ (U : C) (f : F.val.obj (op U)), f ∈ (localProduct I F).obj (op U) ↔
        ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
          ∃ (n : ℕ) (i : Fin n → I.sections V) (x : Fin n → F.val.obj (op V)),
            F.val.map g.op f = ∑ k : Fin n, (i k).val • x k) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (uMap I F).val.app W f =
          SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            (1 : (ringQuotient I).obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W) (r : R.obj.obj W),
        (a I F).hom.val.app W
          (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            ((ringProjection I).hom.app W r)) =
          (moduleProjection I F).val.app W (r • f)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (a I F).inv.val.app W ((moduleProjection I F).val.app W f) =
          SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            (1 : (ringQuotient I).obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W) (s t : (ringQuotient I).obj.obj W),
        (e I F).inv.val.app W ((a I F).hom.val.app W
          (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f (s * t))) =
        s • @id ((Q I F).val.obj W)
          ((e I F).inv.val.app W ((a I F).hom.val.app W
            (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f t)))) ∧
      uMap I F ≫ (a I F).hom = moduleProjection I F ∧
      Epi (uMap I F) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (uMap I F).val.app W f = 0 ↔ f ∈ (localProduct I F).obj W) ∧
      (∀ (G : SheafOfModules.{u} (siteModuleRings R)) (h : F ⟶ G),
        ∃ (qh : moduleQuotient I F ⟶ moduleQuotient I G) (hS : Q I F ⟶ Q I G),
          moduleProjection I F ≫ qh = h ≫ moduleProjection I G ∧
          (e I F).hom ≫ qh =
            (SheafOfModules.RingedTensor.restriction (ringProjection I)).map hS ≫
              (e I G).hom ∧
          (a I F).hom ≫ qh =
            (SheafOfModules.monoidalCategory R).tensorHom h (𝟙 (quotientCoefficient I)) ≫
              (a I G).hom) ∧
      (∀ (I' : RingedSiteIdeal R) (hI : IsContained I' I),
        ∃ (tM : quotientCoefficient I' ⟶ quotientCoefficient I)
          (v : moduleQuotient I' F ⟶ moduleQuotient I F),
          (∀ (W : Cᵒᵖ) (s : (ringQuotient I').obj.obj W),
            tM.val.app W s = (ringTransition hI).hom.app W s) ∧
          moduleProjection I' F ≫ v = moduleProjection I F ∧
          (a I' F).hom ≫ v =
            (SheafOfModules.monoidalCategory R).tensorHom (𝟙 F) tM ≫ (a I F).hom ∧
          uMap I' F ≫ (SheafOfModules.monoidalCategory R).tensorHom (𝟙 F) tM = uMap I F)
```

Its proof was `by sorry`.

## New

The module context is:

```lean
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteIdeal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
```

The theorem retains exactly the signature quoted under Old. Its proof is complete.
All additional constructions and lemmas are private, and all six instance registrations
use `attribute [local instance]`. No existing definition or declaration signature changes.
The full proof and revised DAG steps are in the delivery for independent review.

## Users

`tools/downstream.py Sheaf.Paper.SheafTensorIdealQuotient --uses
sheaf_tensor_ideal_quotient` reports zero downstream modules and only this module as a
textual user. DAG parents still depend on this theorem; its complete statement is
preserved, including all quotient projection and naturality clauses. No consumer needs
adaptation. This is not a withdrawal request.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SheafTensorIdealQuotient | S9 | Complete proof; private helpers and local context |

No target signature or definition changes, so the meanings of target statements are
unchanged. The adopted source tree `lean/WeilConjectures/` is untouched.

## Status

landed 20261021T143951-L-30292 2026-10-21 (merge of deliver/S9/Sheaf.Paper.SheafTensorIdealQuotient)
