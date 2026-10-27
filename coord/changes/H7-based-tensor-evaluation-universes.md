# SheafOfModules.basedSheafTensorEvaluation

## Reason

The point comparison permits independent scheme and coefficient universes. The existing finite-basis theorem required a small site in the coefficient universe, preventing its application to that statement. Generalize the site object and morphism universes and make the existing sheafification assumptions explicit. The old specialization remains available. Replace two imports of private small-site helpers by proved local helpers with the generalized universes. No mathematical conclusion changes. The generic node drops its obsolete proof dependency on `lem-pur-finite-free-scalar-extension`: it used only two helper formulas from that module, now proved locally for the generalized site.

## Old

```lean
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}}


def basedTensorProductSections (d : ℕ)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) :
    (∏ᶜ fun _ : Fin d ↦ M).val.obj U ≅
      ModuleCat.of (R.obj.obj U) (Fin d → M.val.obj U) :=
  PreservesProduct.iso
    (evaluation.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
      (fun _ : Fin d ↦ M) ≪≫ ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj U)


theorem basedSheafTensorEvaluation :
    (∀ (φ : R ⟶ S),
      PreservesFiniteLimits (restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) ∧
      PreservesFiniteColimits (restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) ∧
      ∀ (M N P : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
        (f : M ⟶ N) (g : N ⟶ P),
        (imageSubobject f = kernelSubobject g ↔
          imageSubobject ((restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map f) =
          kernelSubobject ((restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map g))) ∧
    (∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
      (d : ℕ) (b : Module.Basis (Fin d) A
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))),
      (ModuleCat.extendScalars.{u, u, u} φ).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ)) ∧
    ∀ (one : C) (hOne : IsTerminal one) (φ : R ⟶ S) (d : ℕ)
      (b : Fin d → S.obj.obj (op one))
      (e : (∏ᶜ fun _ : Fin d ↦
          unit.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≅
        (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
          (unit.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
      (he : ∀ (U : Cᵒᵖ) (r : Fin d → R.obj.obj U),
        e.hom.val.app U
          ((basedTensorProductSections d
            (unit.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) U).inv r) =
          ∑ i : Fin d, φ.hom.app U (r i) * S.obj.map (hOne.from U.unop).op (b i)),
      ∃ E : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
          SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∃ hE : ∀ F : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R), E.obj F = changeOfRings
            φ F,
        (∀ {F G : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : F ⟶ G), E.map f =
          eqToHom (hE F) ≫ changeOfRingsHom.{u, u, u} φ F f ≫ eqToHom (hE G).symm) ∧
      ∃ (_ : E.Additive),
        PreservesFiniteLimits E ∧ PreservesFiniteColimits E ∧
      ∃ Φ : E ⋙ restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) ≅
          Functor.pi' (fun _ : Fin d ↦ 𝟭 (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⋙
            Pi.functor (Fin d),
      ∃ θ : ∀ (F : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ),
          (changeOfRingsPresheaf.{u, u, u} φ F).obj U ≅ (E.obj F).val.obj U,
        (∀ F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R), Presheaf.IsSheaf J
            (changeOfRingsPresheaf.{u, u, u} φ F).presheaf) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (a :
            S.obj.obj U) (x : F.val.obj U),
          (θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
            (eqToHom (hE F).symm).val.app U
              ((toSheafify J (changeOfRingsPresheaf.{u, u, u} φ F).presheaf).app U
                (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (a :
            S.obj.obj U) (x : F.val.obj U) (i : Fin d),
          (Pi.π (fun _ : Fin d ↦ F) i).val.app U
            ((Φ.hom.app F).val.app U
              ((θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) =
            ((e.inv ≫ Pi.π
              (fun _ : Fin d ↦ unit
                ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) i).val.app U a) •
            x) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (x : (∏ᶜ fun
            _ : Fin d ↦ F).val.obj U),
          (Φ.inv.app F).val.app U x = (θ F U).hom
            (∑ i : Fin d, S.obj.map (hOne.from U.unop).op (b i)
              ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
                ((Pi.π (fun _ : Fin d ↦ F) i).val.app U x))) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (x : (E.obj
            F).val.obj U),
          (θ F U).inv x = ∑ i : Fin d,
            S.obj.map (hOne.from U.unop).op (b i) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
              ((Pi.π (fun _ : Fin d ↦ F) i).val.app U ((Φ.hom.app F).val.app U x))) ∧
        (∀ (F G : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (f : F ⟶ G) (U : Cᵒᵖ)
            (x : (changeOfRingsPresheaf.{u, u, u} φ F).obj U),
          (E.map f).val.app U ((θ F U).hom x) =
            (θ G U).hom ((ModuleCat.extendScalars.{u, u, u}
              (R := R.obj.obj U) (S := S.obj.obj U) (φ.hom.app U).hom).map
              (f.val.app U) x)) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U V : Cᵒᵖ) (j : U ⟶
            V) (x : (changeOfRingsPresheaf.{u, u, u} φ F).obj U),
          (E.obj F).val.map j ((θ F U).hom x) =
            (θ F V).hom ((changeOfRingsPresheaf.{u, u, u} φ F).map j x)) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (k :
            (changeOfRingsPresheaf.{u, u, u} φ F).obj U ⟶ (E.obj F).val.obj U),
          (∀ (a : S.obj.obj U) (x : F.val.obj U),
            k (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
              (θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) →
            k = (θ F U).hom) ∧
        (∀ K : CochainComplex (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
          ∀ U : Cᵒᵖ,
          ∃ α : (((evaluation.{u}
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) ⋙
              ModuleCat.extendScalars.{u, u, u}
              (R := R.obj.obj U) (S := S.obj.obj U) (φ.hom.app U).hom).mapHomologicalComplex (.up
            ℤ)).obj K ≅
            (Functor.mapHomologicalComplex
              (evaluation.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) U)
              (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj K),
            ∀ j : ℤ, α.hom.f j = (θ (K.X j) U).hom ∧
              α.inv.f j = (θ (K.X j) U).inv)
```

## New

```lean
universe u vC uC
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}}


def basedTensorProductSections (d : ℕ)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) :
    (∏ᶜ fun _ : Fin d ↦ M).val.obj U ≅
      ModuleCat.of (R.obj.obj U) (Fin d → M.val.obj U) :=
  PreservesProduct.iso
    (evaluation.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
      (fun _ : Fin d ↦ M) ≪≫ ModuleCat.piIsoPi (fun _ : Fin d ↦ M.val.obj U)


theorem basedSheafTensorEvaluation :
    (∀ (φ : R ⟶ S),
      PreservesFiniteLimits (restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) ∧
      PreservesFiniteColimits (restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) ∧
      ∀ (M N P : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
        (f : M ⟶ N) (g : N ⟶ P),
        (imageSubobject f = kernelSubobject g ↔
          imageSubobject ((restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map f) =
          kernelSubobject ((restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map g))) ∧
    (∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
      (d : ℕ) (b : Module.Basis (Fin d) A
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))),
      (ModuleCat.extendScalars.{u, u, u} φ).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ)) ∧
    ∀ (one : C) (hOne : IsTerminal one) (φ : R ⟶ S) (d : ℕ)
      (b : Fin d → S.obj.obj (op one))
      (e : (∏ᶜ fun _ : Fin d ↦
          unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≅
        (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
      (he : ∀ (U : Cᵒᵖ) (r : Fin d → R.obj.obj U),
        e.hom.val.app U
          ((basedTensorProductSections d
            (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) U).inv r) =
          ∑ i : Fin d, φ.hom.app U (r i) * S.obj.map (hOne.from U.unop).op (b i)),
      ∃ E : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
          SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∃ hE : ∀ F : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R), E.obj F = changeOfRings
            φ F,
        (∀ {F G : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : F ⟶ G), E.map f =
          eqToHom (hE F) ≫ changeOfRingsHom.{vC, uC, u} φ F f ≫ eqToHom (hE G).symm) ∧
      ∃ (_ : E.Additive),
        PreservesFiniteLimits E ∧ PreservesFiniteColimits E ∧
      ∃ Φ : E ⋙ restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) ≅
          Functor.pi' (fun _ : Fin d ↦ 𝟭 (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⋙
            Pi.functor (Fin d),
      ∃ θ : ∀ (F : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ),
          (changeOfRingsPresheaf.{vC, uC, u} φ F).obj U ≅ (E.obj F).val.obj U,
        (∀ F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R), Presheaf.IsSheaf J
            (changeOfRingsPresheaf.{vC, uC, u} φ F).presheaf) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (a :
            S.obj.obj U) (x : F.val.obj U),
          (θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
            (eqToHom (hE F).symm).val.app U
              ((toSheafify J (changeOfRingsPresheaf.{vC, uC, u} φ F).presheaf).app U
                (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (a :
            S.obj.obj U) (x : F.val.obj U) (i : Fin d),
          (Pi.π (fun _ : Fin d ↦ F) i).val.app U
            ((Φ.hom.app F).val.app U
              ((θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) =
            ((e.inv ≫ Pi.π
              (fun _ : Fin d ↦ unit
                ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) i).val.app U a) •
            x) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (x : (∏ᶜ fun
            _ : Fin d ↦ F).val.obj U),
          (Φ.inv.app F).val.app U x = (θ F U).hom
            (∑ i : Fin d, S.obj.map (hOne.from U.unop).op (b i)
              ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
                ((Pi.π (fun _ : Fin d ↦ F) i).val.app U x))) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (x : (E.obj
            F).val.obj U),
          (θ F U).inv x = ∑ i : Fin d,
            S.obj.map (hOne.from U.unop).op (b i) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
              ((Pi.π (fun _ : Fin d ↦ F) i).val.app U ((Φ.hom.app F).val.app U x))) ∧
        (∀ (F G : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (f : F ⟶ G) (U : Cᵒᵖ)
            (x : (changeOfRingsPresheaf.{vC, uC, u} φ F).obj U),
          (E.map f).val.app U ((θ F U).hom x) =
            (θ G U).hom ((ModuleCat.extendScalars.{u, u, u}
              (R := R.obj.obj U) (S := S.obj.obj U) (φ.hom.app U).hom).map
              (f.val.app U) x)) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U V : Cᵒᵖ) (j : U ⟶
            V) (x : (changeOfRingsPresheaf.{vC, uC, u} φ F).obj U),
          (E.obj F).val.map j ((θ F U).hom x) =
            (θ F V).hom ((changeOfRingsPresheaf.{vC, uC, u} φ F).map j x)) ∧
        (∀ (F : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) (k :
            (changeOfRingsPresheaf.{vC, uC, u} φ F).obj U ⟶ (E.obj F).val.obj U),
          (∀ (a : S.obj.obj U) (x : F.val.obj U),
            k (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
              (θ F U).hom (a ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) →
            k = (θ F U).hom) ∧
        (∀ K : CochainComplex (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
          ∀ U : Cᵒᵖ,
          ∃ α : (((evaluation.{u}
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) ⋙
              ModuleCat.extendScalars.{u, u, u}
              (R := R.obj.obj U) (S := S.obj.obj U) (φ.hom.app U).hom).mapHomologicalComplex (.up
            ℤ)).obj K ≅
            (Functor.mapHomologicalComplex
              (evaluation.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) U)
              (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj K),
            ∀ j : ℤ, α.hom.f j = (θ (K.X j) U).hom ∧
              α.inv.f j = (θ (K.X j) U).inv)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.Sheaf.BasedTensorEvaluation | unclaimed | Generalized API and internal proofs; no holes added. |
| Sheaf.Paper.PointFiniteFreeSectionsTensor | H7 | Newly uses the generalized API. |
| Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates | no local claim record (landed 2026-10-25 by Y6) | `import all` of this module (uses `restriction_limits`/`restriction_colimits`); unchanged; compiles against the generalized module (review 0decb: 54.3 s). |

`tools/downstream.py` reported no existing downstream modules when the record was written; since then `Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates` landed with `import all` of this module (reviewer addition, 0decb review); it compiles unchanged. The generic API remains valid for small sites and specializes to the original statement with the canonical instances. This change does not alter any target definition.

## Status

landed 20261024T224923-L-1831152 2026-10-24 (merge of deliver/H7/Sheaf.Paper.PointFiniteFreeSectionsTensor)
