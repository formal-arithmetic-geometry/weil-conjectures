import WeilConjectures.Scratch.C5
import WeilConjectures.WeilObject.Sheaf.EndTensorUnitTrace
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelPointTrace
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The pullback commutes with the multiplication by a scalar. -/
lemma adicUpperStar_map_smul {X Z : Scheme.{u}} (g : Z ⟶ X) (c : ULift.{u + 1} (PadicAlgCl l))
    (M : AdicSheaf l X) : (g)^*ᵃ[l].map (AdicSheaf.smul c M) = AdicSheaf.smul c ((g)^*ᵃ[l].obj M) :=
  Mod.hom_ext _ _ (by
    rw [adicUpperStar_map_hom, AdicSheaf.smul_hom, AdicSheaf.smul_hom, Functor.map_smul,
      CategoryTheory.Functor.map_id]
    rfl)

/-- The Galois action on the global sections of the pullback of an `ℓ`-adic sheaf along `x` with
`σ ≫ x = x`: `Γ(x^* H) ⟶ Γ(σ^* x^* H) ≅ Γ((σ ≫ x)^* H) = Γ(x^* H)`. -/
noncomputable def galoisGlobalSections {S X : Scheme.{u}} (σ : S ⟶ S) (x : S ⟶ X)
    (h : σ ≫ x = x) (H : AdicSheaf l X) :
    (Sheaf.Γ _ _).obj ((x)^*ᵃ[l].obj H).X ⟶ (Sheaf.Γ _ _).obj ((x)^*ᵃ[l].obj H).X :=
  (globalSectionsToUpperStar _ σ).app ((x)^*ᵃ[l].obj H).X ≫
    (Sheaf.Γ _ _).map ((adicUpperStarComp l σ x).inv.app H ≫
      (adicUpperStarCongr l h).hom.app H).hom

/-- The Galois action on global sections is the pullback of morphisms out of `ℚ̄_ℓ`. -/
lemma galoisGlobalSections_globalSectionOfModHom {S X : Scheme.{u}} (σ : S ⟶ S) (x : S ⟶ X)
    (h : σ ≫ x = x) (H : AdicSheaf l X) (v : AdicSheaf.unit l S ⟶ (x)^*ᵃ[l].obj H) :
    (galoisGlobalSections σ x h H).hom (globalSectionOfModHom v) =
      globalSectionOfModHom (adicUpperStarSectionMap σ x h H v) := by
  rw [galoisGlobalSections, ModuleCat.hom_comp, LinearMap.comp_apply,
    globalSectionsToUpperStar_globalSectionOfModHom, adicUpperStarSectionMap,
    ← Category.assoc, globalSectionOfModHom_comp ((adicUpperStarUnitIso l σ).inv ≫ (σ)^*ᵃ[l].map v)]
  rfl

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.UnitBasis

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] {X Y : C} {ι : Type*}
  [Fintype ι] [DecidableEq ι]

/-- A unit basis transported along an isomorphism. -/
@[simps]
noncomputable def ofIsoBasis (b : UnitBasis X ι) (e : Y ≅ X) : UnitBasis Y ι where
  incl i := b.incl i ≫ e.inv
  proj i := e.hom ≫ b.proj i
  incl_proj i j := by rw [Category.assoc, e.inv_hom_id_assoc, b.incl_proj]
  total := by
    simp only [Category.assoc, ← Preadditive.comp_sum]
    simp only [← Category.assoc, ← Preadditive.sum_comp]
    rw [b.total, Category.comp_id, e.hom_inv_id]

end CategoryTheory.UnitBasis

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The Galois action `x^* M ⟶ σ^* x^* M ≅ (σ ≫ x)^* M = x^* M` at a separably closed point,
followed by an endomorphism `f` of `M`. -/
noncomputable def galoisUpperStarEnd {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X) (h : σ ≫ x = x)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) (f : M ⟶ M) :
    (x)^*⟦Profinite.padicAlgClRingObj l⟧.obj M ⟶ (x)^*⟦Profinite.padicAlgClRingObj l⟧.obj M :=
  (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) σ).inv.app
      ((x)^*⟦Profinite.padicAlgClRingObj l⟧.obj M) ≫
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) σ x).inv.app M ≫
    (CondensedRing.upperStarEqToIso (Profinite.padicAlgClRingObj l) h).hom.app M ≫
    (x)^*⟦Profinite.padicAlgClRingObj l⟧.map f

/-- **The local trace of a scaled Galois action in the two models.** -/
theorem endTensorUnitRingEquiv_traceOrZero_galoisUpperStarEnd {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X)
    (h : σ ≫ x = x) (H : AdicSheaf l X) {r : ℕ}
    (eH : (x)^*ᵃ[l].obj H ≅ ⨁ fun _ : Fin r ↦ AdicSheaf.unit l (Spec (.of Ω)))
    (c : PadicAlgCl l) :
    CondensedRing.endTensorUnitRingEquiv l Ω (traceOrZero (galoisUpperStarEnd σ x h
        ((adicSheafEquivCondensedMod l X).functor.obj H)
        ((adicSheafEquivCondensedMod l X).functor.map (AdicSheaf.smul (ULift.up c) H)))) =
      c * LinearMap.trace (PadicAlgCl l) _
        ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections σ x h H)).hom := by
  sorry

end AlgebraicGeometry.ProEtale
