module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FormalTriviality
public import WeilConjectures.AlgebraicGeometry.TrivialityLocus

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X Y : Scheme.{u}}

lemma homOfSectionTop_comp {M M' : X.Modules} (m : Γ(M, ⊤)) (φ : M ⟶ M') :
    homOfSectionTop M m ≫ φ = homOfSectionTop M' (Hom.app φ ⊤ m) :=
  (unitHomEquivTop M').injective <|
    ((ConcreteCategory.congr_hom (Hom.comp_app (homOfSectionTop M m) φ (U := ⊤))
        (oneSection X ⊤)).trans ((ConcreteCategory.comp_apply _ _ _).trans
      (congrArg (ConcreteCategory.hom (Hom.app φ ⊤)) (app_homOfSectionTop_oneSection M m)))).trans
      (app_homOfSectionTop_oneSection M' _).symm

end

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {X Y : Scheme.{u}}

lemma app_pullbackUnitIso_inv_oneSection (a : X ⟶ Y) :
    Hom.app (pullbackUnitIso a).inv ⊤ (oneSection X ⊤) =
      sectionsPullback a (unit Y.ringCatSheaf) (oneSection Y ⊤) := by
  have h1 : Hom.app (pullbackUnitIso a).hom ⊤
      (Hom.app (pullbackUnitIso a).inv ⊤ (oneSection X ⊤)) = oneSection X ⊤ := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id, Hom.id_app,
      ConcreteCategory.id_apply]
  have h2 : Hom.app (pullbackUnitIso a).hom ⊤
      (sectionsPullback a (unit Y.ringCatSheaf) (oneSection Y ⊤)) = oneSection X ⊤ :=
    (app_pullbackUnitIso_hom_sectionsPullback a (oneSection Y ⊤)).trans
      (map_one (ConcreteCategory.hom a.appTop))
  exact (sectionsEquivOfIso (pullbackUnitIso a) ⊤).injective (h1.trans h2.symm)

end
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {X Y : Scheme.{u}}

lemma map_homOfSectionTop (a : X ⟶ Y) (M : Y.Modules) (m : Γ(M, ⊤)) :
    (pullbackUnitIso a).inv ≫ (pullback a).map (homOfSectionTop M m) =
      homOfSectionTop ((pullback a).obj M) (sectionsPullback a M m) := by
  refine (unitHomEquivTop _).injective ?_
  have h1 : Hom.app ((pullbackUnitIso a).inv ≫
      (pullback a).map (homOfSectionTop M m)) ⊤ (oneSection X ⊤) =
      Hom.app ((pullback a).map (homOfSectionTop M m)) ⊤
        (Hom.app (pullbackUnitIso a).inv ⊤ (oneSection X ⊤)) :=
    (ConcreteCategory.congr_hom (Hom.comp_app (pullbackUnitIso a).inv
      ((pullback a).map (homOfSectionTop M m)) (U := ⊤)) (oneSection X ⊤)).trans
      (ConcreteCategory.comp_apply _ _ _)
  have h2 : Hom.app ((pullback a).map (homOfSectionTop M m)) ⊤
      (Hom.app (pullbackUnitIso a).inv ⊤ (oneSection X ⊤)) = sectionsPullback a M m :=
    (congrArg (ConcreteCategory.hom
        (Hom.app ((pullback a).map (homOfSectionTop M m)) ⊤))
      (app_pullbackUnitIso_inv_oneSection a)).trans
      ((sectionsPullback_naturality_apply a (homOfSectionTop M m) (oneSection Y ⊤)).trans
        (congrArg (ConcreteCategory.hom (sectionsPullback a M))
          (app_homOfSectionTop_oneSection M m)))
  exact (h1.trans h2).trans (app_homOfSectionTop_oneSection _ _).symm

end
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme
noncomputable section
variable {W T : Scheme.{u}} (f : W ⟶ T) {V : T.Opens} {t : T} (ht : t ∈ V)

/-- The fibre of `f` over a point of `V` lies over `V`, hence inside `f ⁻¹ᵁ V`. -/
def Hom.fiberLift : f.fiber t ⟶ (f ⁻¹ᵁ V).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ V).ι (f.fiberι t) (by
    rw [Opens.range_ι, f.range_fiberι]
    rintro x (hx : f.base x = t)
    show f.base x ∈ V
    rw [hx]
    exact ht)

@[reassoc (attr := simp)]
lemma Hom.fiberLift_ι : f.fiberLift ht ≫ (f ⁻¹ᵁ V).ι = f.fiberι t :=
  IsOpenImmersion.lift_fac _ _ _

lemma Hom.fiberLift_apply (x : f.fiber t) :
    (f ⁻¹ᵁ V).ι (f.fiberLift ht x) = f.fiberι t x := by
  rw [← f.fiberLift_ι ht]; rfl

end
end AlgebraicGeometry.Scheme
