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

namespace AlgebraicGeometry.Scheme
noncomputable section
variable {W T : Scheme.{u}} (f : W ⟶ T) {V : T.Opens} {t : T} (ht : t ∈ V)

instance : IsPreimmersion (f.fiberLift ht) :=
  have : IsPreimmersion (f.fiberLift ht ≫ (f ⁻¹ᵁ V).ι) := by
    rw [f.fiberLift_ι ht]; infer_instance
  IsPreimmersion.of_comp (f.fiberLift ht) (f ⁻¹ᵁ V).ι

open Modules in
lemma Modules.fiberSectionsOfNhds_comp_fiberLift (F : W.Modules) :
    (eqToHom (pushforward_obj_obj f F V) ≫
        sectionsPullbackLE (f ⁻¹ᵁ V).ι F (f ⁻¹ᵁ V).ι_preimage_self.ge) ≫
      sectionsPullbackOver (f.fiberLift ht) (f.fiberLift_ι ht) F =
    fiberSectionsOfNhds f F t V ht := by
  have h₃ : (⊤ : (f.fiber t).Opens) ≤ (f.fiberLift ht ≫ (f ⁻¹ᵁ V).ι) ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [f.fiberLift_ι ht]
    exact (f.preimage_fiberι_eq_top ht).ge
  rw [fiberSectionsOfNhds, Category.assoc]
  congr 1
  rw [sectionsPullbackOver, sectionsPullback,
    sectionsPullbackLE_comp_assoc _ _ F _ _ h₃, sectionsPullbackLE_congr]

end
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {X : Scheme.{u}}

lemma fiberMap_tensorHom_eq_zero_right {L N : X.Modules} (g : 𝟙_ X.Modules ⟶ L)
    (h : 𝟙_ X.Modules ⟶ N) {x : X} (hh : fiberMap h x = 0) : fiberMap (g ⊗ₘ h) x = 0 := by
  have hnat := fiberTensorIso_hom_naturality g h x
  rw [hh, MonoidalPreadditive.tensor_zero, Limits.comp_zero] at hnat
  exact (Preadditive.IsIso.comp_right_eq_zero _ (fiberTensorIso L N x).hom).1 hnat.symm

lemma fiberMap_pairing_eq_zero_of_right {L N : X.Modules} (e : L ⊗ N ≅ 𝟙_ X.Modules)
    (g : 𝟙_ X.Modules ⟶ L) (h : 𝟙_ X.Modules ⟶ N) {x : X} (hh : fiberMap h x = 0) :
    fiberMap (g ≫ (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom) x = 0 := by
  have hfac : g ≫ (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom
      = (λ_ (𝟙_ X.Modules)).inv ≫ (g ⊗ₘ h) ≫ e.hom := by
    rw [rightUnitor_inv_naturality_assoc, tensorHom_def, unitors_inv_equal]
    simp
  rw [hfac, fiberMap_comp, fiberMap_comp, fiberMap_tensorHom_eq_zero_right g h hh,
    Limits.zero_comp, Limits.comp_zero]

end
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {X X' W : Scheme.{u}}

/-- The comparison isomorphism implicit in `sectionsPullbackOver`. -/
def pullbackOverIso (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W} (hu : u ≫ p' = p) (F : W.Modules) :
    (pullback u).obj ((pullback p').obj F) ≅ (pullback p).obj F :=
  (pullbackComp u p').app F ≪≫ (pullbackCongr hu).app F

lemma sectionsPullbackOver_eq (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W} (hu : u ≫ p' = p)
    (F : W.Modules) (m : Γ((pullback p').obj F, ⊤)) :
    sectionsPullbackOver u hu F m =
      Hom.app (pullbackOverIso u hu F).hom ⊤ (sectionsPullback u ((pullback p').obj F) m) := by
  rw [pullbackOverIso, Iso.trans_hom, Hom.comp_app, sectionsPullbackOver]
  simp

lemma map_homOfSectionTop_eq_zero (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W} (hu : u ≫ p' = p)
    (F : W.Modules) (m : Γ((pullback p').obj F, ⊤)) (hm : sectionsPullbackOver u hu F m = 0) :
    (pullback u).map (homOfSectionTop ((pullback p').obj F) m) = 0 := by
  have hz : sectionsPullback u ((pullback p').obj F) m = 0 := by
    have := (sectionsPullbackOver_eq u hu F m).symm.trans hm
    refine (sectionsEquivOfIso (pullbackOverIso u hu F) ⊤).injective ?_
    rw [map_zero]
    exact this
  rw [← Preadditive.IsIso.comp_left_eq_zero (pullbackUnitIso u).inv, map_homOfSectionTop, hz,
    (homOfSectionTop_eq_zero_iff _ _).2 rfl]
  rfl

end
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {X X' W : Scheme.{u}}

lemma map_homOfSectionTop_over (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W} (hu : u ≫ p' = p)
    (F : W.Modules) (m : Γ((pullback p').obj F, ⊤)) :
    (pullbackUnitIso u).inv ≫ (pullback u).map (homOfSectionTop ((pullback p').obj F) m) ≫
        (pullbackOverIso u hu F).hom =
      homOfSectionTop ((pullback p).obj F) (sectionsPullbackOver u hu F m) := by
  rw [← Category.assoc, map_homOfSectionTop]
  exact (homOfSectionTop_comp _ _).trans
    (congrArg (homOfSectionTop ((pullback p).obj F)) (sectionsPullbackOver_eq u hu F m).symm)

lemma fiberMap_isoComp_eq_zero_iff {M N P Q : X.Modules} (φ : M ⟶ N) (i : P ≅ M) (j : N ≅ Q)
    (x : X) : fiberMap (i.hom ≫ φ ≫ j.hom) x = 0 ↔ fiberMap φ x = 0 := by
  rw [fiberMap_comp, fiberMap_comp, Preadditive.IsIso.comp_left_eq_zero,
    Preadditive.IsIso.comp_right_eq_zero]

lemma fiberMap_homOfSectionTop_eq_zero_iff_over (u : X ⟶ X') {p : X ⟶ W} {p' : X' ⟶ W}
    (hu : u ≫ p' = p) (F : W.Modules) (m : Γ((pullback p').obj F, ⊤)) (x : X)
    [IsIso (u.residueFieldMap x)] :
    fiberMap (homOfSectionTop ((pullback p').obj F) m) (u x) = 0 ↔
      fiberMap (homOfSectionTop ((pullback p).obj F) (sectionsPullbackOver u hu F m)) x = 0 := by
  refine (fiberMap_pullback_map_eq_zero_iff u x
    (homOfSectionTop ((pullback p').obj F) m)).symm.trans ?_
  refine (fiberMap_isoComp_eq_zero_iff ((pullback u).map (homOfSectionTop ((pullback p').obj F) m))
    (pullbackUnitIso u).symm (pullbackOverIso u hu F) x).symm.trans ?_
  exact Iff.of_eq (congrArg (fun ψ ↦ fiberMap ψ x = 0) (map_homOfSectionTop_over u hu F m))

end
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {X : Scheme.{u}} {L N : X.Modules}

/-- **The product of a section of `L` and a section of `N`**, for a tensor inverse pair
`e : L ⊗ N ≅ 𝟙_`, as an endomorphism of the tensor unit. -/
def pairingHom (e : L ⊗ N ≅ 𝟙_ X.Modules) (m : Γ(L, ⊤)) (n : Γ(N, ⊤)) :
    𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
  ((tensorUnitIsoUnit X).hom ≫ homOfSectionTop L m) ≫ (ρ_ L).inv ≫
    (L ◁ ((tensorUnitIsoUnit X).hom ≫ homOfSectionTop N n)) ≫ e.hom

lemma fiberMap_comp_eq_zero_of_left {M M' M'' : X.Modules} (φ : M ⟶ M') (ψ : M' ⟶ M'') (x : X)
    (h : fiberMap φ x = 0) : fiberMap (φ ≫ ψ) x = 0 := by
  rw [fiberMap_comp, h, Limits.zero_comp]

lemma fiberMap_comp_eq_zero_of_right {M M' M'' : X.Modules} (φ : M ⟶ M') (ψ : M' ⟶ M'') (x : X)
    (h : fiberMap ψ x = 0) : fiberMap (φ ≫ ψ) x = 0 := by
  rw [fiberMap_comp, h, Limits.comp_zero]

lemma fiberMap_isoComp_left_eq_zero_iff {M M' M'' : X.Modules} (i : M ≅ M') (φ : M' ⟶ M'')
    (x : X) : fiberMap (i.hom ≫ φ) x = 0 ↔ fiberMap φ x = 0 := by
  rw [fiberMap_comp, Preadditive.IsIso.comp_left_eq_zero]

lemma fiberMap_pairingHom_ne_zero (hL : L.Invertible) (hN : N.Invertible)
    (e : L ⊗ N ≅ 𝟙_ X.Modules) {m : Γ(L, ⊤)} {n : Γ(N, ⊤)} {x : X}
    (hm : fiberMap (homOfSectionTop L m) x ≠ 0) (hn : fiberMap (homOfSectionTop N n) x ≠ 0) :
    fiberMap (pairingHom e m n) x ≠ 0 :=
  have : Nontrivial ((𝟙_ X.Modules).fiber x) :=
    nontrivial_fiber (SheafOfModules.invertible_tensorUnit X.sheaf) x
  fiberMap_ne_zero_of_isIso_fiberMap _ x
    (isIso_fiberMap_comp_of_ne_zero hL hN e _ _
      (fun h ↦ hm ((fiberMap_isoComp_left_eq_zero_iff _ _ x).1 h))
      (fun h ↦ hn ((fiberMap_isoComp_left_eq_zero_iff _ _ x).1 h)))

lemma fiberMap_pairingHom_eq_zero_left (e : L ⊗ N ≅ 𝟙_ X.Modules) {m : Γ(L, ⊤)} {n : Γ(N, ⊤)}
    {x : X} (hm : fiberMap (homOfSectionTop L m) x = 0) : fiberMap (pairingHom e m n) x = 0 :=
  fiberMap_comp_eq_zero_of_left _ _ x (fiberMap_comp_eq_zero_of_right _ _ x hm)

lemma fiberMap_pairingHom_eq_zero_right (e : L ⊗ N ≅ 𝟙_ X.Modules) {m : Γ(L, ⊤)} {n : Γ(N, ⊤)}
    {x : X} (hn : fiberMap (homOfSectionTop N n) x = 0) : fiberMap (pairingHom e m n) x = 0 :=
  fiberMap_pairing_eq_zero_of_right e _ _ (fiberMap_comp_eq_zero_of_right _ _ x hn)

end
end AlgebraicGeometry.Scheme.Modules
