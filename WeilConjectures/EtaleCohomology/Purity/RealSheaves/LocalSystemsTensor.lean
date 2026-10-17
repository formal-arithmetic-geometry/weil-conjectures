module

public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.ConstructibleSheaf.MonoidalParts
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

instance (X : ModuleCat.{u + 1} Λ) : PreservesFilteredColimitsOfSize.{u, u} (tensorRight X) :=
  ⟨fun _ _ _ ↦ ⟨fun {F} ↦ preservesColimit_of_natIso F
    (BraidedCategory.tensorLeftIsoTensorRight X)⟩⟩

/-- For sheaves `F` and `G`, the sheafification of the presheaf tensor product
`F ⊗ᵖ G` is the sheaf tensor product `F ⊗ G`. -/
def Scheme.sheafifyTensorIso (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (F.obj ⊗ G.obj) ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      F.obj G.obj).symm ≪≫
    tensorIso (asIso ((sheafificationAdjunction _ _).counit.app F))
      (asIso ((sheafificationAdjunction _ _).counit.app G))

/-- The canonical map from the presheaf tensor product `F ⊗ᵖ G` of two sheaves to their sheaf
tensor product `F ⊗ G`: on sections, `σ ⊗ τ ↦ σ ⊗ τ`. -/
def Scheme.tensorToSheafTensor (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  toSheafify _ _ ≫ (Scheme.sheafifyTensorIso F G).hom.hom

@[reassoc]
lemma Scheme.tensorToSheafTensor_naturality
    {F F' G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') (g : G ⟶ G') :
    (f.hom ⊗ₘ g.hom) ≫ Scheme.tensorToSheafTensor F' G' =
      Scheme.tensorToSheafTensor F G ≫ (f ⊗ₘ g).hom := by
  have n₁ : (presheafToSheaf _ _).map f.hom ≫ (sheafificationAdjunction _ _).counit.app F' =
      (sheafificationAdjunction _ _).counit.app F ≫ f :=
    (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.naturality f
  have n₂ : (presheafToSheaf _ _).map g.hom ≫ (sheafificationAdjunction _ _).counit.app G' =
      (sheafificationAdjunction _ _).counit.app G ≫ g :=
    (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.naturality g
  have h : (presheafToSheaf _ _).map (f.hom ⊗ₘ g.hom) ≫ (Scheme.sheafifyTensorIso F' G').hom =
      (Scheme.sheafifyTensorIso F G).hom ≫ (f ⊗ₘ g) := by
    simp only [Scheme.sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
      tensorIso_hom, asIso_hom, Category.assoc]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc (presheafToSheaf _ _) f.hom g.hom,
      tensorHom_comp_tensorHom, n₁, n₂, tensorHom_comp_tensorHom]
  rw [Scheme.tensorToSheafTensor, Scheme.tensorToSheafTensor, toSheafify_naturality_assoc,
    Category.assoc]
  exact congrArg (fun φ ↦ toSheafify _ _ ≫ φ.hom) h


section Stalk

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

instance (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Scheme.pointSmallEtale s).presheafFiber.map (Scheme.tensorToSheafTensor F G)) := by
  rw [Scheme.tensorToSheafTensor, Functor.map_comp]
  have : IsIso (Scheme.sheafifyTensorIso F G).hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).mapIso (Scheme.sheafifyTensorIso F G)).hom)
  infer_instance

/-- The stalk at `s` of a tensor product of sheaves of `Λ`-modules is the tensor product of the
stalks, `(F ⊗ G)_s ≅ F_s ⊗ G_s`: the stalk of the presheaf tensor product is the tensor product of
the stalks, and sheafifying does not change stalks. It sends the germ of `σ ⊗ τ` to
`σ_s ⊗ τ_s` (`AlgebraicGeometry.Scheme.sheafFiberTensorIso'_inv_tmul`). -/
def Scheme.sheafFiberTensorIso' (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Scheme.pointSmallEtale s).sheafFiber.obj (F ⊗ G) ≅
      (Scheme.pointSmallEtale s).sheafFiber.obj F ⊗ (Scheme.pointSmallEtale s).sheafFiber.obj G :=
  (asIso ((Scheme.pointSmallEtale s).presheafFiber.map (Scheme.tensorToSheafTensor F G))).symm ≪≫
    (Functor.Monoidal.μIso (Scheme.pointSmallEtale s).presheafFiber F.obj G.obj).symm

lemma Scheme.sheafFiberTensorIso'_inv (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Scheme.sheafFiberTensorIso' s F G).inv =
      Functor.LaxMonoidal.μ (Scheme.pointSmallEtale s).presheafFiber F.obj G.obj ≫
        (Scheme.pointSmallEtale s).presheafFiber.map (Scheme.tensorToSheafTensor F G) :=
  rfl

/-- `AlgebraicGeometry.Scheme.sheafFiberTensorIso'` on germs: the germ at `s` of `σ ⊗ τ` is
`σ_s ⊗ τ_s`. -/
lemma Scheme.sheafFiberTensorIso'_inv_tmul (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V) (σ : F.obj.obj (.op V))
    (τ : G.obj.obj (.op V)) :
    (Scheme.sheafFiberTensorIso' s F G).inv.hom
        ((Scheme.pointSmallEtale s).toPresheafFiber V v F.obj σ ⊗ₜ
          (Scheme.pointSmallEtale s).toPresheafFiber V v G.obj τ) =
      (Scheme.pointSmallEtale s).toPresheafFiber V v (F ⊗ G).obj
        ((Scheme.tensorToSheafTensor F G).app (.op V) (σ ⊗ₜ τ)) := by
  have h := ConcreteCategory.congr_hom
    (GrothendieckTopology.Point.tensorHom_comp_toPresheafFiber_μ (Scheme.pointSmallEtale s) V v
      F.obj G.obj) (σ ⊗ₜ τ)
  rw [Scheme.sheafFiberTensorIso'_inv, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ConcreteCategory.comp_apply] at h
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul] at h
  erw [h]
  exact (Scheme.pointSmallEtale s).toPresheafFiber_naturality_apply _ V v _

/-- Naturality of `AlgebraicGeometry.Scheme.sheafFiberTensorIso'` in both variables. -/
@[reassoc]
lemma Scheme.sheafFiberTensorIso'_hom_naturality
    {F F' G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') (g : G ⟶ G') :
    (Scheme.pointSmallEtale s).sheafFiber.map (f ⊗ₘ g) ≫ (Scheme.sheafFiberTensorIso' s F' G').hom =
      (Scheme.sheafFiberTensorIso' s F G).hom ≫
        ((Scheme.pointSmallEtale s).sheafFiber.map f ⊗ₘ
          (Scheme.pointSmallEtale s).sheafFiber.map g) := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv, Scheme.sheafFiberTensorIso'_inv,
    Scheme.sheafFiberTensorIso'_inv, Category.assoc]
  change _ = ((Scheme.pointSmallEtale s).presheafFiber.map f.hom ⊗ₘ
    (Scheme.pointSmallEtale s).presheafFiber.map g.hom) ≫ _
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp,
    Scheme.tensorToSheafTensor_naturality, Functor.map_comp]
  rfl

end Stalk

end AlgebraicGeometry
