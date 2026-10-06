/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import WeilConjectures.CategoryTheory.ModuleObjects.Bimod
public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive

/-!

# Extension and restriction of scalars for module objects

Let `(C, ⊗, 𝟙)` be a monoidal category and `φ : R ⟶ S` a morphism of algebra objects
(`[IsMonHom φ]`).

* *Restriction of scalars* along `φ` is the functor `Mod.comap φ : Mod C S ⥤ Mod C R` of
  Mathlib: an `S`-module object `N` becomes an `R`-module object with action
  `R ⊗ N ⟶ S ⊗ N ⟶ N`. It is faithful, commutes with the forgetful functors, and is additive
  when `C` is monoidal preadditive. We record its compatibility with identities and compositions
  (`Mod.comapId`, `Mod.comapComp`).

* *Extension of scalars* along `φ` is the functor `Mod.extendScalars φ : Mod C R ⥤ Mod C S`,
  `M ↦ S ⊗_R M`, defined when `C` is braided with coequalizers preserved by the tensor product,
  and `R` is commutative: `S` is an `S`-`R`-bimodule via `φ` (`Bimod.ofMonHom φ`), `M` is an
  `R`-`R`-bimodule since `R` is commutative (`Mod.toBimodObj`), and `S ⊗_R M` is the tensor
  product of bimodules `Bimod.tensorBimod`, regarded as a left `S`-module. Concretely, `S ⊗_R M`
  is the coequalizer of the two maps `S ⊗ R ⊗ M ⇉ S ⊗ M` given by the right action of `R` on `S`
  through `φ` and the action of `R` on `M`, with `S` acting through the first factor.

The main result is the adjunction `Mod.extendRestrictAdjunction φ : extendScalars φ ⊣ comap φ`:
an `S`-linear map `S ⊗_R M ⟶ N` is the same as an `R`-linear map `M ⟶ N` into the restriction
of `N`. Consequently, extension of scalars preserves colimits, is additive in the preadditive
setting, and is compatible with identities and compositions (`Mod.extendScalarsId`,
`Mod.extendScalarsComp`), by uniqueness of left adjoints.

Maps out of `S ⊗_R M` are constructed with `Mod.extendDesc`, from a map `S ⊗ M ⟶ N` which
coequalizes the two actions of `R` and is `S`-linear in the first factor; equalities between
such maps are checked after precomposition with the epimorphism
`Mod.extendπ φ M : S ⊗ M ⟶ S ⊗_R M` (`Mod.extendScalarsObj_hom_ext`).

The derived functor of extension of scalars is constructed in
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Restriction of scalars -/

namespace Mod

section Restriction

variable {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]

lemma comap_obj_smul (N : Mod C S) : γ[R,((comap φ).obj N).X] = φ ▷ N.X ≫ γ[S,N.X] := rfl

instance : (comap φ : Mod C S ⥤ Mod C R).Faithful where
  map_injective h := by
    have := congrArg Hom.hom h
    exact hom_ext _ _ this

lemma comap_comp_forget : comap φ ⋙ forget R = (forget S : Mod C S ⥤ C) := rfl

/-- Restriction of scalars along the identity is the identity. -/
@[simps!]
def comapId : (comap (𝟙 R) : Mod C R ⥤ Mod C R) ≅ 𝟭 (Mod C R) :=
  NatIso.ofComponents (fun M ↦ isoMk (Iso.refl M.X) (by
    change (𝟙 R ▷ M.X ≫ γ[R,M.X]) ≫ 𝟙 _ = R ◁ 𝟙 _ ≫ γ[R,M.X]
    simp)) (fun f ↦ by
      ext
      exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

variable {T : C} [MonObj T] (ψ : S ⟶ T) [IsMonHom ψ]

/-- Restriction of scalars along a composition is the composition of the restrictions. -/
@[simps!]
def comapComp : (comap (φ ≫ ψ) : Mod C T ⥤ Mod C R) ≅ comap ψ ⋙ comap φ :=
  NatIso.ofComponents (fun M ↦ isoMk (Iso.refl M.X) (by
    change ((φ ≫ ψ) ▷ M.X ≫ γ[T,M.X]) ≫ 𝟙 _ = R ◁ 𝟙 _ ≫ φ ▷ M.X ≫ ψ ▷ M.X ≫ γ[T,M.X]
    simp)) (fun f ↦ by
      ext
      exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

instance : (comap φ : Mod C S ⥤ Mod C R).Additive where
  map_add := hom_ext _ _ rfl

end Preadditive

end Restriction

end Mod

/-! ### An algebra object as a bimodule over its scalars -/

namespace MonoidalCategory

@[reassoc]
lemma whiskerLeft_leftUnitor_inv_associator_inv (X Y : C) :
    X ◁ (λ_ Y).inv ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ▷ Y := by
  rw [← triangle_assoc_comp_right_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end MonoidalCategory

namespace MonObj

variable {R S : C} [MonObj S] (φ : R ⟶ S)

/-- Multiplying the unit of `S` by the image of `r : R` gives the image of `r`. -/
@[reassoc]
lemma leftUnitor_inv_one_whiskerRight_whiskerLeft_mul :
    (λ_ R).inv ≫ η[S] ▷ R ≫ S ◁ φ ≫ μ[S] = φ := by
  rw [← whisker_exchange_assoc, MonObj.one_mul, leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- Multiplying the image of `r : R` by the unit of `S` gives the image of `r`. -/
@[reassoc]
lemma rightUnitor_inv_whiskerLeft_one_whiskerRight_mul :
    (ρ_ R).inv ≫ R ◁ η[S] ≫ φ ▷ S ≫ μ[S] = φ := by
  rw [whisker_exchange_assoc, MonObj.mul_one, rightUnitor_naturality, Iso.inv_hom_id_assoc]

end MonObj

namespace Bimod

variable {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- An algebra object `S` as an `S`-`R`-bimodule along a morphism of algebra objects
`φ : R ⟶ S`: `S` acts on the left by multiplication and `R` acts on the right by multiplication
through `φ`. -/
@[simps]
def ofMonHom : Bimod (Mon.mk S) (Mon.mk R) where
  X := S
  actLeft := μ[S]
  actRight := S ◁ φ ≫ μ[S]
  actRight_one := by
    change S ◁ η[R] ≫ S ◁ φ ≫ μ[S] = (ρ_ S).hom
    rw [← whiskerLeft_comp_assoc, IsMonHom.one_hom, MonObj.mul_one]
  right_assoc := by
    change S ◁ μ[R] ≫ S ◁ φ ≫ μ[S] =
      (α_ S R R).inv ≫ (S ◁ φ ≫ μ[S]) ▷ R ≫ S ◁ φ ≫ μ[S]
    rw [← whiskerLeft_comp_assoc, IsMonHom.mul_hom, whiskerLeft_comp_assoc, MonObj.mul_assoc_flip,
      tensorHom_def, whiskerLeft_comp_assoc, associator_inv_naturality_right_assoc,
      associator_inv_naturality_middle_assoc, comp_whiskerRight, Category.assoc,
      ← whisker_exchange_assoc μ[S] φ]
  middle_assoc := by
    change μ[S] ▷ R ≫ S ◁ φ ≫ μ[S] = (α_ S S R).hom ≫ S ◁ (S ◁ φ ≫ μ[S]) ≫ μ[S]
    rw [← whisker_exchange_assoc μ[S] φ, MonObj.mul_assoc, whiskerLeft_comp_assoc,
      ← associator_naturality_right_assoc]

end Bimod

/-! ### Extension of scalars -/

namespace Mod

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

section Object

variable (M : Mod C R)

/-- The `S`-`R`-bimodule `S ⊗_R M`, for an `R`-module object `M`. -/
noncomputable abbrev extendScalarsBimod : Bimod (Mon.mk S) (Mon.mk R) :=
  (Bimod.ofMonHom φ).tensorBimod (toBimodObj R M)

/-- The `S`-module object `S ⊗_R M` obtained from an `R`-module object `M` by extension of
scalars along `φ : R ⟶ S`. -/
noncomputable def extendScalarsObj : Mod C S :=
  letI : ModObj S (extendScalarsBimod φ M).X :=
    { smul := (extendScalarsBimod φ M).actLeft
      one_smul := (extendScalarsBimod φ M).one_actLeft
      mul_smul := (extendScalarsBimod φ M).left_assoc }
  ⟨(extendScalarsBimod φ M).X⟩

/-- `S ⊗_R M` is the coequalizer of the right action of `R` on `S` through `φ` and of the
action of `R` on `M`. -/
lemma extendScalarsObj_X : (extendScalarsObj φ M).X =
    coequalizer ((S ◁ φ ≫ μ[S]) ▷ M.X) ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) :=
  rfl

lemma extendScalarsObj_smul :
    γ[S,(extendScalarsObj φ M).X] = (extendScalarsBimod φ M).actLeft :=
  rfl

/-- The projection `S ⊗ M ⟶ S ⊗_R M`. -/
noncomputable def extendπ : S ⊗ M.X ⟶ (extendScalarsObj φ M).X :=
  coequalizer.π ((S ◁ φ ≫ μ[S]) ▷ M.X) ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X])

@[reassoc]
lemma extendπ_condition :
    (S ◁ φ ≫ μ[S]) ▷ M.X ≫ extendπ φ M = ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) ≫ extendπ φ M :=
  coequalizer.condition _ _

@[reassoc]
lemma whiskerLeft_smul_extendπ :
    S ◁ γ[R,M.X] ≫ extendπ φ M = (α_ S R M.X).inv ≫ (S ◁ φ ≫ μ[S]) ▷ M.X ≫ extendπ φ M := by
  rw [extendπ_condition, Category.assoc, Iso.inv_hom_id_assoc]

/-- `extendπ φ M` exhibits `S ⊗_R M` as the coequalizer of the two actions of `R`. -/
noncomputable def isColimitExtendπ :
    IsColimit (Cofork.ofπ (extendπ φ M) (extendπ_condition φ M) :
      Cofork ((S ◁ φ ≫ μ[S]) ▷ M.X) ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X])) :=
  coequalizerIsCoequalizer _ _

instance : Epi (extendπ φ M) := by
  dsimp [extendπ]
  infer_instance

instance (X : C) : Epi (X ◁ extendπ φ M) :=
  (tensorLeft X).map_epi (extendπ φ M)

/-- The action of `S` on `S ⊗_R M` is induced by the multiplication of `S`. -/
@[reassoc]
lemma whiskerLeft_extendπ_smul :
    S ◁ extendπ φ M ≫ γ[S,(extendScalarsObj φ M).X] =
      (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ extendπ φ M :=
  Bimod.TensorBimod.whiskerLeft_π_actLeft (Bimod.ofMonHom φ) (toBimodObj R M)

variable {M} in
/-- The morphism `S ⊗_R M ⟶ Y` of `C` induced by a map `g : S ⊗ M ⟶ Y` which coequalizes the
two actions of `R`. -/
noncomputable def extendDescHom {Y : C} (g : S ⊗ M.X ⟶ Y)
    (hg : (S ◁ φ ≫ μ[S]) ▷ M.X ≫ g = ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) ≫ g) :
    (extendScalarsObj φ M).X ⟶ Y :=
  coequalizer.desc g hg

variable {M} in
@[reassoc (attr := simp)]
lemma extendπ_extendDescHom {Y : C} (g : S ⊗ M.X ⟶ Y) (hg) :
    extendπ φ M ≫ extendDescHom φ g hg = g :=
  coequalizer.π_desc _ _

variable {M} in
/-- Construct an `S`-linear map `S ⊗_R M ⟶ N` from a map `g : S ⊗ M ⟶ N` which coequalizes the
two actions of `R` and is `S`-linear in the first factor. -/
noncomputable def extendDesc {N : Mod C S} (g : S ⊗ M.X ⟶ N.X)
    (hg : (S ◁ φ ≫ μ[S]) ▷ M.X ≫ g = ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) ≫ g)
    (hg' : S ◁ g ≫ γ[S,N.X] = (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ g) :
    extendScalarsObj φ M ⟶ N :=
  Hom.mk' (extendDescHom φ g hg) (by
    change γ[S,(extendScalarsObj φ M).X] ≫ extendDescHom φ g hg =
      S ◁ extendDescHom φ g hg ≫ γ[S,N.X]
    rw [← cancel_epi (S ◁ extendπ φ M), whiskerLeft_extendπ_smul_assoc, extendπ_extendDescHom,
      ← whiskerLeft_comp_assoc, extendπ_extendDescHom, hg'])

variable {M} in
@[reassoc (attr := simp)]
lemma extendπ_extendDesc {N : Mod C S} (g : S ⊗ M.X ⟶ N.X) (hg) (hg') :
    extendπ φ M ≫ (extendDesc φ g hg hg').hom = g :=
  coequalizer.π_desc _ _

variable {M} in
lemma extendScalarsObj_hom_ext {N : Mod C S} {f g : extendScalarsObj φ M ⟶ N}
    (h : extendπ φ M ≫ f.hom = extendπ φ M ≫ g.hom) : f = g :=
  hom_ext _ _ ((cancel_epi (extendπ φ M)).1 h)

end Object

section Functor

variable {M N : Mod C R} (f : M ⟶ N)

@[reassoc]
lemma actRight_whiskerRight_whiskerLeft_extendπ :
    (S ◁ φ ≫ μ[S]) ▷ M.X ≫ S ◁ f.hom ≫ extendπ φ N =
      ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) ≫ S ◁ f.hom ≫ extendπ φ N := by
  rw [← whisker_exchange_assoc, extendπ_condition]
  simp only [Category.assoc]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc,
    smul_hom]

@[reassoc]
lemma whiskerLeft_whiskerLeft_extendπ_smul :
    S ◁ (S ◁ f.hom ≫ extendπ φ N) ≫ γ[S,(extendScalarsObj φ N).X] =
      (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ S ◁ f.hom ≫ extendπ φ N := by
  rw [whiskerLeft_comp_assoc, whiskerLeft_extendπ_smul, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]

/-- The `S`-linear map `S ⊗_R M ⟶ S ⊗_R N` induced by an `R`-linear map `M ⟶ N`. -/
noncomputable def extendScalarsMap : extendScalarsObj φ M ⟶ extendScalarsObj φ N :=
  extendDesc φ (S ◁ f.hom ≫ extendπ φ N) (actRight_whiskerRight_whiskerLeft_extendπ φ f)
    (whiskerLeft_whiskerLeft_extendπ_smul φ f)

@[reassoc (attr := simp)]
lemma extendπ_extendScalarsMap :
    extendπ φ M ≫ (extendScalarsMap φ f).hom = S ◁ f.hom ≫ extendπ φ N :=
  extendπ_extendDesc φ _ _ _

/-- Extension of scalars along a morphism of algebra objects `φ : R ⟶ S`, with `R` commutative:
the functor `M ↦ S ⊗_R M` from `R`-module objects to `S`-module objects. -/
@[simps obj map]
noncomputable def extendScalars : Mod C R ⥤ Mod C S where
  obj := extendScalarsObj φ
  map := extendScalarsMap φ
  map_id M := extendScalarsObj_hom_ext φ (by simp)
  map_comp f g := extendScalarsObj_hom_ext φ (by simp [extendπ_extendScalarsMap_assoc])

end Functor

/-! ### The adjunction between extension and restriction of scalars -/

section Adjunction

variable (M : Mod C R)

/-- The unit `M ⟶ S ⊗_R M`, `m ↦ 1 ⊗ m`, as a morphism of `C`. -/
noncomputable def extendUnitHom : M.X ⟶ (extendScalarsObj φ M).X :=
  (λ_ M.X).inv ≫ η[S] ▷ M.X ≫ extendπ φ M

/-- The unit is `R`-linear: `r • (1 ⊗ m) = φ(r) ⊗ m`. -/
@[reassoc]
lemma smul_extendUnitHom : γ[R,M.X] ≫ extendUnitHom φ M = φ ▷ M.X ≫ extendπ φ M := by
  change (γ[R,M.X] ≫ (λ_ M.X).inv ≫ η[S] ▷ M.X ≫ extendπ φ M : R ⊗ M.X ⟶ _) = _
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, whiskerLeft_smul_extendπ,
    leftUnitor_tensor_inv, Category.assoc, ← associator_naturality_left_assoc,
    Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc,
    MonObj.leftUnitor_inv_one_whiskerRight_whiskerLeft_mul]

/-- The unit is `R`-linear: `1 ⊗ (r • m) = φ(r) ⊗ m`. -/
@[reassoc]
lemma whiskerLeft_extendUnitHom_smul :
    R ◁ extendUnitHom φ M ≫ φ ▷ (extendScalarsObj φ M).X ≫ γ[S,(extendScalarsObj φ M).X] =
      φ ▷ M.X ≫ extendπ φ M := by
  dsimp only [extendUnitHom]
  rw [whiskerLeft_comp_assoc, whiskerLeft_comp_assoc, whisker_exchange_assoc,
    whiskerLeft_extendπ_smul, associator_inv_naturality_left_assoc,
    associator_inv_naturality_middle_assoc, whiskerLeft_leftUnitor_inv_associator_inv_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [MonObj.rightUnitor_inv_whiskerLeft_one_whiskerRight_mul]

/-- The unit followed by the action of `S` is the projection: `s • (1 ⊗ m) = s ⊗ m`. -/
@[reassoc]
lemma whiskerLeft_extendUnitHom_smul' :
    S ◁ extendUnitHom φ M ≫ γ[S,(extendScalarsObj φ M).X] = extendπ φ M := by
  dsimp only [extendUnitHom]
  rw [whiskerLeft_comp_assoc, whiskerLeft_comp_assoc, whiskerLeft_extendπ_smul,
    associator_inv_naturality_middle_assoc, whiskerLeft_leftUnitor_inv_associator_inv_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, MonObj.mul_one,
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

/-- The unit `M ⟶ S ⊗_R M` of the extension-restriction adjunction. -/
noncomputable def extendUnit : M ⟶ (comap φ).obj (extendScalarsObj φ M) :=
  Hom.mk' (extendUnitHom φ M) (by
    change γ[R,M.X] ≫ extendUnitHom φ M =
      R ◁ extendUnitHom φ M ≫ φ ▷ (extendScalarsObj φ M).X ≫ γ[S,(extendScalarsObj φ M).X]
    rw [smul_extendUnitHom, whiskerLeft_extendUnitHom_smul])

@[simp]
lemma extendUnit_hom : (extendUnit φ M).hom = extendUnitHom φ M := rfl

variable {M} in
/-- The `S`-linear map `S ⊗_R M ⟶ N` extending a map `g : M ⟶ N` of `C` which is `R`-linear
for the action of `R` on `N` through `φ`. -/
noncomputable def extendHomOfHom {N : Mod C S} (g : M.X ⟶ N.X)
    (hg : γ[R,M.X] ≫ g = R ◁ g ≫ φ ▷ N.X ≫ γ[S,N.X]) : extendScalarsObj φ M ⟶ N :=
  extendDesc φ (S ◁ g ≫ γ[S,N.X])
    (by
      rw [Category.assoc, ← whiskerLeft_comp_assoc, hg, whiskerLeft_comp_assoc,
        whiskerLeft_comp_assoc, ModObj.mul_smul_self_flip, associator_inv_naturality_middle_assoc,
        associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc, whisker_exchange_assoc,
        whisker_exchange_assoc, comp_whiskerRight_assoc])
    (by
      rw [whiskerLeft_comp_assoc, ModObj.mul_smul_self_flip, associator_inv_naturality_right_assoc,
        whisker_exchange_assoc])

variable {M} in
@[reassoc (attr := simp)]
lemma extendπ_extendHomOfHom {N : Mod C S} (g : M.X ⟶ N.X) (hg) :
    extendπ φ M ≫ (extendHomOfHom φ g hg).hom = S ◁ g ≫ γ[S,N.X] :=
  extendπ_extendDesc φ _ _ _

variable {M} in
@[reassoc (attr := simp)]
lemma extendUnitHom_extendHomOfHom {N : Mod C S} (g : M.X ⟶ N.X) (hg) :
    extendUnitHom φ M ≫ (extendHomOfHom φ g hg).hom = g := by
  dsimp only [extendUnitHom]
  simp only [Category.assoc]
  rw [extendπ_extendHomOfHom, ← whisker_exchange_assoc, ModObj.one_smul_self,
    leftUnitor_naturality, Iso.inv_hom_id_assoc]

variable {M} in
/-- The `S`-linear map `S ⊗_R M ⟶ N` extending an `R`-linear map `M ⟶ N`. -/
noncomputable def extendHom {N : Mod C S} (f : M ⟶ (comap φ).obj N) : extendScalarsObj φ M ⟶ N :=
  extendHomOfHom φ f.hom (smul_hom f)

variable {M} in
@[reassoc (attr := simp)]
lemma extendπ_extendHom {N : Mod C S} (f : M ⟶ (comap φ).obj N) :
    extendπ φ M ≫ (extendHom φ f).hom = S ◁ f.hom ≫ γ[S,N.X] :=
  extendπ_extendHomOfHom φ _ _

variable {M} in
@[reassoc (attr := simp)]
lemma extendUnitHom_extendHom {N : Mod C S} (f : M ⟶ (comap φ).obj N) :
    extendUnitHom φ M ≫ (extendHom φ f).hom = f.hom :=
  extendUnitHom_extendHomOfHom φ _ _

/-- `S`-linear maps `S ⊗_R M ⟶ N` correspond to `R`-linear maps `M ⟶ N`. -/
@[simps]
noncomputable def extendHomEquiv (N : Mod C S) :
    (extendScalarsObj φ M ⟶ N) ≃ (M ⟶ (comap φ).obj N) where
  toFun g := extendUnit φ M ≫ (comap φ).map g
  invFun := extendHom φ
  left_inv g := extendScalarsObj_hom_ext φ (by
    rw [extendπ_extendHom, comp_hom', comap_map_hom, extendUnit_hom, whiskerLeft_comp_assoc,
      ← smul_hom g, whiskerLeft_extendUnitHom_smul'_assoc])
  right_inv f := hom_ext _ _ (by simp)

/-- Extension of scalars is left adjoint to restriction of scalars. -/
noncomputable def extendRestrictAdjunction : extendScalars φ ⊣ comap φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extendHomEquiv φ
      homEquiv_naturality_left_symm {M M' N} f g := by
        change extendHom φ (f ≫ g) = extendScalarsMap φ f ≫ extendHom φ g
        refine extendScalarsObj_hom_ext φ ?_
        rw [extendπ_extendHom, comp_hom', comp_hom', extendπ_extendScalarsMap_assoc,
          extendπ_extendHom, whiskerLeft_comp_assoc]
      homEquiv_naturality_right f g := by
        change extendUnit φ _ ≫ (comap φ).map (f ≫ g) =
          (extendUnit φ _ ≫ (comap φ).map f) ≫ (comap φ).map g
        rw [Functor.map_comp, Category.assoc] }

instance : (extendScalars φ).IsLeftAdjoint := (extendRestrictAdjunction φ).isLeftAdjoint

instance : (comap φ : Mod C S ⥤ Mod C R).IsRightAdjoint :=
  (extendRestrictAdjunction φ).isRightAdjoint

/-- Extension of scalars preserves colimits, being a left adjoint. -/
noncomputable instance : PreservesColimitsOfSize.{v, u} (extendScalars φ) :=
  (extendRestrictAdjunction φ).leftAdjoint_preservesColimits

/-- Restriction of scalars preserves limits, being a right adjoint. -/
noncomputable instance : PreservesLimitsOfSize.{v, u} (comap φ : Mod C S ⥤ Mod C R) :=
  (extendRestrictAdjunction φ).rightAdjoint_preservesLimits

end Adjunction

/-! ### Compatibilities of extension of scalars -/

section Compatibilities

/-- Extension of scalars along the identity is the identity. -/
noncomputable def extendScalarsId : extendScalars (𝟙 R) ≅ 𝟭 (Mod C R) :=
  (extendRestrictAdjunction (𝟙 R)).leftAdjointUniq (Adjunction.id.ofNatIsoRight comapId.symm)

variable {T : C} [MonObj T] [IsCommMonObj S] (ψ : S ⟶ T) [IsMonHom ψ]

/-- Extension of scalars along a composition is the composition of the extensions. -/
noncomputable def extendScalarsComp :
    extendScalars (φ ≫ ψ) ≅ extendScalars φ ⋙ extendScalars ψ :=
  (extendRestrictAdjunction (φ ≫ ψ)).leftAdjointUniq
    (((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
      (comapComp φ ψ).symm)

end Compatibilities

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

instance : (extendScalars φ).Additive where
  map_add {M N f g} := extendScalarsObj_hom_ext φ (by
    simp [MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add])

end Preadditive

end Mod

end CategoryTheory
