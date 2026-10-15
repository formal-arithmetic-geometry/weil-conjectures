/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom

/-!
# Internal homs of Weil complexes

Let `Λ` be a finite coefficient ring and `g` an automorphism of a scheme `X` of finite type over a
field on which the exponent of `Λ` is invertible. The *internal-Hom Frobenius* of two Weil
complexes `(K, φ_K)` and `(L, φ_L)` is the composite
`Lg^* RHom(K, L) ≅ RHom(Lg^* K, Lg^* L) ⟶ RHom(K, L)`, the second arrow being
`RHom(φ_K⁻¹, φ_L)` (`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius`). The first arrow
is the comparison map of the monoidal functor `Lg^*`, an isomorphism because `Lg^*` is an
equivalence, `g` being an automorphism.

With this Frobenius the derived internal hom becomes a bifunctor
`RHom(-, -) : WeilDᵒᵖ × WeilD ⥤ WeilD` (`AlgebraicGeometry.Etale.WeilComplex.internalHom`)
lying over the derived internal hom of `Dctf(X, Λ)`, which is triangulated in its second
variable. See `WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom` for the model of the
Weil category used here.

## Main definitions

- `AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius` (`def-wf-internal-hom`).
- `AlgebraicGeometry.Etale.WeilComplex.internalHom` (`lem-wf-internal-hom-weil`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

namespace WeilComplex

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}} {g : X ≅ X}

omit [Finite Λ] in
/-- The compatibility of a morphism of Weil complexes with the inverses of the Weil structures,
in `D(X_ét)`. -/
@[reassoc]
lemma frobenius_inv_hom_comp_map {K L : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K ⟶ L) :
    K.frobenius.inv.hom ≫ L((g.hom)^*[ModuleCat.{u + 1} Λ]).map f.hom.hom =
      f.hom.hom ≫ L.frobenius.inv.hom := by
  rw [← cancel_mono ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).hom]
  rw [Category.assoc, Category.assoc]
  change _ = _ ≫ ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).inv ≫
    ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius).hom
  rw [Iso.inv_hom_id, Category.comp_id]
  change _ ≫ _ ≫ L.frobenius.hom.hom = _
  rw [← frobenius_hom_comp_hom]
  change ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius).inv ≫
    ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

variable {k : Type u} [Field k] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasInvertibleExponent Λ X]

/-- Blueprint `def-wf-internal-hom`: the *internal-Hom Frobenius* of two Weil complexes
`(K, φ_K)` and `(L, φ_L)`, the Weil structure
`Lg^* RHom(K, L) ≅ RHom(Lg^* K, Lg^* L) ≅ RHom(K, L)` on `RHom(K, L)`, whose first arrow is the
comparison map of the monoidal equivalence `Lg^*` and whose second arrow is
`RHom(φ_K⁻¹, φ_L)`. -/
noncomputable def internalHomFrobenius (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).obj
        (((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).obj L.obj) ≅
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).obj L.obj :=
  ObjectProperty.isoMk _
    (leftDerivedUpperStarDerivedHomIso (ModuleCat.{u + 1} Λ) g.hom K.obj.obj L.obj.obj ≪≫
      (RHom(X)[ModuleCat.{u + 1} Λ].mapIso
        ((DerivedCategoryFiniteTor.ι _ X).mapIso K.frobenius).symm.op).app _ ≪≫
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).mapIso
        ((DerivedCategoryFiniteTor.ι _ X).mapIso L.frobenius))

lemma internalHomFrobenius_hom_hom (K L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomFrobenius aX K L).hom.hom =
      leftDerivedUpperStarDerivedHomComparison (ModuleCat.{u + 1} Λ) g.hom K.obj.obj L.obj.obj ≫
        (RHom(X)[ModuleCat.{u + 1} Λ].map K.frobenius.inv.hom.op).app _ ≫
          (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map L.frobenius.hom.hom :=
  rfl

/-- The internal-Hom Frobenius is natural in the second variable. -/
lemma internalHomFrobenius_hom_comp_map_right (K : WeilComplex (ModuleCat.{u + 1} Λ) g)
    {L L' : WeilComplex (ModuleCat.{u + 1} Λ) g} (h : L ⟶ L') :
    (internalHomFrobenius aX K L).hom ≫
        ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).map h.hom =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).map
          (((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).map h.hom) ≫
        (internalHomFrobenius aX K L').hom := by
  apply ObjectProperty.hom_ext
  change (internalHomFrobenius aX K L).hom.hom ≫
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map h.hom.hom =
    L((g.hom)^*[ModuleCat.{u + 1} Λ]).map
        ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map h.hom.hom) ≫
      (internalHomFrobenius aX K L').hom.hom
  rw [internalHomFrobenius_hom_hom, internalHomFrobenius_hom_hom,
    leftDerivedUpperStarDerivedHomComparison_naturality_right_assoc, Category.assoc,
    Category.assoc, NatTrans.naturality_assoc, ← Functor.map_comp, ← Functor.map_comp,
    frobenius_hom_comp_hom]

omit [Finite Λ] [HasInvertibleExponent Λ X] in
/-- The naturality of the internal-Hom Frobenius in the first variable, in `D(X_ét)`: an instance
of `AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedHomComparison_comp_naturality_left`. -/
lemma internalHomFrobenius_aux {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g}
    (f : K' ⟶ K) (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (leftDerivedUpperStarDerivedHomComparison (ModuleCat.{u + 1} Λ) g.hom K.obj.obj L.obj.obj ≫
      (RHom(X)[ModuleCat.{u + 1} Λ].map K.frobenius.inv.hom.op).app _ ≫
        (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K.obj.obj)).map L.frobenius.hom.hom) ≫
      (RHom(X)[ModuleCat.{u + 1} Λ].map f.hom.hom.op).app L.obj.obj =
    L((g.hom)^*[ModuleCat.{u + 1} Λ]).map ((RHom(X)[ModuleCat.{u + 1} Λ].map f.hom.hom.op).app
        L.obj.obj) ≫
      leftDerivedUpperStarDerivedHomComparison (ModuleCat.{u + 1} Λ) g.hom K'.obj.obj L.obj.obj ≫
        (RHom(X)[ModuleCat.{u + 1} Λ].map K'.frobenius.inv.hom.op).app _ ≫
          (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K'.obj.obj)).map L.frobenius.hom.hom :=
  leftDerivedUpperStarDerivedHomComparison_comp_naturality_left _ g.hom f.hom.hom _ _ _
    (frobenius_inv_hom_comp_map f)

/-- The internal-Hom Frobenius is natural in the first variable. -/
lemma internalHomFrobenius_hom_comp_map_left {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g}
    (f : K' ⟶ K) (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomFrobenius aX K L).hom ≫
        ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj =
      (DerivedCategoryFiniteTor.leftDerivedUpperStar _ g.hom).map
          (((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj) ≫
        (internalHomFrobenius aX K' L).hom := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    internalHomFrobenius_hom_hom, internalHomFrobenius_hom_hom,
    DerivedCategoryFiniteTor.leftDerivedUpperStar_map_hom,
    DerivedCategoryFiniteTor.derivedHom_map_app_hom, Quiver.Hom.unop_op]
  exact internalHomFrobenius_aux f L

/-- The derived internal hom `RHom(K, -)` of a Weil complex `K`, as an endofunctor of Weil
complexes: the Weil structure of `RHom(K, L)` is the internal-Hom Frobenius
(`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius`). -/
noncomputable def internalHomObj (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    WeilComplex (ModuleCat.{u + 1} Λ) g ⥤ WeilComplex (ModuleCat.{u + 1} Λ) g where
  obj L := ⟨((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).obj L.obj,
    internalHomFrobenius aX K L⟩
  map h := ⟨((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).map h.hom,
    internalHomFrobenius_hom_comp_map_right aX K h⟩
  map_id L := hom_ext (((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).map_id L.obj)
  map_comp h h' := hom_ext
    (((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.obj)).map_comp h.hom h'.hom)

/-- The component at `L` of the natural transformation `RHom(K, -) ⟶ RHom(K', -)` induced by a
morphism `f : K' ⟶ K` of Weil complexes. -/
noncomputable def internalHomMapApp {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomObj aX K).obj L ⟶ (internalHomObj aX K').obj L :=
  ⟨((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj,
    internalHomFrobenius_hom_comp_map_left aX f L⟩

/-- The components `internalHomMapApp` are natural in the second variable. -/
lemma internalHomMap_naturality {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    {L L' : WeilComplex (ModuleCat.{u + 1} Λ) g} (h : L ⟶ L') :
    (internalHomObj aX K).map h ≫ internalHomMapApp aX f L' =
      internalHomMapApp aX f L ≫ (internalHomObj aX K').map h :=
  hom_ext (((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).naturality h.hom)

/-- The natural transformation `RHom(K, -) ⟶ RHom(K', -)` of endofunctors of Weil complexes
induced by a morphism `f : K' ⟶ K` of Weil complexes. -/
noncomputable def internalHomMap {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K) :
    internalHomObj aX K ⟶ internalHomObj aX K' where
  app := internalHomMapApp aX f
  naturality _ _ := internalHomMap_naturality aX f

@[simp]
lemma internalHomMapApp_hom {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomMapApp aX f L).hom =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.hom.op).app L.obj :=
  rfl

@[simp]
lemma internalHomMap_app {K K' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (internalHomMap aX f).app L = internalHomMapApp aX f L :=
  rfl

lemma internalHomMap_id (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    internalHomMap aX (𝟙 K) = 𝟙 (internalHomObj aX K) := by
  ext L
  rw [internalHomMap_app, internalHomMapApp_hom, id_hom, op_id, CategoryTheory.Functor.map_id,
    NatTrans.id_app, NatTrans.id_app, id_hom]
  rfl

lemma internalHomMap_comp {K K' K'' : WeilComplex (ModuleCat.{u + 1} Λ) g} (f : K' ⟶ K)
    (f' : K'' ⟶ K') :
    internalHomMap aX (f' ≫ f) = internalHomMap aX f ≫ internalHomMap aX f' := by
  ext L
  rw [internalHomMap_app, internalHomMapApp_hom, NatTrans.comp_app, comp_hom, internalHomMap_app,
    internalHomMap_app, comp_hom, internalHomMapApp_hom, internalHomMapApp_hom, op_comp,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app]

variable (g) in
/-- Blueprint `lem-wf-internal-hom-weil`: the derived internal hom of Weil complexes. With the
internal-Hom Frobenius `RHom(φ_K⁻¹, φ_L)`
(`AlgebraicGeometry.Etale.WeilComplex.internalHomFrobenius`), the derived internal hom of
`Dctf(X, Λ)` lifts to a bifunctor `WeilDᵒᵖ × WeilD ⥤ WeilD` on Weil complexes, lying over the
derived internal hom of `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.WeilComplex.internalHom_obj_obj_obj`,
`…internalHom_map_app_hom`, `…internalHom_obj_map_hom`), which is triangulated in its second
variable. -/
noncomputable def internalHom :
    (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ ⥤ WeilComplex (ModuleCat.{u + 1} Λ) g ⥤
      WeilComplex (ModuleCat.{u + 1} Λ) g where
  obj K := internalHomObj aX K.unop
  map f := internalHomMap aX f.unop
  map_id K := internalHomMap_id aX K.unop
  map_comp f f' := internalHomMap_comp aX f.unop f'.unop

@[simp]
lemma internalHom_obj_obj_obj (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).obj K).obj L).obj =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).obj L.obj :=
  rfl

@[simp]
lemma internalHom_obj_obj_frobenius (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).obj K).obj L).frobenius = internalHomFrobenius aX K.unop L :=
  rfl

@[simp]
lemma internalHom_obj_map_hom (K : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ)
    {L L' : WeilComplex (ModuleCat.{u + 1} Λ) g} (h : L ⟶ L') :
    (((internalHom g aX).obj K).map h).hom =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).obj (op K.unop.obj)).map h.hom :=
  rfl

@[simp]
lemma internalHom_map_app_hom {K K' : (WeilComplex (ModuleCat.{u + 1} Λ) g)ᵒᵖ} (f : K ⟶ K')
    (L : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (((internalHom g aX).map f).app L).hom =
      ((DerivedCategoryFiniteTor.derivedHom Λ aX).map f.unop.hom.op).app L.obj :=
  rfl

end WeilComplex

end Etale

end AlgebraicGeometry
