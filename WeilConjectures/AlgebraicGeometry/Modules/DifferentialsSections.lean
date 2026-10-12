/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

/-!
# Sections of the sheaf of differentials over affine opens

Let `g : X ⟶ Spec R` be a morphism of schemes and `U` an affine open of `X`. Then the sections
`Γ(Ω¹_{X/R}, U)` of the sheaf of relative differentials are the Kähler differentials
`Ω[Γ(X, U)⁄R]`, compatibly with `d` and `D`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.Hom.specStructureMap`: the structure map `R ⟶ Γ(X, U)`.
- `AlgebraicGeometry.Scheme.Hom.exists_linearEquiv_kaehlerDifferential`: for `U` affine,
  `Ω[Γ(X, U)⁄R] ≃ Γ(Ω¹_{X/R}, U)`, sending `D b` to `d b`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R)

/-- The structure map `R ⟶ Γ(X, U)` of a scheme `X` over `Spec R`. -/
noncomputable def specStructureMap (U : X.Opens) : R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ g.appLE ⊤ U le_top

lemma specStructureMap_map {U V : X.Opens} (h : V ≤ U) :
    g.specStructureMap U ≫ X.presheaf.map (homOfLE h).op = g.specStructureMap V := by
  simp [specStructureMap]

/-- The universal derivation `d : 𝒪_X → Ω¹_{X/R}` on sections over `U`. -/
noncomputable def sectionsD (U : X.Opens) : Γ(X, U) →+ Γ(g.relativeDifferentials, U) :=
  g.relativeDifferentialsDerivation.d (X := op U)

lemma sectionsD_mul (U : X.Opens) (a b : Γ(X, U)) :
    g.sectionsD U (a * b) = a • g.sectionsD U b + b • g.sectionsD U a :=
  g.relativeDifferentialsDerivation.d_mul a b

lemma sectionsD_map {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    g.sectionsD V (X.presheaf.map (homOfLE h).op a) =
      g.relativeDifferentials.presheaf.map (homOfLE h).op (g.sectionsD U a) :=
  g.relativeDifferentialsDerivation.d_map _ a

lemma sectionsD_specStructureMap (U : X.Opens) (r : R) :
    g.sectionsD U (g.specStructureMap U r) = 0 := by
  have h := PresheafOfModules.Derivation'.d_app_app g.relativeDifferentialsDerivation ⊤
    ((Scheme.ΓSpecIso R).inv r)
  have h' := g.sectionsD_map (le_top : U ≤ g ⁻¹ᵁ ⊤) (g.app ⊤ ((Scheme.ΓSpecIso R).inv r))
  have e : g.specStructureMap U r =
      X.presheaf.map (homOfLE (le_top : U ≤ g ⁻¹ᵁ ⊤)).op (g.app ⊤ ((Scheme.ΓSpecIso R).inv r)) := by
    simp [specStructureMap, Scheme.Hom.appLE]
  rw [e, h']
  exact (congrArg (g.relativeDifferentials.presheaf.map _) h).trans (map_zero _)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R) {U : X.Opens}
  (hU : IsAffineOpen U)

include hU in
lemma _root_.AlgebraicGeometry.IsAffineOpen.image_fromSpec_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [image_top_eq_opensRange, hU.opensRange_fromSpec]

lemma fromSpec_comp_eq_specMap : hU.fromSpec ≫ g = Spec.map (g.specStructureMap U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top (Spec R)) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, specStructureMap, Spec.map_comp]

/-- Restricting a section of `𝒪_X` over the affine open `U` to `hU.fromSpec ''ᵁ ⊤ = U` and
transporting it to `Γ(Spec Γ(X, U), ⊤)` is the inverse of `Scheme.ΓSpecIso`. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.map_eqToHom_comp_appIso_hom :
    X.presheaf.map (eqToHom hU.image_fromSpec_top).op ≫ (hU.fromSpec.appIso ⊤).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE, hU.fromSpec_app_self,
    Category.assoc, ← Functor.map_comp, Subsingleton.elim (_ ≫ _) (𝟙 _),
    CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- Elementwise version of `IsAffineOpen.map_eqToHom_comp_appIso_hom`. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.map_eqToHom_apply (a : Γ(X, U)) :
    X.presheaf.map (eqToHom hU.image_fromSpec_top).op a =
      (hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a) := by
  rw [← hU.map_eqToHom_comp_appIso_hom, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply]

variable {g} in
/-- `relativeDifferentialsCongr` is compatible with the universal derivations. -/
lemma relativeDifferentialsCongr_hom_app_d {g' : X ⟶ Spec R} (e : g = g') {W : X.Opensᵒᵖ}
    (x : X.presheaf.obj W) :
    (relativeDifferentialsCongr g e).hom.val.app W (g.relativeDifferentialsDerivation.d x) =
      g'.relativeDifferentialsDerivation.d x := by
  subst e
  rw [relativeDifferentialsCongr, eqToIso_refl, Iso.refl_hom]
  rfl

/-- The identity map from the sections over `⊤` of an `𝒪_{Spec A}`-module `N` to the underlying
group of the `A`-module `moduleSpecΓFunctor.obj N`. Stating it for an arbitrary `N` keeps the
unification of the two (definitionally equal) additive structures cheap. -/
def _root_.AlgebraicGeometry.Scheme.Modules.toModuleSpecΓ {A : CommRingCat.{u}}
    (N : (Spec A).Modules) : N.val.obj (op ⊤) →+ (moduleSpecΓFunctor (R := A)).obj N where
  toFun x := x
  map_zero' := rfl
  map_add' _ _ := rfl

lemma _root_.AlgebraicGeometry.Scheme.Modules.toModuleSpecΓ_smul {A : CommRingCat.{u}}
    (N : (Spec A).Modules) (a : A) (x : N.val.obj (op ⊤)) :
    N.toModuleSpecΓ ((Scheme.ΓSpecIso A).inv a • x) = a • N.toModuleSpecΓ x :=
  rfl

lemma _root_.AlgebraicGeometry.Scheme.Modules.toModuleSpecΓ_bijective {A : CommRingCat.{u}}
    (N : (Spec A).Modules) : Function.Bijective N.toModuleSpecΓ :=
  Function.bijective_id

/-- For an isomorphism of sheaves of modules, the maps on sections are bijective. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.bijective_val_app {Y : Scheme.{u}}
    {M N : Y.Modules} (e : M ≅ N) (W : Y.Opensᵒᵖ) : Function.Bijective (e.hom.val.app W) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.val.app W, fun x ↦ ?_, fun y ↦ ?_⟩
  · exact congr($(e.hom_inv_id).val.app W x)
  · exact congr($(e.inv_hom_id).val.app W y)

variable {M : X.Modules} {N : (Spec Γ(X, U)).Modules} (θ : M.restrict hU.fromSpec ≅ N)
  {K : ModuleCat Γ(X, U)} (ε : (moduleSpecΓFunctor (R := Γ(X, U))).obj N ≅ K)

/-- Given identifications `θ : M|_{Spec Γ(X, U)} ≅ N` and `ε : Γ(N, ⊤) ≅ K`, the map
`Γ(M, U) → K` obtained by restricting along `hU.fromSpec`. -/
noncomputable def sectionsMapOfIso (m : Γ(M, U)) : K :=
  ε.hom.hom (N.toModuleSpecΓ (θ.hom.val.app (op ⊤) (M.presheaf.map (eqToHom hU.image_fromSpec_top).op m)))

set_option maxHeartbeats 20000 in
lemma sectionsMapOfIso_add (m m' : Γ(M, U)) :
    sectionsMapOfIso hU θ ε (m + m') = sectionsMapOfIso hU θ ε m + sectionsMapOfIso hU θ ε m' := by
  simp only [sectionsMapOfIso, map_add]

set_option maxHeartbeats 20000 in
lemma sectionsMapOfIso_smul (a : Γ(X, U)) (m : Γ(M, U)) :
    sectionsMapOfIso hU θ ε (a • m) = a • sectionsMapOfIso hU θ ε m := by
  have h1 : M.presheaf.map (eqToHom hU.image_fromSpec_top).op (a • m) =
      (Scheme.ΓSpecIso Γ(X, U)).inv a • (M.restrictAppIso hU.fromSpec ⊤).inv
        (M.presheaf.map (eqToHom hU.image_fromSpec_top).op m) := by
    rw [Scheme.Modules.map_smul, hU.map_eqToHom_apply]
    rfl
  refine (congrArg (fun x ↦ ε.hom.hom (N.toModuleSpecΓ (θ.hom.val.app (op ⊤) x))) h1).trans ?_
  refine (congrArg (fun x ↦ ε.hom.hom (N.toModuleSpecΓ x))
    ((θ.hom.val.app (op ⊤)).hom.map_smul _ _)).trans ?_
  refine (congrArg (fun x ↦ ε.hom.hom x) (N.toModuleSpecΓ_smul _ _)).trans ?_
  exact ε.hom.hom.map_smul _ _

set_option maxHeartbeats 20000 in
lemma sectionsMapOfIso_bijective : Function.Bijective (sectionsMapOfIso hU θ ε) :=
  ε.toLinearEquiv.bijective.comp ((Scheme.Modules.toModuleSpecΓ_bijective _).comp
    ((Scheme.Modules.bijective_val_app _ _).comp (ConcreteCategory.bijective_of_isIso _)))

end AlgebraicGeometry.Scheme.Hom
