/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# The canonical pullback map on relative differentials

Source: Stacks Project, Morphisms, Section 29.32, Tag 01UV,
`lemma-functoriality-differentials`; Curves, Tag 0C1C
(blueprint: def-a1-relative-differentials-pullback-map).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Hom

/-- The section `1 ⊗ da` of the tensor pullback, formed using the abelian inverse-image
unit and the module-sheafification unit, rather than an unspecified adjunction.
Source: Stacks Project, Morphisms, Section 29.32, Tag 01UV,
`lemma-functoriality-differentials` (blueprint: def-a1-relative-differentials-pullback-map). -/
noncomputable def relativeDifferentialsPullbackGenerator {X Y S : Scheme.{u}}
    (g : Y ⟶ S) (h : X ⟶ Y) (W : Y.Opens) (a : Γ(Y, W)) :
    ((Modules.tensorPullback h).obj g.relativeDifferentials).val.obj (op (h ⁻¹ᵁ W)) :=
  (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (Modules.tensorPullbackRingMap h)
      (TopCat.Sheaf.inverseImageModule h.base Y.sheaf g.relativeDifferentials)).presheaf).app
    (op (h ⁻¹ᵁ W))
    ((1 : X.sheaf.obj.obj (op (h ⁻¹ᵁ W))) ⊗ₜ[
      (TopCat.Sheaf.inverseImageRing h.base Y.sheaf).obj.obj (op (h ⁻¹ᵁ W)),
      ((Modules.tensorPullbackRingMap h).hom.app (op (h ⁻¹ᵁ W))).hom]
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map h.base) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app
            ((SheafOfModules.toSheaf _).obj g.relativeDifferentials)).hom.app (op W)
              (g.relativeDifferentialsDerivation.d (X := op W) a)))

/-- There is a unique morphism `h* Ω_{Y/S} ⟶ Ω_{X/S}` sending `1 ⊗ da` to `d(h♯a)`.
Source: Stacks Project, Morphisms, Section 29.32, Tag 01UV,
`lemma-functoriality-differentials` (blueprint: def-a1-relative-differentials-pullback-map).

Proof: the universal derivation on X composed with h-sharp is an S-derivation on Y
with values in h_* Ω_{X/S}. The universal property of Ω_{Y/S} gives its unique module
map. The inverse-image and tensor adjunctions give a map from the explicit tensor
pullback; the section formula is the tensor-unit formula for those adjunctions.
For uniqueness, the differentials da generate Ω_{Y/S} locally, their inverse images
locally generate the inverse-image module, and pure tensors generate the change of
rings. The displayed formula therefore determines every stalk map and hence the map. -/
theorem existsUnique_relativeDifferentialsPullbackMap {X Y S : Scheme.{u}}
    (g : Y ⟶ S) (h : X ⟶ Y) :
    ∃! d : (Modules.tensorPullback h).obj g.relativeDifferentials ⟶
        (h ≫ g).relativeDifferentials,
      ∀ (W : Y.Opens) (a : Γ(Y, W)),
        d.val.app (op (h ⁻¹ᵁ W)) (relativeDifferentialsPullbackGenerator g h W a) =
          (h ≫ g).relativeDifferentialsDerivation.d (X := op (h ⁻¹ᵁ W)) (h.app W a) := by
  let D : ((Modules.pushforward h).obj (h ≫ g).relativeDifferentials).val.Derivation'
      g.pullbackPresheafToPresheaf :=
    g.derivationMk
      (fun {U} ↦ (h ≫ g).relativeDifferentialsDerivation.d.comp
        (h.app U.unop).hom.toAddMonoidHom)
      (by
        intro U a b
        change (h ≫ g).relativeDifferentialsDerivation.d (h.app U.unop (a * b)) = _
        rw [map_mul, PresheafOfModules.Derivation.d_mul]
        rfl)
      (by
        intro U V i a
        change (h ≫ g).relativeDifferentialsDerivation.d
          (h.app V.unop (Y.presheaf.map i a)) = _
        rw [← CommRingCat.comp_apply, h.naturality i]
        exact (h ≫ g).relativeDifferentialsDerivation.d_map _ _)
      (by
        intro V a
        change (h ≫ g).relativeDifferentialsDerivation.d
          (h.app (g ⁻¹ᵁ V) (g.app V a)) = 0
        exact (h ≫ g).relativeDifferentialsDerivation.d_app_app V a)
  obtain ⟨adj, hadj⟩ := Modules.exists_tensorPullbackAdjunction h
  let e := adj.homEquiv g.relativeDifferentials (h ≫ g).relativeDifferentials
  let q := (g.relativeDifferentialsHomEquiv _).symm D
  have he (d : (Modules.tensorPullback h).obj g.relativeDifferentials ⟶
      (h ≫ g).relativeDifferentials) (W : Y.Opens) (a : Γ(Y, W)) :
      (e d).val.app (op W) (g.relativeDifferentialsDerivation.d a) =
        d.val.app (op (h ⁻¹ᵁ W)) (relativeDifferentialsPullbackGenerator g h W a) := by
    rw [Adjunction.homEquiv_unit]
    change d.val.app (op (h ⁻¹ᵁ W))
      ((adj.unit.app g.relativeDifferentials).val.app (op W)
        (g.relativeDifferentialsDerivation.d a)) = _
    rw [hadj]
    rfl
  refine ⟨e.symm q, ?_, ?_⟩
  · intro W a
    rw [← he, Equiv.apply_symm_apply]
    exact g.relativeDifferentialsHomEquiv_symm_app_d D a
  · intro d hd
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply (g.relativeDifferentialsHomEquiv _).injective
    ext U a
    exact (he d U.unop a).trans (hd U.unop a) |>.trans
      (g.relativeDifferentialsHomEquiv_symm_app_d D a).symm

/-- The canonical differential map, uniquely determined by `1 ⊗ da ↦ d(h♯a)`.
Source: Stacks Project, Morphisms, Section 29.32, Tag 01UV,
`lemma-functoriality-differentials` (blueprint: def-a1-relative-differentials-pullback-map).
The choice is from a unique existence statement; it postpones only the proof of the
universal property and does not choose an arbitrary morphism. -/
noncomputable def relativeDifferentialsPullbackMap {X Y S : Scheme.{u}}
    (g : Y ⟶ S) (h : X ⟶ Y) :
    (Modules.tensorPullback h).obj g.relativeDifferentials ⟶ (h ≫ g).relativeDifferentials :=
  Classical.choose (existsUnique_relativeDifferentialsPullbackMap g h)

end AlgebraicGeometry.Scheme.Hom
