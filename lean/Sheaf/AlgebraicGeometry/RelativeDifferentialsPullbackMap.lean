/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.TensorPullback

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
  sorry

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
