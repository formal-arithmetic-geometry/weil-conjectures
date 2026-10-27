/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.RelativeFlatOfStalks
import Sheaf.RingTheory.FlatnessFaithfullyFlatExtension
import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent

/-!
# Relative flatness detected on a flat source cover

Source: Stacks Project, Morphisms, Tag 02JZ, `lemma-flat-permanence`, with the
pointwise definition in Tag 01U3 and its affine-section characterization in Tag 01U4
(blueprint: lem-trf-relative-flatness-source-cover).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Relative flatness of a quasi-coherent module is detected pointwise by a morphism
flat at the chosen point, and globally by any jointly surjective family of flat morphisms.
The pointwise scalar actions are restriction along the respective scheme stalk maps;
the global condition is the recorded affine-section predicate `IsFlatOver`.

Source: Stacks Project, Morphisms, Tag 02JZ, `lemma-flat-permanence`; Tags 01U3 and 01U4
(blueprint: lem-trf-relative-flatness-source-cover).

Proof:
1. For a point `x`, put `y = h x`, `s = f y`, `A = O_{S,s}`, `B = O_{Y,y}`,
   `C = O_{X,x}`, and `N = G_y`. The local stalk map `B → C` is flat by hypothesis,
   hence faithfully flat by lem-pc-local-flat-faithful-flat-reflects-surjective.
   The isomorphism lem-weil-pbc-module-stalk-pullback identifies the pulled-back stalk
   with `C ⊗[B] N`. Functoriality of the scheme stalk maps identifies its `A`-action
   with that through `h ≫ f`.
2. Apply lem-trf-flatness-faithfully-flat-extension to `A → B → C` and `N`.
   Flatness of `N` over `A` is equivalent to flatness of `C ⊗[B] N` over `A`.
   The stalk isomorphism of Step 1 gives the first conjunct.
3. For the family, def-weil-pbc-tensor-pullback-ordinary-comparison transports
   lem-weil-pbc-module-pullback-quasi-coherent to every tensor pulled-back module.
   If `G.IsFlatOver f`, lem-pc-relative-flat-module-stalk
   gives flatness at every point of `Y`; Step 2 gives flatness at every point of each
   `X i`, and lem-pc-relative-flat-of-stalks gives the required global flatness there.
   Conversely, apply lem-pc-relative-flat-module-stalk to each pulled-back module.
   For each `y`, joint surjectivity supplies `i` and `x` with `h i x = y`.
   Step 2 then gives flatness of `G` at `y`, and lem-pc-relative-flat-of-stalks gives
   `G.IsFlatOver f`. This also applies to empty schemes and empty covering families. -/
theorem relative_flatness_source_cover {Y S : Scheme.{u}} (f : Y ⟶ S)
    (G : Y.Modules) [G.IsQuasicoherent] :
    (∀ (X : Scheme.{u}) (h : X ⟶ Y) (x : X), (h.stalkMap x).hom.Flat →
      (Module.Flat (S.presheaf.stalk (f (h x)))
        ((ModuleCat.restrictScalars (f.stalkMap (h x)).hom).obj
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (h x)).obj G)) ↔
       Module.Flat (S.presheaf.stalk ((h ≫ f) x))
        ((ModuleCat.restrictScalars ((h ≫ f).stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            ((Scheme.Modules.tensorPullback h).obj G))))) ∧
    (∀ (I : Type v) (X : I → Scheme.{u}) (h : ∀ i : I, X i ⟶ Y),
      (∀ i : I, Flat (h i)) →
      (∀ y : Y, ∃ (i : I) (x : X i), h i x = y) →
      (G.IsFlatOver f ↔
        ∀ i : I, ((Scheme.Modules.tensorPullback (h i)).obj G).IsFlatOver (h i ≫ f))) := by
  classical
  have pointwise (X : Scheme.{u}) (h : X ⟶ Y) (x : X)
      (hx : (h.stalkMap x).hom.Flat) :
      Module.Flat (S.presheaf.stalk (f (h x)))
        ((ModuleCat.restrictScalars (f.stalkMap (h x)).hom).obj
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (h x)).obj G)) ↔
      Module.Flat (S.presheaf.stalk ((h ≫ f) x))
        ((ModuleCat.restrictScalars ((h ≫ f).stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            ((Scheme.Modules.tensorPullback h).obj G))) := by
    let A := S.presheaf.stalk (f (h x))
    let B := Y.presheaf.stalk (h x)
    let C := X.presheaf.stalk x
    let N := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (h x)).obj G
    let P := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      ((Scheme.Modules.tensorPullback h).obj G)
    let : Algebra A B := (f.stalkMap (h x)).hom.toAlgebra
    let : Algebra B C := (h.stalkMap x).hom.toAlgebra
    let : Algebra A C := ((h.stalkMap x).hom.comp (f.stalkMap (h x)).hom).toAlgebra
    have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
    let : Module A N := Module.compHom N (algebraMap A B)
    have : IsScalarTower A B N := IsScalarTower.of_compHom A B N
    have : Module.Flat B C := hx
    have : IsLocalHom (algebraMap B C) :=
      (inferInstance : IsLocalHom (h.stalkMap x).hom)
    have : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
    let : Module A P := Module.compHom P (algebraMap A C)
    have : IsScalarTower A C P := IsScalarTower.of_compHom A C P
    obtain ⟨e, _⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso h x
    let E₀ : P ≃ₗ[C] (TensorProduct B C N) := (e.app G).toLinearEquiv
    let E : P ≃ₗ[A] (TensorProduct B C N) := E₀.restrictScalars A
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    change Module.Flat A N ↔ Module.Flat A P
    exact Module.Flat.iff_flat_tensorProduct_of_faithfullyFlat_extension.trans
      (Module.Flat.equiv_iff E).symm
  refine ⟨pointwise, ?_⟩
  intro I X h hh hsurj
  constructor
  · intro hG i
    apply relative_flat_of_stalks
    intro x
    apply (pointwise (X i) (h i) x ((Flat.iff_flat_stalkMap (h i)).mp (hh i) x)).mp
    let : Algebra (S.presheaf.stalk (f (h i x))) (Y.presheaf.stalk (h i x)) :=
      (f.stalkMap (h i x)).hom.toAlgebra
    exact relative_flat_module_stalk f G hG (h i x) rfl
  · intro hG
    apply relative_flat_of_stalks
    intro y
    obtain ⟨i, x, rfl⟩ := hsurj y
    apply (pointwise (X i) (h i) x ((Flat.iff_flat_stalkMap (h i)).mp (hh i) x)).mpr
    let : Algebra (S.presheaf.stalk ((h i ≫ f) x)) ((X i).presheaf.stalk x) :=
      ((h i ≫ f).stalkMap x).hom.toAlgebra
    exact relative_flat_module_stalk (h i ≫ f) _ (hG i) x rfl

end AlgebraicGeometry
