/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived coefficient change of supported Kummer classes

Source: Stacks Project, Tag 07A6; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md, final paragraph
(blueprint: def-asd-ordinary-supported-kummer-scalar).

## Main definitions

* `SupportedDerivedScalarUnit`: the derived scalar-unit universal property.
* `SupportedKummerScalar`: the normalized scalar-extension square for the classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace CategoryTheory

/-- A coefficient-unit universal property expressed with abstract functors.
This is the degree-zero embedding formulation used below; abstracting the functors avoids
repeatedly expanding the derived localization while using its categorical API.
Source: Stacks 07A6 (blueprint: def-asd-ordinary-supported-kummer-scalar). -/
@[irreducible] def IsScalarExtensionUnit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {U : D ⥤ C} {V : D' ⥤ C'} (L : C ⥤ C') (M : D ⥤ D')
    (e : M ⋙ V ≅ U ⋙ L) {F : C} {G : D} (η : F ⟶ U.obj G) : Prop :=
  ∀ K : D', Function.Bijective
    (fun f : M.obj G ⟶ K ↦ (L.map η ≫ e.inv.app G) ≫ V.map f)

/-- Transport a scalar unit through isomorphisms of its ordinary source and target.
Source: naturality of the degree-zero restriction comparison, Stacks 07A6.
Proof: precompose test morphisms by the target isomorphism and postcompose their
images by the source isomorphism. Both operations are bijective. Naturality of the
comparison and the given ordinary unit equation identify the resulting function.
(blueprint: lem-asd-scalar-unit-transport-api) -/
theorem isScalarExtensionUnit_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {U : D ⥤ C} {V : D' ⥤ C'} (L : C ⥤ C') (M : D ⥤ D')
    (e : M ⋙ V ≅ U ⋙ L) {F F' : C} {G G' : D}
    (a : F' ≅ F) (b : G' ≅ G) (η' : F' ⟶ U.obj G') (η : F ⟶ U.obj G)
    (hη : a.inv ≫ η' ≫ U.map b.hom = η)
    (h : IsScalarExtensionUnit L M e η') : IsScalarExtensionUnit L M e η := by
  rw [IsScalarExtensionUnit] at h ⊢
  simp only [Category.assoc] at h ⊢
  intro K
  let p : (M.obj G ⟶ K) ≃ (M.obj G' ⟶ K) :=
    { toFun := fun f ↦ M.map b.hom ≫ f
      invFun := fun f ↦ M.map b.inv ≫ f
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  let q : (L.obj F' ⟶ V.obj K) ≃ (L.obj F ⟶ V.obj K) :=
    { toFun := fun f ↦ L.map a.inv ≫ f
      invFun := fun f ↦ L.map a.hom ≫ f
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  have hb := q.bijective.comp ((h K).comp p.bijective)
  convert hb using 1
  funext f
  change L.map η ≫ e.inv.app G ≫ V.map f =
    L.map a.inv ≫ L.map η' ≫ e.inv.app G' ≫ V.map (M.map b.hom ≫ f)
  have hn := e.inv.naturality b.hom
  dsimp only [Functor.comp_map] at hn
  rw [← hη]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

end CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The universal-property formulation of a derived scalar-extension unit at F.
The target is G in degree zero, while test objects K range over the entire unbounded
derived category. This is derived tensor extension, with no flatness assumption on S.
Source: Stacks 07A6 (blueprint: def-asd-ordinary-supported-kummer-scalar). -/
@[irreducible]
def SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  IsScalarExtensionUnit
    (DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) 0)
    (DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S)) 0)
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0) η


/-- The scalar-extension clause, with the comparison maps fixed on generators.
Both displayed universal properties refer to the canonical sectionwise scalar maps:
constants send r to φ(r), roots send a ⊗ z to φ(a) ⊗ z. The Ext square is the assertion
that the class itself is obtained by the same derived scalar extension.
Source: Stacks 07A6 and blueprint lem-amb-cartier-kummer-map, final paragraph
(blueprint: def-asd-ordinary-supported-kummer-scalar). -/
@[irreducible]
def SupportedKummerScalar {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T)
    (cR : Ext ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      (Scheme.finiteEtaleTateLine T N R hR) 2)
    (cS : Ext ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      (Scheme.finiteEtaleTateLine T N S hS) 2) : Prop :=
  ∃ (η : ordinaryFiniteConstant R D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (θ : Scheme.finiteEtaleTateLine T N R hR ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N S hS)),
    (∀ (U : D.Etaleᵒᵖ) (r : R),
      η.hom.app U
        ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r)) ∧
    (∀ (U : T.Etaleᵒᵖ) (r : R) (z : (T.rootsOfUnitySheaf N).obj.obj U),
      θ.hom.app U (Scheme.finiteEtaleTateOneGenerator R N T hR U r z) =
        Scheme.finiteEtaleTateOneGenerator S N T hS U (φ r) z) ∧
    SupportedDerivedScalarUnit φ T
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    SupportedDerivedScalarUnit φ T (Scheme.finiteEtaleTateLine T N R hR)
      (Scheme.finiteEtaleTateLine T N S hS) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars T.smallEtaleTopology φ)) (zero_add 2) =
      cR.comp (Ext.mk₀ θ) (add_zero 2)


end AlgebraicGeometry.Etale
