/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentPullbackCohomologyMaps
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.CategoryTheory.ExtUniverseChange
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientFactor
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtCoefficientFactor

/-! # The large abelian resolution comparison and scheme pullback

Source: Stacks Project, Tags 03FD and 01F7.
-/

@[expose] public section
universe u v w u₀ v₀ u₁ v₁
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local irreducible] tensorPullback tensorPullbackObj
  SheafOfModules.toSheaf moduleAbelianCohomologyLarge moduleCohomologyFMap
  invImage coeff constIso constantSheaf constantSheafAdj
  ExtEdgeResolution.moduleComparisonEquiv
  RingedSpace.moduleCohomology Abelian.Ext Abelian.Ext.instAddCommGroup
  moduleCohomologyEdgeMap
attribute [local instance 4000] cohomologyHasSheafify cohomologyHasExt
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

private theorem factor_square {A B M C D N : Type*}
    (cA : A → C) (cB : B → D) (cM : M → N)
    (f : A → B) (m : A → M) (e : M → B)
    (a : N → D) (b : C → N) (p : C → D)
    (hf : ∀ x, f x = e (m x)) (he : ∀ x, cB (e x) = a (cM x))
    (hc : ∀ x, cM (m x) = b (cA x)) (hp : ∀ x, a (b x) = p x) (x : A) :
    cB (f x) = p (cA x) := by
  rw [hf, he, hc, hp]

attribute [local irreducible] coherentExtUniverseEquiv

private theorem coherent_universe_apply
    {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [es : HasExt.{v} A] [et : HasExt.{w} A] {M N : A} {q : ℕ}
    (x : Abelian.Ext.{v} M N q) :
    @coherentExtUniverseEquiv A _ _ es et M N q x =
      @Abelian.Ext.universeChangeEquiv A _ _ es et M N q x := by
  unfold coherentExtUniverseEquiv
  unfold Abelian.Ext.universeChangeEquiv
  rfl

-- Plain functions cache the conversion from the additive comparison.
@[irreducible]
private def resolutionFunction (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    (RingedSpace.moduleCohomology X.toRingedSpace q).obj F → H F q :=
  fun x ↦ moduleCohomologyExtResolutionEquiv X F q x

private theorem coherent_universe_exactComposite
    {A : Type u₀} [Category.{v₀} A] [Abelian A]
    {B : Type u₁} [Category.{v₁} B] [Abelian B]
    [esA : HasExt.{v} A] [etA : HasExt.{w} A]
    [esB : HasExt.{v} B] [etB : HasExt.{w} B]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {Z F : A} {W G : B} (a : W ⟶ L.obj Z) (b : L.obj F ⟶ G)
    (q : ℕ) (x : Abelian.Ext.{v} Z F q) :
    @coherentExtUniverseEquiv B _ _ esB etB W G q
        (((Abelian.Ext.mk₀.{v} a).comp
          (Abelian.Ext.mapExactFunctor.{v, v} L x) (zero_add q)).comp
            (Abelian.Ext.mk₀.{v} b) (add_zero q)) =
      ((Abelian.Ext.mk₀.{w} a).comp
        (Abelian.Ext.mapExactFunctor.{w, w} L
          (@coherentExtUniverseEquiv A _ _ esA etA Z F q x)) (zero_add q)).comp
        (Abelian.Ext.mk₀.{w} b) (add_zero q) := by
  simpa only [coherent_universe_apply] using
    (Abelian.Ext.universeChangeEquiv_exactComposite
      (esA := esA) (etA := etA) (esB := esB) (etB := etB) L a b q x)

@[irreducible]
private def universeFunction (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    H F q → CoherentEtale.Source X F q :=
  fun x ↦ @coherentExtUniverseEquiv
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) _ _
    (comparisonHasExt X) (HasExt.standard _)
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q x

private theorem large_resolution_apply (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleAbelianCohomologyLarge X F q x =
      universeFunction X F q (resolutionFunction X F q x) := by
  with_unfolding_all rfl

/-- The fixed large abelian comparison intertwines module and abelian pullback.
Source: Stacks Project, Tags 03FD and 01F7.
(blueprint: lem-weil-pbc-module-abelian-large-pullback)

Proof: First factor the module cohomology f-map into its coefficient map and
the direct-image edge. Naturality and edge compatibility of the fixed common
resolution comparison identify it with exact abelian inverse image followed
by the adjoint coefficient map. Exact inverse image and both Yoneda products
commute with the canonical change-of-universe equivalence, giving the fixed
large comparison square. The argument does not assume flatness or
quasi-coherence and includes degree zero and empty schemes. -/
theorem moduleAbelianCohomologyLarge_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf)
    (G : SheafOfModules.{u} Y.ringCatSheaf) (φ : F ⟶ (pushforward g).obj G)
    (q : ℕ) (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleAbelianCohomologyLarge Y G q
        (moduleCohomologyFMap g
          φ q x) =
      zariskiPullbackCohomology g F G φ q (moduleAbelianCohomologyLarge X F q x) := by
  have h :=
    (factor_square
      (A := (RingedSpace.moduleCohomology X.toRingedSpace q).obj F)
      (B := (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
      (M := (RingedSpace.moduleCohomology X.toRingedSpace q).obj ((pushforward g).obj G))
      (C := H F q) (D := H G q)
      (N := H ((pushforward g).obj G) q)
      (resolutionFunction X F q)
      (resolutionFunction Y G q)
      (resolutionFunction X ((pushforward g).obj G) q)
      (moduleCohomologyFMap g φ q)
      (fun x ↦ ((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x)
      (moduleCohomologyEdgeMap g G q)
      (fun x ↦ Sheaf.H.map.{u}
        (coeff (M := (pushforward g).obj G) (N := G) g (𝟙 ((pushforward g).obj G))) q
        (Sheaf.H.mapFunctor.{u} (invImage g) (constIso g).symm
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((pushforward g).obj G)) q x))
      (H.map (X := X) φ q)
      (fun x ↦ Sheaf.H.map.{u} (coeff (M := F) (N := G) g φ) q
        (Sheaf.H.mapFunctor.{u} (invImage g) (constIso g).symm
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q x))
      (moduleCohomology_coefficient_factor (X := Y) (Y := X) (N := F) (F := G) g φ q)
      (fun z ↦ by
        unfold resolutionFunction
        exact moduleCohomologyExtResolutionEquiv_edge (X := Y) (Y := X) g G q z)
      (fun z ↦ by
        unfold resolutionFunction
        exact moduleCohomologyExtResolutionEquiv_naturality X q F
          ((pushforward g).obj G) φ z)
      (moduleCohomology_ext_coefficient_factor (X := Y) (Y := X) (N := F) (F := G)
        g φ q) x)
  refine (large_resolution_apply Y G q _).trans
    ((congrArg (universeFunction Y G q) h).trans ?_)
  refine Eq.trans ?_ (congrArg (zariskiPullbackCohomology g F G φ q)
    (large_resolution_apply X F q x).symm)
  unfold universeFunction zariskiPullbackCohomology Sheaf.cohomologyPullbackMap
    Abelian.Ext.mapExactFunctorWithCoefficients
  have hu := coherent_universe_exactComposite
    (esA := comparisonHasExt X) (esB := comparisonHasExt Y)
    (etA := (HasExt.standard _ : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})))
    (etB := (HasExt.standard _ : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})))
    (invImage g) (constIso g).inv (coeff g φ) q
    (resolutionFunction X F q x)
  set_option backward.isDefEq.respectTransparency false in
    simpa only [Sheaf.H.map_apply, Sheaf.H.mapFunctor_apply, Iso.symm_hom,
      AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv] using hu

end
end AlgebraicGeometry.Scheme.Modules
