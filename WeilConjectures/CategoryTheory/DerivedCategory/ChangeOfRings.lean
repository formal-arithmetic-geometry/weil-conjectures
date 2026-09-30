/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Extension and restriction of scalars along an algebra

Let `S` be an `R`-algebra, for commutative rings `R` and `S`. This file defines the
extension of scalars `S ⊗[R] -` and the restriction of scalars along `algebraMap R S`, and
the adjunction between them, at three stages:

| stage | extension | restriction |
| --- | --- | --- |
| modules | `ModuleCat.algebraExtendScalars R S` | `ModuleCat.algebraRestrictScalars R S` |
| sheaves | `Sheaf.algebraExtendScalars J R S` | `Sheaf.algebraRestrictScalars J R S` |
| derived | `DerivedCategory.algebraExtendScalars` | `DerivedCategory.algebraRestrictScalars` |

Each stage is built from the previous one:

* on modules, the extension of scalars of an `R`-module `M` is `S ⊗[R] M`, with the
  `S`-module structure coming from the *algebra* `S`, and a morphism `f` is sent to
  `f.baseChange S`; the restriction of scalars of an `S`-module `N` is `N` with
  `r • n = algebraMap R S r • n`. The adjunction `ModuleCat.algebraExtendRestrictScalarsAdj`
  is `LinearMap.liftBaseChangeEquiv`.
* on sheaves on a site `(C, J)`, the restriction of scalars is applied sectionwise
  (`sheafCompose`), and the extension of scalars is applied sectionwise and then sheafified
  (`Sheaf.composeAndSheafify`); the adjunction is `Sheaf.adjunction`.
* on derived categories, the restriction of scalars is exact, so it is applied levelwise
  (`Functor.mapDerivedCategory`), while the extension of scalars is left derived via K-flat
  resolutions (`Functor.leftDerivedFunctor`). The adjunction
  `DerivedCategory.algebraExtendRestrictScalarsAdj` is `Adjunction.derivedAdjunction`,
  transported along the identification of the right derived functor of the exact
  restriction functor with the levelwise one.

As in `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`, the site `C` has objects
in `Type (u + 1)`, `Hom`-types in `Type u` and is essentially small in `u + 1`, and the
coefficient rings live in `Type (u + 1)`, so that `Sheaf J (ModuleCat.{u + 1} R)` is
Grothendieck abelian, monoidal, and has a derived category, all by instance search.

## Why not `ModuleCat.extendScalars`

Mathlib's `ModuleCat.extendScalars f` takes a ring homomorphism `f : R →+* S`, and its
value on `M` is the tensor product `S ⊗[R] M` in which `S` is an `R`-module through
`Module.compHom S f`. When `S` is an `R`-algebra and `f = algebraMap R S`, this `R`-module
structure on `S` is *not* the one given by the algebra, `Algebra.toModule`: the two agree
only propositionally (`Algebra.smul_def`), so the tensor product and every instance on it
differ from those that `[Algebra R S]` provides, and nothing stated for `S ⊗[R] M` in the
algebra setting applies. The constructions below never use `ModuleCat.extendScalars`: they
are phrased with the algebra instances throughout, so that
`(ModuleCat.algebraExtendScalars R S).obj M` is `ModuleCat.of S (S ⊗[R] M)` for the
standard instances, and the restriction of scalars is definitionally Mathlib's
`ModuleCat.restrictScalars (algebraMap R S)`
(`ModuleCat.algebraRestrictScalars_eq_restrictScalars`), whose instances it inherits.

## Main definitions

- `ModuleCat.algebraExtendScalars`, `ModuleCat.algebraRestrictScalars` and the adjunction
  `ModuleCat.algebraExtendRestrictScalarsAdj`.
- `CategoryTheory.Sheaf.algebraExtendScalars`, `CategoryTheory.Sheaf.algebraRestrictScalars`
  and the adjunction `CategoryTheory.Sheaf.algebraExtendRestrictScalarsAdj`.
- `DerivedCategory.algebraExtendScalars`, `DerivedCategory.algebraRestrictScalars` and the
  adjunction `DerivedCategory.algebraExtendRestrictScalarsAdj`.
- `ModuleCat.algebraRestrictScalarsComp`, `ModuleCat.algebraExtendScalarsComp`,
  `CategoryTheory.Sheaf.algebraRestrictScalarsComp` and
  `CategoryTheory.Sheaf.algebraExtendScalarsComp` : for a scalar tower `R → S → T`, the
  change of scalars along `R → T` is the composite of those along `R → S` and `S → T`. The
  restriction isomorphisms are Mathlib's `ModuleCat.restrictScalarsComp'` with the
  composition of ring homomorphisms given by `IsScalarTower.algebraMap_eq`, and the extension
  isomorphisms are their conjugates along the adjunctions.

## Sorry

The single `sorry` is `CategoryTheory.Sheaf.preservesKFlatQuasiIso_algebraExtendScalars`:
the extension of scalars of sheaves sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms. This is the only functor-specific input of the left derived functor.
-/

@[expose] public section

universe v u₁ u

open CategoryTheory Limits

open scoped TensorProduct

namespace ModuleCat

variable (R : Type u₁) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

section Restrict

/-- The restriction of scalars from `S`-modules to `R`-modules along an `R`-algebra `S`:
an `S`-module `N` is regarded as an `R`-module through `r • n = algebraMap R S r • n`. -/
def algebraRestrictScalars : ModuleCat.{v} S ⥤ ModuleCat.{v} R where
  obj N := letI := Module.compHom N (algebraMap R S); of R N
  map {N N'} g :=
    letI := Module.compHom N (algebraMap R S)
    letI := Module.compHom N' (algebraMap R S)
    ofHom { g.hom with map_smul' := fun r ↦ g.hom.map_smul (algebraMap R S r) }

/-- The restriction of scalars along an algebra is, definitionally, Mathlib's restriction of
scalars along the ring homomorphism `algebraMap R S`. -/
lemma algebraRestrictScalars_eq_restrictScalars :
    algebraRestrictScalars.{v} R S = restrictScalars.{v} (algebraMap R S) :=
  rfl

variable {R S}

instance (N : ModuleCat.{v} S) : Module S ((algebraRestrictScalars R S).obj N) :=
  inferInstanceAs (Module S N)

@[simp]
lemma algebraRestrictScalars_smul_def (N : ModuleCat.{v} S) (r : R)
    (n : (algebraRestrictScalars R S).obj N) :
    r • n = (algebraMap R S r • n : N) :=
  rfl

instance (N : ModuleCat.{v} S) : IsScalarTower R S ((algebraRestrictScalars R S).obj N) where
  smul_assoc r s n := by
    change (r • s) • (n : N) = algebraMap R S r • s • (n : N)
    rw [Algebra.smul_def, mul_smul]

@[simp]
lemma algebraRestrictScalars_map_apply {N N' : ModuleCat.{v} S} (g : N ⟶ N')
    (n : (algebraRestrictScalars R S).obj N) :
    (algebraRestrictScalars R S).map g n = g n :=
  rfl

variable (R S)

instance : (algebraRestrictScalars.{v} R S).Additive :=
  inferInstanceAs (restrictScalars.{v} (algebraMap R S)).Additive

/-- The restriction of scalars is also a left adjoint, to Mathlib's coextension of scalars. -/
instance : (algebraRestrictScalars.{v} R S).IsLeftAdjoint :=
  ⟨_, ⟨restrictCoextendScalarsAdj.{v} (algebraMap R S)⟩⟩

end Restrict

section Extend

/-- The extension of scalars from `R`-modules to `S`-modules along an `R`-algebra `S`: an
`R`-module `M` is sent to `S ⊗[R] M`, with the `S`-module structure given by the algebra, and
a linear map `f` to its base change `f.baseChange S`. -/
def algebraExtendScalars : ModuleCat.{v} R ⥤ ModuleCat.{v} S where
  obj M := of S (S ⊗[R] M)
  map f := ofHom (f.hom.baseChange S)
  map_id M := by ext : 1; exact LinearMap.baseChange_id
  map_comp f g := by ext : 1; exact LinearMap.baseChange_comp _ _

variable {R S}

lemma algebraExtendScalars_obj (M : ModuleCat.{v} R) :
    (algebraExtendScalars R S).obj M = of S (S ⊗[R] M) :=
  rfl

@[simp]
lemma algebraExtendScalars_map_tmul {M M' : ModuleCat.{v} R} (f : M ⟶ M') (s : S) (m : M) :
    (algebraExtendScalars R S).map f (s ⊗ₜ[R] m) = s ⊗ₜ[R] f m :=
  rfl

variable (R S)

instance : (algebraExtendScalars.{v} R S).Additive where
  map_add := by intros; ext : 1; exact LinearMap.baseChange_add _ _

end Extend

section Adjunction

variable {R S} in
/-- The bijection underlying the adjunction between extension and restriction of scalars:
`S`-linear maps `S ⊗[R] M → N` correspond to `R`-linear maps `M → N`, by
`LinearMap.liftBaseChangeEquiv`. -/
def algebraExtendRestrictScalarsHomEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{v} S) :
    ((algebraExtendScalars R S).obj M ⟶ N) ≃ (M ⟶ (algebraRestrictScalars R S).obj N) :=
  letI := Module.compHom N (algebraMap R S)
  have : IsScalarTower R S N :=
    inferInstanceAs (IsScalarTower R S ((algebraRestrictScalars R S).obj N))
  homEquiv.trans <|
    (LinearMap.liftBaseChangeEquiv (M := M) (N := N) S).symm.toEquiv.trans
      (homEquiv (M := M) (N := (algebraRestrictScalars R S).obj N)).symm

/-- The extension of scalars along an `R`-algebra `S` is left adjoint to the restriction of
scalars, with hom-set bijection `ModuleCat.algebraExtendRestrictScalarsHomEquiv`. -/
def algebraExtendRestrictScalarsAdj :
    algebraExtendScalars.{v} R S ⊣ algebraRestrictScalars.{v} R S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := algebraExtendRestrictScalarsHomEquiv
      homEquiv_naturality_left_symm f g := by
        ext x
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul => rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      homEquiv_naturality_right f g := by
        ext
        rfl }

variable {R S}

@[simp]
lemma algebraExtendRestrictScalarsAdj_homEquiv_apply {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (g : (algebraExtendScalars R S).obj M ⟶ N) (m : M) :
    (algebraExtendRestrictScalarsAdj R S).homEquiv M N g m = g ((1 : S) ⊗ₜ[R] m) :=
  rfl

@[simp]
lemma algebraExtendRestrictScalarsAdj_homEquiv_symm_apply_tmul {M : ModuleCat.{v} R}
    {N : ModuleCat.{v} S} (f : M ⟶ (algebraRestrictScalars R S).obj N) (s : S) (m : M) :
    ((algebraExtendRestrictScalarsAdj R S).homEquiv M N).symm f (s ⊗ₜ[R] m) = s • (f m : N) :=
  rfl

@[simp]
lemma algebraExtendRestrictScalarsAdj_unit_app_apply (M : ModuleCat.{v} R) (m : M) :
    (algebraExtendRestrictScalarsAdj R S).unit.app M m = (1 : S) ⊗ₜ[R] m :=
  rfl

@[simp]
lemma algebraExtendRestrictScalarsAdj_counit_app_tmul (N : ModuleCat.{v} S) (s : S)
    (n : (algebraRestrictScalars R S).obj N) :
    (algebraExtendRestrictScalarsAdj R S).counit.app N (s ⊗ₜ[R] n) = s • (n : N) :=
  rfl

variable (R S)

instance : (algebraExtendScalars.{v} R S).IsLeftAdjoint :=
  (algebraExtendRestrictScalarsAdj R S).isLeftAdjoint

instance : (algebraRestrictScalars.{v} R S).IsRightAdjoint :=
  (algebraExtendRestrictScalarsAdj R S).isRightAdjoint

end Adjunction

section Comp

variable (T : Type v) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- For a tower of algebras `R → S → T`, restricting scalars from `T` to `R` is restricting
from `T` to `S` and then from `S` to `R`. This is Mathlib's `ModuleCat.restrictScalarsComp'`,
the composition `algebraMap R T = (algebraMap S T).comp (algebraMap R S)` being given by the
scalar tower. -/
noncomputable def algebraRestrictScalarsComp :
    algebraRestrictScalars.{v} R T ≅ algebraRestrictScalars S T ⋙ algebraRestrictScalars R S :=
  restrictScalarsComp' _ _ _ (IsScalarTower.algebraMap_eq R S T)

variable {R S T} in
@[simp]
lemma algebraRestrictScalarsComp_hom_app_apply (N : ModuleCat.{v} T)
    (n : (algebraRestrictScalars R T).obj N) :
    (algebraRestrictScalarsComp R S T).hom.app N n = n :=
  rfl

variable {R S T} in
@[simp]
lemma algebraRestrictScalarsComp_inv_app_apply (N : ModuleCat.{v} T)
    (n : (algebraRestrictScalars R S).obj ((algebraRestrictScalars S T).obj N)) :
    (algebraRestrictScalarsComp R S T).inv.app N n = n :=
  rfl

/-- For a tower of algebras `R → S → T`, extending scalars from `R` to `T` is extending from
`R` to `S` and then from `S` to `T`: the left adjoints of the two sides of
`ModuleCat.algebraRestrictScalarsComp` are isomorphic. -/
noncomputable def algebraExtendScalarsComp :
    algebraExtendScalars.{v} R T ≅ algebraExtendScalars R S ⋙ algebraExtendScalars S T :=
  (conjugateIsoEquiv ((algebraExtendRestrictScalarsAdj R S).comp
    (algebraExtendRestrictScalarsAdj S T)) (algebraExtendRestrictScalarsAdj R T)).symm
      (algebraRestrictScalarsComp R S T).symm

variable {R S T} in
@[simp]
lemma algebraExtendScalarsComp_hom_app_tmul (M : ModuleCat.{v} R) (t : T) (m : M) :
    (algebraExtendScalarsComp R S T).hom.app M (t ⊗ₜ[R] m) = t ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) := by
  simp only [algebraExtendScalarsComp, conjugateIsoEquiv, Equiv.coe_fn_symm_mk,
    conjugateEquiv_symm_apply_app, Adjunction.comp_unit_app]
  change t • ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) : T ⊗[S] (S ⊗[R] M)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Comp

end ModuleCat

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

/-- The restriction of scalars of sheaves of modules along an `R`-algebra `S`, applied
sectionwise: this preserves sheaves because the restriction of scalars of modules preserves
limits. -/
noncomputable def algebraRestrictScalars :
    Sheaf J (ModuleCat.{u + 1} S) ⥤ Sheaf J (ModuleCat.{u + 1} R) :=
  sheafCompose J (ModuleCat.algebraRestrictScalars R S)

/-- The extension of scalars of sheaves of modules along an `R`-algebra `S`: the sectionwise
extension of scalars `U ↦ S ⊗[R] F(U)`, followed by sheafification. -/
noncomputable def algebraExtendScalars :
    Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} S) :=
  composeAndSheafify J (ModuleCat.algebraExtendScalars R S)

/-- The extension of scalars of sheaves of modules is left adjoint to the restriction of
scalars, by `Sheaf.adjunction` applied to `ModuleCat.algebraExtendRestrictScalarsAdj`. -/
noncomputable def algebraExtendRestrictScalarsAdj :
    algebraExtendScalars J R S ⊣ algebraRestrictScalars J R S :=
  Sheaf.adjunction J (ModuleCat.algebraExtendRestrictScalarsAdj R S)

instance : (algebraRestrictScalars J R S).Additive where
  map_add := by
    intros
    ext1
    exact ((Functor.whiskeringRight _ _ _).obj (ModuleCat.algebraRestrictScalars R S)).map_add

instance : (algebraExtendScalars J R S).Additive :=
  (algebraExtendRestrictScalarsAdj J R S).left_adjoint_additive

instance : (algebraExtendScalars J R S).IsLeftAdjoint :=
  (algebraExtendRestrictScalarsAdj J R S).isLeftAdjoint

instance : (algebraRestrictScalars J R S).IsRightAdjoint :=
  (algebraExtendRestrictScalarsAdj J R S).isRightAdjoint

/-- The restriction of scalars of sheaves is also a left adjoint: it is isomorphic to
`Sheaf.composeAndSheafify` of the restriction of scalars of modules, which is a left adjoint
(to the coextension of scalars), and which preserves sheafification. -/
instance : (algebraRestrictScalars J R S).IsLeftAdjoint :=
  sheafCompose_isLeftAdjoint J (ModuleCat.algebraRestrictScalars R S)

section Comp

variable (T : Type (u + 1)) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- For a tower of algebras `R → S → T`, restricting scalars of sheaves from `T` to `R` is
restricting from `T` to `S` and then from `S` to `R`: this is
`ModuleCat.algebraRestrictScalarsComp`, applied sectionwise. -/
noncomputable def algebraRestrictScalarsComp :
    algebraRestrictScalars J R T ≅ algebraRestrictScalars J S T ⋙ algebraRestrictScalars J R S
    where
  hom := sheafCompose_map J (ModuleCat.algebraRestrictScalarsComp R S T).hom
  inv := sheafCompose_map J (ModuleCat.algebraRestrictScalarsComp R S T).inv
  hom_inv_id := by rw [← sheafCompose_comp, Iso.hom_inv_id, sheafCompose_id]; rfl
  inv_hom_id := by rw [← sheafCompose_comp, Iso.inv_hom_id, sheafCompose_id]; rfl

/-- For a tower of algebras `R → S → T`, extending scalars of sheaves from `R` to `T` is
extending from `R` to `S` and then from `S` to `T`: the left adjoints of the two sides of
`Sheaf.algebraRestrictScalarsComp` are isomorphic. -/
noncomputable def algebraExtendScalarsComp :
    algebraExtendScalars J R T ≅ algebraExtendScalars J R S ⋙ algebraExtendScalars J S T :=
  (conjugateIsoEquiv ((algebraExtendRestrictScalarsAdj J R S).comp
    (algebraExtendRestrictScalarsAdj J S T)) (algebraExtendRestrictScalarsAdj J R T)).symm
      (algebraRestrictScalarsComp J R S T).symm

end Comp

/-- The restriction of scalars of sheaves is exact. -/
example : PreservesFiniteLimits (algebraRestrictScalars J R S) := inferInstance

/-- The restriction of scalars of sheaves is exact. -/
example : PreservesFiniteColimits (algebraRestrictScalars J R S) := inferInstance

/-- The extension of scalars of sheaves sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms. This is the input needed to left derive it.

Sketch: the cone of a quasi-isomorphism between K-flat complexes is an acyclic K-flat complex
`K`, and the extension of scalars commutes with cones, so it suffices to see that
`S ⊗[R] K` is acyclic. Its restriction of scalars back to `R` is the tensor product `S ⊗ K` of
sheaves of `R`-modules with the constant sheaf `S`, which is acyclic because `K` is acyclic and
K-flat; and the restriction of scalars is exact and faithful, so it reflects acyclicity. -/
instance preservesKFlatQuasiIso_algebraExtendScalars :
    (algebraExtendScalars J R S).PreservesKFlatQuasiIso :=
  sorry

end CategoryTheory.Sheaf

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

/-- The restriction of scalars on the derived categories of sheaves of modules along an
`R`-algebra `S`. It is the functor induced by the exact restriction of scalars of sheaves,
applied levelwise. -/
noncomputable def algebraRestrictScalars :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} S)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  (Sheaf.algebraRestrictScalars J R S).mapDerivedCategory

/-- The derived extension of scalars `S ⊗ᴸ[R] -` on the derived categories of sheaves of
modules along an `R`-algebra `S`: the total left derived functor of the extension of scalars
of sheaves, computed on K-flat resolutions. -/
noncomputable def algebraExtendScalars :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} S)) :=
  (Sheaf.algebraExtendScalars J R S).leftDerivedFunctor

/-- The derived extension of scalars is left adjoint to the restriction of scalars on the
derived categories of sheaves of modules. It is the derived adjunction
`Adjunction.derivedAdjunction` of `Sheaf.algebraExtendRestrictScalarsAdj`, whose right adjoint
is the right derived functor of the restriction of scalars, transported along the
identification `Functor.rightDerivedFunctorIsoMapDerivedCategory` of that right derived
functor with the levelwise restriction of scalars, the latter being exact. -/
noncomputable def algebraExtendRestrictScalarsAdj :
    algebraExtendScalars J R S ⊣ algebraRestrictScalars J R S :=
  (Sheaf.algebraExtendRestrictScalarsAdj J R S).derivedAdjunction.ofNatIsoRight
    (Sheaf.algebraRestrictScalars J R S).rightDerivedFunctorIsoMapDerivedCategory

end DerivedCategory
