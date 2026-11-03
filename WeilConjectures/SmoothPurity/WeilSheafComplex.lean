/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!
# Weil sheaf and Weil complex

This module states the node `def-weil-weil-sheaf-complex` (latest blueprint,
`sk-thm-sfb-proper-base-change/def-weil-weil-sheaf-complex.md`, "Weil sheaf and Weil complex").

* The coefficient `Λ` is one of the two condensed rings of the node: `E̲` for a finite
  extension `E/ℚ_ℓ` inside `ℚ̄_ℓ`, or `ℚ̲̄_ℓ` (`WeilCoefficient`). Its ring object
  structure is the canonical one, `Sheaf.monObj_sheafCompose_obj`, on the underlying abelian
  sheaf of the condensed ring; no other monoid structure is ever bound.
* `Y = Y₀ ×_{k₀} k` is the geometric fibre and `g_Y` the geometric Frobenius
  (`FiniteFieldDatum.geometricFrobenius`).
* Weil modules, Weil sheaves, Weil complexes, strict Weil complexes and the realization
  `K ↦ (For K, θ_K)` are the recorded constructions of `Sheaf.Paper.CondensedWeilModules`
  at `Λ` and `g_Y`.
* Extension of scalars on Weil modules is the actual `Mod.extendScalars` along the coefficient
  inclusions `E̲ → F̲ → ℚ̲̄_ℓ`, transported to Weil modules by the (Pull) isomorphism
  `CondensedRing.pullIso`, and derived; on strict pairs it is the same functor on derived
  categories, transported by the derived (Pull) isomorphism.
* The clauses of the node that are assertions (exactness, closure, triangulated
  subcategory, truncations, heart, `For` t-exact and triangulated, `θ_K` compatible with shifts
  and triangles, heart equivalence, non-faithfulness on `Spec k`, scalar extension, descent
  (1)–(3)) are the named theorems below; their proofs are the proof steps 1–7 of the node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.longLine false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open CategoryTheory.Pretriangulated

namespace WeilConjectures

/-! ### Coefficients -/

/-- The coefficients allowed by the node: a finite extension `E` of `ℚ_ℓ` inside
`ℚ̄_ℓ = PadicAlgCl ℓ`, or `ℚ̄_ℓ` itself.
Source: `def-weil-weil-sheaf-complex`, first paragraph, "`Λ ∈ {E̲, ℚ̲̄_ℓ}`"
(blueprint: def-weil-weil-sheaf-complex). -/
inductive WeilCoefficient (ell : ℕ) [Fact ell.Prime] where
  /-- the condensed ring `E̲` of a finite extension `E/ℚ_ℓ` inside `ℚ̄_ℓ` -/
  | finite (E : PadicAlgCl.FiniteIntermediateField ell)
  /-- the condensed ring `ℚ̲̄_ℓ` -/
  | qbar

/-- The condensed ring `Λ` of a coefficient: `E̲ = C(-, E)` ([det-def-sfb-condensed-ring]) or
`ℚ̲̄_ℓ` ([sk-def-sfb-qlbar-condensed]).
Source: `def-weil-weil-sheaf-complex`, first paragraph (blueprint: def-weil-weil-sheaf-complex). -/
noncomputable abbrev WeilCoefficient.ring {ell : ℕ} [Fact ell.Prime] :
    WeilCoefficient ell → Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}
  | .finite E => Profinite.continuousMapRingSheaf E
  | .qbar => Profinite.padicAlgClCondensedRing ell

/-- The underlying condensed abelian group of `Λ`, a commutative ring object through the
canonical instance `Sheaf.monObj_sheafCompose_obj`.
Source: `def-weil-weil-sheaf-complex`, first paragraph (blueprint: def-weil-weil-sheaf-complex). -/
abbrev WeilCoefficient.ab {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  coefficientHeartRingObj (WeilCoefficient.ring c)

/-- The coefficient inclusion `E̲ → F̲` for finite `E ⊆ F` inside `ℚ̄_ℓ`.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable abbrev weilCoefficientMap {ell : ℕ} [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    WeilCoefficient.ab.{u} (.finite E) ⟶ WeilCoefficient.ab (.finite F) :=
  Profinite.padicSubfieldRingObjMap ell h

/-- The coefficient inclusion `E̲ → ℚ̲̄_ℓ`.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable abbrev weilCoefficientToQbar {ell : ℕ} [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    WeilCoefficient.ab.{u} (.finite E) ⟶ WeilCoefficient.ab (WeilCoefficient.qbar (ell := ell)) :=
  Profinite.padicSubfieldRingObjToPadicAlgCl ell E

/-- The abelian category `Mod_W(Y, Λ)` of Weil `Λ_Y`-modules `(M, θ : g_Y^* M ≅ M)` on the
geometric fibre `Y = Y₀ ×_{k₀} k`, for the geometric Frobenius `g_Y`.
Source: `def-weil-weil-sheaf-complex`, "Weil sheaves", the displayed `θ`
(blueprint: def-weil-weil-sheaf-complex). -/
abbrev weilSheafModuleCategory
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (c : WeilCoefficient ell) : Type _ :=
  condensedWeilModules (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom

/-! ### The categories -/

/-- The category `D^b_{c,W}(Y, Λ)` of Weil complexes: the full subcategory of
`D(Mod_W(Y, Λ))` of bounded complexes whose cohomology objects are Weil sheaves.
Source: `def-weil-weil-sheaf-complex`, "Weil complexes" (blueprint: def-weil-weil-sheaf-complex). -/
abbrev weilComplexCategory
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (c : WeilCoefficient ell) : Type _ :=
  condensedWeilComplex (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom

/-- The category of strict Weil complexes: pairs `(K, θ : Lg_Y^* K ≅ K)` with
`K ∈ D^b_c(Y, Λ)`, morphisms commuting with `θ`.
Source: `def-weil-weil-sheaf-complex`, "Strict Weil complexes"
(blueprint: def-weil-weil-sheaf-complex). -/
abbrev strictWeilComplexCategory
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (c : WeilCoefficient ell) : Type _ :=
  condensedStrictWeilComplex (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom

/-- The functor `K ↦ (For K, θ_K)` from Weil complexes to strict Weil complexes.
Source: `def-weil-weil-sheaf-complex`, "Strict Weil complexes"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable def weilComplexRealization
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (c : WeilCoefficient ell) :
    weilComplexCategory D ell _hell Y₀ c ⥤ strictWeilComplexCategory D ell _hell Y₀ c :=
  condensedWeilRealization (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom

/-- On the hearts, `K ↦ (For K, θ_K)` is an equivalence onto the strict Weil complexes whose
carrier lies in the heart (the pairs `(𝓕, θ)` with `𝓕 ∈ Sh_c(Y, Λ)`): it is bijective on
morphisms between Weil complexes in the heart, and every such pair is its image.
Source: `def-weil-weil-sheaf-complex`, "Strict Weil complexes", "On the hearts it is an
equivalence" (blueprint: def-weil-weil-sheaf-complex).
Proof (node step 2): on hearts the derived realization restricts to the forgetful
identification of Weil sheaves with fixed pairs in `Sh_c(Y, Λ)`
(`lem-pur-derived-fixed-pair-realization`), since morphisms in the heart are morphisms of
sheaves. -/
theorem weilComplexRealization_heart_equivalence
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (c : WeilCoefficient ell) :
    (∀ K L : weilComplexCategory D ell _hell Y₀ c,
      DerivedCategory.TStructure.t.IsLE K.obj 0 → DerivedCategory.TStructure.t.IsGE K.obj 0 →
      DerivedCategory.TStructure.t.IsLE L.obj 0 → DerivedCategory.TStructure.t.IsGE L.obj 0 →
        Function.Bijective (fun f : K ⟶ L ↦ (weilComplexRealization D ell _hell Y₀ c).map f)) ∧
    (∀ P : strictWeilComplexCategory D ell _hell Y₀ c,
      DerivedCategory.TStructure.t.IsLE P.obj.carrier 0 →
      DerivedCategory.TStructure.t.IsGE P.obj.carrier 0 →
        ∃ K : weilComplexCategory D ell _hell Y₀ c,
          DerivedCategory.TStructure.t.IsLE K.obj 0 ∧ DerivedCategory.TStructure.t.IsGE K.obj 0 ∧
            Nonempty ((weilComplexRealization D ell _hell Y₀ c).obj K ≅ P)) := by sorry

/-- The realization `K ↦ (For K, θ_K)` is not faithful on `Y = Spec k`
(`Y₀ = Spec k₀`): two different morphisms of Weil complexes have the same image.
Source: `def-weil-weil-sheaf-complex`, "Strict Weil complexes", "It is not faithful"
(blueprint: def-weil-weil-sheaf-complex).
Proof (node step 3): on `Spec k`, underlying `Ext^1(Λ, Λ) = 0` by exact point evaluation
(`def-weil-finite-coefficient-point`). Give `J = Λ²` the action `(x, y) ↦ (x + y, y)`; a
splitting would send `1` to `(a, 1)`, which is not fixed. The derived realization therefore
sends this nonzero class `Λ → Λ[1]` of `D^b_{c,W}` to zero, the image of the zero map. -/
theorem weilComplexRealization_not_faithful
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (c : WeilCoefficient ell) :
    ∃ K L : weilComplexCategory D ell _hell (Over.mk (𝟙 (Spec (.of D.k₀)))) c,
      ∃ f₁ f₂ : K ⟶ L, f₁ ≠ f₂ ∧
        (weilComplexRealization D ell _hell (Over.mk (𝟙 (Spec (.of D.k₀)))) c).map f₁ =
          (weilComplexRealization D ell _hell (Over.mk (𝟙 (Spec (.of D.k₀)))) c).map f₂ := by sorry

/-- Extension of scalars on Weil modules along a coefficient map `a : Λ → Λ'`:
`(M, θ) ↦ (Λ'_Y ⊗_{Λ_Y} M, θ')`, the structure transported by the (Pull) isomorphism
`g^* ∘ Ext_a ≅ Ext_a ∘ g^*` (`CondensedRing.pullIso`). It is used below only at the item's
coefficient inclusions `E̲ → F̲ → ℚ̲̄_ℓ`.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients",
`M ↦ M_F = F_Y ⊗_{E_Y} M` (blueprint: def-weil-weil-sheaf-complex). -/
noncomputable abbrev weilModuleExtendScalars
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {Y : Scheme.{u}} (g : Y ⟶ Y) :
    condensedWeilModules Λ g ⥤ condensedWeilModules Λ' g :=
  Endofunctor.IsoAlgebra.mapOfNatIso (CondensedRing.pullIso a g).symm

/-- The derived (Pull) isomorphism `Ext_a ∘ Lg^* ≅ Lg^* ∘ Ext_a` on derived categories of
modules, for an exact extension of scalars.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients",
"commutes with `g_Y^*`" (blueprint: def-weil-weil-sheaf-complex). -/
noncomputable def weilDerivedPullExtendScalarsIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {Y : Scheme.{u}} (g : Y ⟶ Y)
    [Limits.PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Y))] :
    (Mod.extendScalars (coefficientMap a Y)).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ' g).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ g).mapDerivedCategory ⋙
        (Mod.extendScalars (coefficientMap a Y)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.pullIso a g).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Extension of scalars on strict pairs `(K, θ) ↦ (Λ'_Y ⊗ K, θ')`, the structure transported
by the derived (Pull) isomorphism.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable def weilStrictExtendScalars
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {Y : Scheme.{u}} (g : Y ⟶ Y)
    [Limits.PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Y))] :
    Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ g).mapDerivedCategory ⥤
      Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ' g).mapDerivedCategory :=
  Endofunctor.IsoAlgebra.mapOfNatIso (weilDerivedPullExtendScalarsIso a g)

/-- The derived extension of scalars of Weil complexes `D(Mod_W(Y, E)) → D(Mod_W(Y, F))`,
`K ↦ K_F`, for finite `E ⊆ F` inside `ℚ̄_ℓ`.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable abbrev weilComplexExtendSubfield
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    DerivedCategory (weilSheafModuleCategory D ell _hell Y₀ (.finite E)) ⥤
      DerivedCategory (weilSheafModuleCategory D ell _hell Y₀ (.finite F)) :=
  (weilModuleExtendScalars (weilCoefficientMap h) (D.geometricFrobenius Y₀).hom).mapDerivedCategory

/-- The derived extension of scalars of Weil complexes `D(Mod_W(Y, E)) → D(Mod_W(Y, ℚ̄_ℓ))`,
`K ↦ K_{ℚ̄_ℓ}`.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable abbrev weilComplexExtendToQbar
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    DerivedCategory (weilSheafModuleCategory D ell _hell Y₀ (.finite E)) ⥤
      DerivedCategory (weilSheafModuleCategory D ell _hell Y₀ .qbar) :=
  (weilModuleExtendScalars (weilCoefficientToQbar E) (D.geometricFrobenius Y₀).hom).mapDerivedCategory

/-- Extension of scalars of strict pairs over `E̲` to strict pairs over `ℚ̲̄_ℓ`.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable def weilStrictExtendToQbar
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    Endofunctor.IsoAlgebra (CondensedRing.upperStar (WeilCoefficient.ab (.finite E))
        (D.geometricFrobenius Y₀).hom).mapDerivedCategory ⥤
      Endofunctor.IsoAlgebra (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar (ell := ell)))
        (D.geometricFrobenius Y₀).hom).mapDerivedCategory :=
  weilStrictExtendScalars (weilCoefficientToQbar E) (D.geometricFrobenius Y₀).hom

/-- The canonical isomorphism `Ext_{F→ℚ̄_ℓ} ∘ Ext_{E→F} ≅ Ext_{E→ℚ̄_ℓ}` of extensions of scalars
of modules (`Mod.extendScalarsComp` and `E̲ → F̲ → ℚ̲̄_ℓ = E̲ → ℚ̲̄_ℓ`).
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients", the chain
`D^b_{c,W}(Y,E) → D^b_{c,W}(Y,F) → D^b_{c,W}(Y,ℚ̄_ℓ)` (blueprint: def-weil-weil-sheaf-complex). -/
noncomputable def weilCoefficientCompIso
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    Mod.extendScalars (coefficientMap (weilCoefficientMap h) (D.geometricFiber Y₀).left) ⋙
        Mod.extendScalars (coefficientMap (weilCoefficientToQbar F) (D.geometricFiber Y₀).left) ≅
      Mod.extendScalars (coefficientMap (weilCoefficientToQbar E) (D.geometricFiber Y₀).left) :=
  (Mod.extendScalarsComp _ _).symm ≪≫
    Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl (D.geometricFiber Y₀).left ell h)

/-- The isomorphism of Weil-module extensions of scalars `Ext_{F→ℚ̄_ℓ} ∘ Ext_{E→F} ≅ Ext_{E→ℚ̄_ℓ}`
whose underlying module maps are the canonical `weilCoefficientCompIso` (unique, the forgetful
functor of Weil modules being faithful).
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
def IsCanonicalWeilCompIso
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    (e : weilModuleExtendScalars (weilCoefficientMap h) (D.geometricFrobenius Y₀).hom ⋙
        weilModuleExtendScalars (weilCoefficientToQbar F) (D.geometricFrobenius Y₀).hom ≅
      weilModuleExtendScalars (weilCoefficientToQbar E) (D.geometricFrobenius Y₀).hom) : Prop :=
  ∀ M, (e.hom.app M).hom.f = (weilCoefficientCompIso D ell Y₀ h).hom.app M.carrier

/-- The derived isomorphism `(K_F)_{ℚ̄_ℓ} ≅ K_{ℚ̄_ℓ}` induced by an isomorphism of Weil-module
extensions of scalars (used with the canonical one, `IsCanonicalWeilCompIso`).
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable abbrev weilComplexExtendCompIso
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F)
    (e : weilModuleExtendScalars (weilCoefficientMap h) (D.geometricFrobenius Y₀).hom ⋙
        weilModuleExtendScalars (weilCoefficientToQbar F) (D.geometricFrobenius Y₀).hom ≅
      weilModuleExtendScalars (weilCoefficientToQbar E) (D.geometricFrobenius Y₀).hom) :
    weilComplexExtendSubfield D ell _hell Y₀ h ⋙ weilComplexExtendToQbar D ell _hell Y₀ F ≅
      weilComplexExtendToQbar D ell _hell Y₀ E :=
  (Functor.mapDerivedCategoryCompIso
      (weilModuleExtendScalars (weilCoefficientMap h) (D.geometricFrobenius Y₀).hom)
      (weilModuleExtendScalars (weilCoefficientToQbar F) (D.geometricFrobenius Y₀).hom)).symm ≪≫
    Functor.mapDerivedCategoryNatIso e

/-- Descent clauses (1)–(3) of the node, for the actual extensions of scalars above.
(1) every strict Weil complex over `ℚ̄_ℓ` is the extension of a strict Weil complex over some
finite `F`, a sheaf when the given one is (its carrier in the heart), and morphisms of strict
Weil complexes descend; (2) for Weil complexes `K, L` over `E` and `r ∈ ℤ`,
`colim_F Hom_{D^b_{c,W}(Y,F)}(K_F, L_F[r]) → Hom_{D^b_{c,W}(Y,ℚ̄_ℓ)}(K_{ℚ̄_ℓ}, L_{ℚ̄_ℓ}[r])` is an
isomorphism: a class dying over `ℚ̄_ℓ` dies over some finite `H`, and every class over `ℚ̄_ℓ`
comes from some finite `F` (through the canonical composition isomorphism); (3) every Weil
complex over `ℚ̄_ℓ` is `K_{ℚ̄_ℓ}` for some finite `E` and some Weil complex `K` over `E`.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients",
clauses (1)–(3) (blueprint: def-weil-weil-sheaf-complex).
Proof (node steps 5–7). Step 5: descend the carrier by (Obj), then `θ, θ⁻¹` by (Hom-surj); by
(Hom-inj) their inverse identities hold at a common larger finite field; descend commuting
morphisms likewise; for a sheaf, all off-zero cohomology vanishes at that field because
`M → M_{ℚ̄_ℓ}` is monic (step 4). Step 6: apply the cyclic derived Hom sequence
(`lem-sf-cyclic-derived-hom-exact-sequence`) to `K, L[r]`; its outer terms are coinvariants of
`V^{r-1}` and invariants of `V^r`; Hom-surj/inj identify `colim_F V_F^j = V_{ℚ̄_ℓ}^j`; filtered
colimits are exact and the short five lemma gives (2). Step 7: induct on the number of nonzero
cohomology sheaves; truncate at the top degree, descend `A = τ^{<m}K` and `B = H^m(K)[-m]` to a
common field, descend `δ : B → A[1]` by (2), and complete it to a triangle. -/
theorem weilDescent_properties
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    -- (1) objects, with the sheaf clause
    (∀ K : strictWeilComplexCategory D ell _hell Y₀ .qbar,
      ∃ (F : PadicAlgCl.FiniteIntermediateField ell)
        (KF : strictWeilComplexCategory D ell _hell Y₀ (.finite F)),
        Nonempty ((weilStrictExtendToQbar D ell _hell Y₀ F).obj KF.obj ≅ K.obj) ∧
        (DerivedCategory.TStructure.t.IsLE K.obj.carrier 0 →
          DerivedCategory.TStructure.t.IsGE K.obj.carrier 0 →
            DerivedCategory.TStructure.t.IsLE KF.obj.carrier 0 ∧
              DerivedCategory.TStructure.t.IsGE KF.obj.carrier 0)) ∧
    -- (1) morphisms
    (∀ (F : PadicAlgCl.FiniteIntermediateField ell)
        (K L : strictWeilComplexCategory D ell _hell Y₀ (.finite F))
        (h : (weilStrictExtendToQbar D ell _hell Y₀ F).obj K.obj ⟶
          (weilStrictExtendToQbar D ell _hell Y₀ F).obj L.obj),
      ∃ (F' : PadicAlgCl.FiniteIntermediateField ell) (_ : F ≤ F')
        (K' L' : strictWeilComplexCategory D ell _hell Y₀ (.finite F'))
        (eK : (weilStrictExtendToQbar D ell _hell Y₀ F').obj K'.obj ≅
          (weilStrictExtendToQbar D ell _hell Y₀ F).obj K.obj)
        (eL : (weilStrictExtendToQbar D ell _hell Y₀ F').obj L'.obj ≅
          (weilStrictExtendToQbar D ell _hell Y₀ F).obj L.obj)
        (h' : K' ⟶ L'),
        (weilStrictExtendToQbar D ell _hell Y₀ F').map h'.hom = eK.hom ≫ h ≫ eL.inv) ∧
    -- (2) Hom groups of Weil complexes
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
        (K L : weilComplexCategory D ell _hell Y₀ (.finite E)) (r : ℤ),
      (∀ (F : PadicAlgCl.FiniteIntermediateField ell) (hF : E ≤ F)
          (a : (weilComplexExtendSubfield D ell _hell Y₀ hF).obj K.obj ⟶
            (weilComplexExtendSubfield D ell _hell Y₀ hF).obj (L.obj⟦r⟧)),
        (weilComplexExtendToQbar D ell _hell Y₀ F).map a = 0 →
          ∃ (H : PadicAlgCl.FiniteIntermediateField ell) (hH : F ≤ H),
            (weilComplexExtendSubfield D ell _hell Y₀ hH).map a = 0) ∧
      (∀ ψ : (weilComplexExtendToQbar D ell _hell Y₀ E).obj K.obj ⟶
          (weilComplexExtendToQbar D ell _hell Y₀ E).obj (L.obj⟦r⟧),
        ∃ (F : PadicAlgCl.FiniteIntermediateField ell) (hF : E ≤ F)
          (a : (weilComplexExtendSubfield D ell _hell Y₀ hF).obj K.obj ⟶
            (weilComplexExtendSubfield D ell _hell Y₀ hF).obj (L.obj⟦r⟧)),
          ∀ e, IsCanonicalWeilCompIso D ell Y₀ hF e →
            ψ = (weilComplexExtendCompIso D ell _hell Y₀ hF e).inv.app K.obj ≫
              (weilComplexExtendToQbar D ell _hell Y₀ F).map a ≫
                (weilComplexExtendCompIso D ell _hell Y₀ hF e).hom.app (L.obj⟦r⟧))) ∧
    -- (3) Weil complexes
    (∀ K : weilComplexCategory D ell _hell Y₀ .qbar,
      ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
        (KE : weilComplexCategory D ell _hell Y₀ (.finite E)),
        Nonempty ((weilComplexExtendToQbar D ell _hell Y₀ E).obj KE.obj ≅ K.obj)) := by sorry

/-! ### Frobenius, Weil sheaves, Weil complexes -/

/-! ### Non-faithfulness on `Spec k` -/

/-! ### Extension of scalars -/

/-! ### Descent to a finite field of coefficients -/

end WeilConjectures
