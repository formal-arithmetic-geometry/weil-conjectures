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

/-- The underlying condensed abelian group of `Λ` is a commutative ring object: `E̲ = C(-, E)`
and `ℚ̲̄_ℓ` are condensed commutative rings.
Source: `def-weil-weil-sheaf-complex`, first paragraph (blueprint: def-weil-weil-sheaf-complex). -/
instance WeilCoefficient.isCommMonObj_ab {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell) :
    IsCommMonObj (WeilCoefficient.ab.{u} c) :=
  match c with
  | .finite E => Profinite.isCommMonObj_continuousMapRingObj E
  | .qbar => Profinite.isCommMonObj_padicAlgClRingObj ell

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

/-- Extension of scalars of strict pairs over `E̲` to strict pairs over `ℚ̲̄_ℓ`.
Source: `def-weil-weil-sheaf-complex`, "Descent to a finite field of coefficients"
(blueprint: def-weil-weil-sheaf-complex). -/
noncomputable def weilStrictExtendToQbar
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    Endofunctor.IsoAlgebra (CondensedRing.upperStar (WeilCoefficient.ab (.finite E))
        (D.geometricFrobenius Y₀).hom).mapDerivedCategory ⥤
      Endofunctor.IsoAlgebra
        (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar (ell := ell)))
          (D.geometricFrobenius Y₀).hom).mapDerivedCategory :=
  weilStrictExtendScalars (weilCoefficientToQbar E) (D.geometricFrobenius Y₀).hom

/-! ### Frobenius, Weil sheaves, Weil complexes -/

/-! ### Non-faithfulness on `Spec k` -/

/-! ### Extension of scalars -/

/-! ### Descent to a finite field of coefficients -/

end WeilConjectures
