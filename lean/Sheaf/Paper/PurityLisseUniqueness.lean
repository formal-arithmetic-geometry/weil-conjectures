/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.Paper.ProEtaleLisseOrigin
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-!
# Uniqueness for lisse sheaf maps

Source: blueprint sec-smooth-purity/sk-prop-a1-inv/lem-pur-lisse-uniqueness.md
(blueprint: lem-pur-lisse-uniqueness).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry
namespace ProEtale

/-- In the finite coefficient purity setting, restriction to the punctured affine line and
restriction to the unit section are faithful on morphisms between lisse pro-etale module sheaves.
Source: blueprint sec-smooth-purity/sk-prop-a1-inv/lem-pur-lisse-uniqueness.md
(blueprint: lem-pur-lisse-uniqueness).

The proof follows the source's three steps. First use a finite affine cover of `B`:
the charts have rings `R[t]` and `R[t,t⁻¹]`, finite type over the base field.
Their relative diagonals are cut out by the difference of the two coordinates;
compose with the closed base-change of the diagonal of `B` to obtain separatedness.
For the empty base the empty covering forces every module sheaf to be zero. For the first
assertion, take the difference of two maps, use the inverse-image geometric-stalk comparison
for `j`, and choose one geometric point in each connected component meeting the open; the two
clauses of `lem-pur-lisse-morphism-rigidity` then force the difference to vanish. For the second
assertion use the unit-section intersection with every component of `G`, apply the same stalk
comparison to `e`, and invoke the same rigidity clauses. Choose each geometric point by
an algebraic closure of the residue field of the selected point. For both assertions,
`prop-weil-pbc-proetale-constant-ring-map` identifies the inverse-image coefficient ring
with the constant coefficient ring. The maps `m ⊗ r ↦ c⁻¹(r)m` and `m ↦ m ⊗ 1`
identify module restriction with the fixed-module inverse image and its stalk maps.
The finite coefficient ring is `P.Coefficient` of the fixed purity setting. -/
theorem lisse_map_restriction_unique
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (G : Scheme.{u})
    (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ)
    (e : B ⟶ G)
    (he : e ≫ j = AffineSpace.oneSection (ULift.{u} (Fin 1)) B)
    (L₁ M₁ : Sheaf (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) B))
      (ModuleCat.{u + 1} P.Coefficient))
    (L₂ M₂ : Sheaf (Scheme.ProEt.topology G) (ModuleCat.{u + 1} P.Coefficient))
    (hL₁ : Scheme.IsLisseProEtaleFixedModuleSheaf
      (AffineSpace (ULift.{u} (Fin 1)) B) P.Coefficient L₁)
    (hM₁ : Scheme.IsLisseProEtaleFixedModuleSheaf
      (AffineSpace (ULift.{u} (Fin 1)) B) P.Coefficient M₁)
    (hL₂ : Scheme.IsLisseProEtaleFixedModuleSheaf G P.Coefficient L₂)
    (hM₂ : Scheme.IsLisseProEtaleFixedModuleSheaf G P.Coefficient M₂) :
    (∀ (φ ψ : L₁ ⟶ M₁),
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).map φ =
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).map ψ → φ = ψ) ∧
    (∀ (φ ψ : L₂ ⟶ M₂),
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).map φ =
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).map ψ → φ = ψ) := by
  sorry

end ProEtale
end AlgebraicGeometry
