/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateLocalRootTensorsExt

/-! # Derived morphism realization of the Cartier Chern clause

Source: CartierKummerChern, Stacks Tag 099R, and Mathlib Ext.mapExactFunctor_hom.
(blueprint: lem-pur-cartier-chern-hom-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

set_option maxHeartbeats 2000000 in
-- Comparing the cached Ext realization needs more reduction steps.
/-- The Cartier Chern clause has its ordinary class and its normalized derived realization.
Source: CartierKummerChern; Stacks Tag 099R; Mathlib Ext.mapExactFunctor_hom.
(blueprint: lem-pur-cartier-chern-hom-transport).

Proof: obtain k and the root-normalized isomorphism q from CartierKummerChern.
Root-tensor extensionality identifies q with twistComparison, since both send every
locally lifted scalar root tensor to the prescribed pro-etale generator. Take Ext.hom
of the realization equation. The formulas for Ext composition, degree-zero maps and
exact functors express it using the single-complex comparison beta, the derived
comparison and its shift isomorphism. Precompose by beta.hom, cancel beta.inv,
expand ShiftedHom.map, and combine the shifted maps. The result is precisely
comparison(k.hom) followed by twistDerived.hom. Keep the ordinary class equation
from the original Chern clause. This argument is categorical, so empty schemes and
zero coefficient rings satisfy the same equations; no flatness is used. -/
theorem cartierChern_hom_transport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤)))
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    ∃ k : Ext (Etale.ordinaryFiniteConstant (Scheme.finiteTateCoefficient l E n) T)
      (Scheme.finiteEtaleTateLine T (l ^ (r + 1))
        (Scheme.finiteTateCoefficient l E n) hA) 2,
      (Ext.mk₀ (Etale.ordinaryFiniteIntegralGenerator
        (Scheme.finiteTateCoefficient l E n) T)).comp
        (k.mapExactFunctor (Etale.RawModuleScalarComparison.forget
          (Scheme.finiteTateCoefficient l E n) T)) (zero_add 2) =
        Etale.supportedKummerChern (Scheme.finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA i hI
          (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) ∧
      ((comparisonUpperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        T).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          (Etale.cartierConstantComparison (Scheme.finiteTateCoefficient l E n) T) ≫
        (DerivedCategory.singleFunctor _ 0).map (Etale.cartierSupportedUnit l E n i) ≫
        Etale.finiteCartierKummerMap l E n i hI hT =
      (comparison (Scheme.finiteTateCoefficient l E n) T).map k.hom ≫
        (twistDerived l E n T hT r hA 1 2).hom := by
  have hdata := (Etale.cartier_kummer_map l E).2.exists.choose_spec
  have hcprop := hdata.2.2.2.1
  unfold Etale.CartierKummerChern at hcprop
  obtain ⟨k, q, hq, hclass, heq⟩ := hcprop n i hI hT r hA
  have hqhom : q = twistComparison l E n T hT r hA 1 := by
    apply Iso.ext
    unfold twistComparison
    apply Scheme.finiteTate_local_root_tensors_hom_ext l E n T hT r hA 1
    intro U W v a z x hx
    exact (hq U W v a z x hx).trans
      (((Scheme.finite_tate_site_descent l E n).choose_spec.1
        T hT r hA 1 U W v a z x hx).symm)
  have hh := congrArg (fun e ↦ Ext.hom.{u + 1} e) heq
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom] at hh
  rw [hqhom] at hh
  have hh' := congrArg
    (fun f ↦ ((comparisonUpperStar
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      T).mapDerivedCategorySingleFunctor 0).hom.app _ ≫ f) hh
  simp only [ShiftedHom.map, Category.assoc, Nat.cast_ofNat] at hh'
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hh'
  refine ⟨k, hclass, ?_⟩
  simp only [Etale.finiteCartierKummerMap, twistDerived, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, comparison, geoP1Comparison,
    Scheme.finiteEtaleTateTwist] at hh' ⊢
  with_reducible_and_instances
    convert hh' using 1
  congr 3
  with_unfolding_all rfl

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
