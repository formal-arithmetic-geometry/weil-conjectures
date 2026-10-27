/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.CartierKummerData
import Sheaf.AlgebraicGeometry.CartierKummerDescent
import Sheaf.AlgebraicGeometry.CartierKummerNaturality
import Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence
import all Sheaf.AlgebraicGeometry.SupportedDerivedUnitForget
import Sheaf.AlgebraicGeometry.SupportedKummerChernRealization
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # The supported Cartier Kummer morphism

Source: blueprint main-20261015, lem-amb-cartier-kummer-map, paragraphs 1--4.
(blueprint: lem-amb-cartier-kummer-map)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
section
universe uC uD vC vD wC wD
variable {C : Type uC} {B : Type uD} [Category.{vC} C] [Category.{vD} B]
  [Abelian C] [Abelian B] [HasExt.{wC} C] [HasExt.{wD} B]

private theorem constantUnit_transport (F : C ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X P Q : C} {X' P' Q' : B} (u : X ⟶ P) (v : X' ⟶ P')
    (a : F.obj X ⟶ X') (b : F.obj P ⟶ P') (q : F.obj Q ⟶ Q')
    (κ : Ext P Q 2) (c : Ext P' Q' 2)
    (hu : F.map u ≫ b = a ≫ v)
    (hc : (Ext.mk₀ b).comp c (zero_add 2) =
      (κ.mapExactFunctor F).comp (Ext.mk₀ q) (add_zero 2)) :
    (Ext.mk₀ a).comp ((Ext.mk₀ v).comp c (zero_add 2)) (zero_add 2) =
      (((Ext.mk₀ u).comp κ (zero_add 2)).mapExactFunctor F).comp
        (Ext.mk₀ q) (add_zero 2) := by
  rw [Ext.mk₀_comp_mk₀_assoc, ← hu, ← Ext.mk₀_comp_mk₀_assoc, hc,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

private theorem map_composite_precompose (F : C ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X P Q : C} {Y Z : B} (a : Z ⟶ F.obj X) (u : X ⟶ P)
    (v : Z ⟶ Y) (b : Y ⟶ F.obj P) (κ : Ext P Q 2)
    (h : a ≫ F.map u = v ≫ b) :
    (Ext.mk₀ a).comp (((Ext.mk₀ u).comp κ (zero_add 2)).mapExactFunctor F)
        (zero_add 2) =
      (Ext.mk₀ v).comp ((Ext.mk₀ b).comp (κ.mapExactFunctor F) (zero_add 2))
        (zero_add 2) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    h, ← Ext.mk₀_comp_mk₀_assoc]

end

namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
open Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem cartierCoefficient_annihilated (n : ℕ) :
    ((l ^ (n + 1) : ℕ) : finiteTateCoefficient l E n) = 0 := by
  let h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hm : ∀ x : Padic.coefficientExtensionIntegers l E,
      x ∈ Padic.coefficientExtensionMaximalIdeal l E ↔
        Padic.coefficientExtensionAbsoluteValue l E (x : E) < 1 := h.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hl : (l : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) := by
    rw [hgen, hm]
    have he := spectralNorm_extends (K := Padic l) (L := E) (l : Padic l)
    change spectralNorm (Padic l) E (l : E) < 1
    rw [map_natCast] at he
    rw [he, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hp : (l : Padic.coefficientExtensionIntegers l E) ^ (n + 1) ∈
      Padic.coefficientExtensionIdeal l E (n + 1) :=
    Ideal.pow_mem_pow hl (n + 1)
  have hz : ((l ^ (n + 1) : ℕ) : Padic.coefficientExtensionRing l E (n + 1)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _)]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [Nat.cast_pow] using hp
  exact congrArg (ULift.up : Padic.coefficientExtensionRing l E (n + 1) →
    finiteTateCoefficient l E n) hz

private theorem cartierEtaleFamily_unique
    (κ κ' : CartierEtaleKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ)
    (hκ' : CartierEtaleKummerNormalization l E κ') : κ = κ' := by
  unfold CartierEtaleKummerNormalization at hκ hκ'
  funext n r hA D T i hi hI hT
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  exact (supported_cartier_boundary_existsUnique T (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (finiteTateCoefficient l E n) hA
    (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) i hI).unique
      (hκ n r hA i hI hT) (hκ' n r hA i hI hT)

private theorem cartierEtaleFamily_existsUnique :
    ∃! κ : CartierEtaleKummerFamily l E, CartierEtaleKummerNormalization l E κ := by
  classical
  have hc (n r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
      {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
      (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) := by
    let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
      Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    exact supported_cartier_boundary_existsUnique T (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (finiteTateCoefficient l E n) hA
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) i hI
  let κ : CartierEtaleKummerFamily l E :=
    fun n r hA _ _ i _ hI hT ↦ (hc n r hA i hI hT).exists.choose
  have hκ : CartierEtaleKummerNormalization l E κ := by
    unfold CartierEtaleKummerNormalization
    intro n r hA D T i hi hI hT
    exact (hc n r hA i hI hT).exists.choose_spec
  refine ⟨κ, hκ, ?_⟩
  intro κ' hκ'
  exact cartierEtaleFamily_unique l E κ' κ hκ' hκ

private theorem boundary_chern_composite (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hT : IsUnit (N : Γ(T, ⊤)))
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ) :
    (Ext.mk₀ (ordinaryFiniteIntegralGenerator A T)).comp
      (((Ext.mk₀ (supportedConstantUnit A i)).comp κ (zero_add 2)).mapExactFunctor
        (RawModuleScalarComparison.forget A T)) (zero_add 2) =
      supportedKummerChern A N hA i hI hT := by
  exact (map_composite_precompose (RawModuleScalarComparison.forget A T)
    (ordinaryFiniteIntegralGenerator A T) (supportedConstantUnit A i)
    (supportedIntegralUnit i) (supportedIntegralGenerator A i) κ
    (coefficient_unit A i)).trans
      (supported_kummer_chern_realization T N A hA hT i hI κ hκ)

private theorem cartierKummer_chern_of_realization
    (κ : CartierEtaleKummerFamily l E) (c : CartierKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ)
    (hc : CartierKummerRealization l E κ c) : CartierKummerChern l E c := by
  unfold CartierEtaleKummerNormalization at hκ
  unfold CartierKummerRealization at hc
  unfold CartierKummerChern
  intro n D T i hi hI hT r hA
  obtain ⟨α, q, hq, hunit, hext⟩ := hc n r hA i hI hT
  refine ⟨(Ext.mk₀ (supportedConstantUnit (finiteTateCoefficient l E n) i)).comp
    (κ n r hA i hI hT) (zero_add 2), q, hq, ?_, ?_⟩
  · exact boundary_chern_composite (finiteTateCoefficient l E n) (l ^ (r + 1)) hA i hI
      (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) (κ n r hA i hI hT)
      (hκ n r hA i hI hT)
  · exact constantUnit_transport
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)
      (supportedConstantUnit (finiteTateCoefficient l E n) i)
      (cartierSupportedUnit l E n i) (cartierConstantComparison (finiteTateCoefficient l E n) T)
      α.hom q.hom (κ n r hA i hI hT) (c n i hI hT) hunit hext

/-- The normalized supported Cartier Kummer map for all positive coefficient levels.
The witness is simultaneous in the scheme, divisor, coefficient level and auxiliary
Kummer exponent. The uniqueness concerns the arrows, rather than auxiliary choices
of covers, resolutions, or comparison proofs.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier/
lem-amb-cartier-kummer-map.md and its proof, paragraphs 1--4; Stacks 03PL, 0A45, 099R
(blueprint: lem-amb-cartier-kummer-map).

Proof:
1. The spectral valuation of l is less than one. Thus l belongs to the maximal
ideal generated by the chosen uniformizer, and l^(n+1) vanishes modulo its
(n+1)-st power. This gives an explicit allowed exponent at every coefficient level.
2. The positive quotient ring is finite. Apply the existing ordinary supported
boundary existence-and-uniqueness theorem at every argument. Function
extensionality assembles exactly one normalized family κ.
3. The descent theorem transports this family to the published pro-etale Tate
line simultaneously for all killing exponents, and proves uniqueness of that family.
4. The naturality theorem supplies both coefficient-reduction clauses and
Cartier-preserving geometric pullback for the realized family.
5. Forgetting support in the ordinary family is precomposition by the supported
constant unit. The integral coefficient generator commutes with this unit, so
the existing relative-boundary Chern equation gives the ordinary Chern witness.
The source-unit normalization and realization equation then give its transported
Chern equation by exact Ext functoriality and Yoneda associativity.
6. Any second pair has the same ordinary family by relative-boundary normalization,
and then the same pro-etale family by unique descent. Product extensionality
proves uniqueness. The canonical arrow below retains its original unique choice.
-/
theorem cartier_kummer_map :
    (∀ n : ℕ, ∃ r : ℕ, ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) ∧
    ∃! data : CartierEtaleKummerFamily l E × CartierKummerFamily l E,
      CartierEtaleKummerNormalization l E data.1 ∧
      CartierEtaleKummerReduction l E data.1 ∧
      CartierKummerRealization l E data.1 data.2 ∧
      CartierKummerChern l E data.2 ∧
      CartierKummerBaseChange l E data.2 ∧
      CartierKummerReduction l E data.2 := by
  classical
  have hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0 :=
    fun n ↦ ⟨n, cartierCoefficient_annihilated l E n⟩
  obtain ⟨κ, hκ, hκuniq⟩ := cartierEtaleFamily_existsUnique l E
  obtain ⟨c, hc, hcuniq⟩ := cartier_kummer_descent l E hkill κ hκ
  obtain ⟨hred, hbase, hcoef⟩ := cartier_kummer_naturality l E hkill κ c hκ hc
  refine ⟨hkill, ⟨(κ, c), ⟨hκ, hred, hc,
    cartierKummer_chern_of_realization l E κ c hκ hc, hbase, hcoef⟩, ?_⟩⟩
  rintro ⟨κ', c'⟩ ⟨hκ', _, hc', _⟩
  have he : κ' = κ := hκuniq κ' hκ'
  subst κ'
  exact Prod.ext rfl (hcuniq c' hc')

/-- The canonical supported arrow, selected from its uniquely normalized system.
Its target is the published pro-etale Tate line; no new twisting object is chosen.
Source: blueprint, statement (blueprint: lem-amb-cartier-kummer-map). -/
def cartierKummerMap (n : ℕ) {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) (hT : IsUnit (l : Γ(T, ⊤))) :
    (DerivedCategory.singleFunctor _ 0).obj (cartierSupported l E n i) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (finiteTateProSheaf l E n T 1))⟦(2 : ℤ)⟧ :=
  ((cartier_kummer_map l E).2.exists.choose.2 n i hI hT).hom

end AlgebraicGeometry.Etale
