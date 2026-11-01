/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerRealizationExistence

import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! # Descent and exponent independence of normalized Cartier boundaries

Source: blueprint main-20261015, lem-amb-cartier-kummer-map.proof.md,
final paragraph, and the expanded DAG proof, steps 8--11 and 13.
(blueprint: lem-amb-cartier-kummer-descent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 512
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem supported_unit_epi (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    Epi (supportedConstantUnit A i) := by
  have h := shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
    i.openComplement.ι i (ordinaryFiniteConstant A T) i.range_eq_compl_range_openComplement_ι
  have hu : Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
      (ordinaryFiniteConstant A T)) := h.epi_g
  unfold supportedConstantUnit
  rw [Adjunction.homEquiv_unit]
  have hi : IsIso ((lowerStar (ModuleCat.{u + 1} A) i).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
        (ModuleCat.of A A)).hom) := inferInstance
  exact inferInstance

universe uC vC wC

private theorem ext_precomp_injective {C : Type uC} [Category.{vC} C]
    [Abelian C] [HasExt.{wC} C]
    {X Y Z : C} (e : X ≅ Y) {x y : Ext Y Z 2}
    (h : (Ext.mk₀ e.hom).comp x (zero_add 2) =
      (Ext.mk₀ e.hom).comp y (zero_add 2)) : x = y := by
  have hh := congrArg (fun z ↦ (Ext.mk₀ e.inv).comp z (zero_add 2)) h
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp] using hh

attribute [local irreducible] ProEtale.comparisonUpperStar

private theorem mapped_supported_unit_epi (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    Epi ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map
      (supportedConstantUnit A i)) := by
  let := supported_unit_epi A i
  let := Functor.preservesEpimorphisms_of_adjunction
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T)
  exact Functor.map_epi _ _

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem realization_unique
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E) (c c' : CartierKummerFamily l E)
    (hc : CartierKummerRealization l E κ c)
    (hc' : CartierKummerRealization l E κ c') : c' = c := by
  unfold CartierKummerRealization at hc hc'
  funext n D T i hi hI hT
  obtain ⟨r, hr⟩ := hkill n
  obtain ⟨α, q, hq, hα, he⟩ := hc n r hr i hI hT
  obtain ⟨α', q', hq', hα', he'⟩ := hc' n r hr i hI hT
  have hqq : q' = q :=
    (WeilConjectures.adicPurityRootComparison_existsUnique l E n T hT
      r hr 1).unique hq' hq
  let := mapped_supported_unit_epi (finiteTateCoefficient l E n) i
  have hαα : α'.hom = α.hom := (cancel_epi _).1 (hα'.trans hα.symm)
  subst q'
  have hαiso : α' = α := Iso.ext hαα
  subst α'
  exact ext_precomp_injective α (he'.trans he.symm)

/-- A normalized ordinary boundary family descends to a unique family in the
published pro-etale Tate lines, independently of the annihilating exponent.

Source: blueprint main-20261015, lem-amb-cartier-kummer-map.proof.md, final paragraph;
expanded proof steps 8--11 and 13 (blueprint: lem-amb-cartier-kummer-descent).

Proof: At each coefficient level choose an annihilating exponent. The canonical
closed direct-image mate is invertible by the exact site comparison and the
open-closed quotient presentation. Its composite with the ordinary quotient is
constant comparison followed by the pro-etale quotient. Transport the ordinary
Ext class by this source isomorphism and by the root-projection-normalized Tate
isomorphism supplied by finite_tate_site_descent. This defines an arrow at that
level. For two exponents compare both with their maximum. The map of Kummer
sequences has identity on the right-hand G_m and power l^(s-r) in the middle
and on roots. Boundary naturality identifies the two relative classes; exact
coefficient forgetting and support Hom preserve the equation. The normalized
scalar adjunction identifies successive extension with direct extension.
The root projections satisfy p_r=p_(s,r)p_s, so the Tate comparisons carry
this equation to equality of the two transported arrows. Thus one arrow realizes
every allowed exponent. For uniqueness the quotient unit is epic, so its
normalization fixes the source comparison. The Tate comparison is fixed on local
pure root tensors: refine a root-trivializing etale cover by pro-etale covers
where roots lift compatibly to the tower, and use the tensor sheafification
universal property. The realization equation, cancelled against the invertible
source comparison, now determines the arrow at every argument. Function
extensionality proves uniqueness of the simultaneous family. Empty schemes and
empty divisors satisfy the same quotient and tensor calculations. -/
theorem cartier_kummer_descent
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ) :
    ∃! c : CartierKummerFamily l E, CartierKummerRealization l E κ c := by
  obtain ⟨c, hc⟩ := cartier_kummer_realization_exists l E hkill κ hκ
  exact ⟨c, hc, fun c' hc' ↦ realization_unique l E hkill κ c c' hc hc'⟩

end AlgebraicGeometry.Etale
