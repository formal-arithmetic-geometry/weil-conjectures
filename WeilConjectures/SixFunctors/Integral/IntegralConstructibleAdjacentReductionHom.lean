/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import all WeilConjectures.SixFunctors.Integral.IntegralConstructibleReductionHom
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor

/-! # Reconstruction from adjacent compatible finite reductions -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _
attribute [local irreducible] HasDerivedCategory.standard
  scalarReductionDerivedExistence completedIntegralCoefficientSheafUnrestricted
  normalizedDVRResCompletedComp

/-- Adjacent compatible finite reductions reconstruct a unique constructible morphism.
Source: the mapping-limit argument for lem-coef-integral-finite-extension and
Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-sf-integral-constructible-adjacent-reduction-hom).

Proof: the intrinsic reduction cone of the target is a homotopy limit by its
Roos triangle. Its shifted Hom groups from the source are finite, so the Milnor
map is bijective. Transpose each finite map by scalar adjunction. The adjacent
compatibility equations say exactly that these transposes belong to the inverse
limit of Hom groups. The Milnor bijection lifts that family uniquely. Naturality
of the scalar-adjunction unit identifies its finite reductions with the given
maps. Only adjacent transitions enter a sequential inverse limit, so no
compatibility assumption for nonadjacent quotients is needed. -/
theorem integralConstructibleAdjacentReductionHom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (K M : sfIntegralConstructibleCategory l E X)
    (f : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj K.obj ⟶
      (scalarReductionDerivedExtension l E X n).obj M.obj)
    (hf : ∀ n : ℕ,
      f (n + 1) ≫ normalizedDVRReductionTransition l E X D hl n.le_succ M.obj =
        normalizedDVRReductionTransition l E X D hl n.le_succ K.obj ≫
          (normalizedDVRRes l E X n.le_succ).map (f n)) :
    ∃! g : K.obj ⟶ M.obj,
      ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).map g = f n := by
  obtain ⟨hp, δ, hδ⟩ := M.property.1
  let := hp
  have hc : IsHomotopyLimit (sfIntegralReductionCone l E X M.obj) := by
    apply roos_isHomotopyLimit (δ := δ)
    change IsDerivedLimitTriangle
      (K := fun n ↦ (sfDerivedReductionRestricted l E X n).obj M.obj)
      (fun n ↦ (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op)
      M.obj (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app M.obj)) δ
    simpa only [sfIntegralReductionTower,
      Functor.ofOpSequence_map_homOfLE_succ] using hδ
  have (n : ℕ) : Finite
      (K.obj⟦(1 : ℤ)⟧ ⟶ (sfIntegralReductionTower l E X M.obj).obj (op n)) :=
    reduction_hom_finite D l hl E X K M n
  have hb := hc.bijective_milnorMap K.obj
  let a (n : ℕ) := (normalizedDVRIntegralAdjunction l E X n).homEquiv K.obj _ (f n)
  have ha (n : ℕ) : a (n + 1) ≫
      (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op = a n := by
    have ht : (sfIntegralReductionTower l E X M.obj).map (homOfLE n.le_succ).op =
        (sfDerivedReductionTransition l E X n).app M.obj :=
      Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [ht, intrinsic_transition_eq D l hl E X M.obj n]
    exact adjoint_compatible
      (normalizedDVRIntegralAdjunction l E X (n + 1))
      (normalizedDVRIntegralAdjunction l E X n)
      (normalizedDVRRes l E X n.le_succ)
      (normalizedDVRResCompletedComp.{u, u, u} l E X D hl n.le_succ)
      (f (n + 1)) (f n) (hf n)
  obtain ⟨g, hg⟩ := hb.surjective ⟨a, ha⟩
  change K.obj ⟶ M.obj at g
  have hgn (n : ℕ) : (scalarReductionDerivedExtension.{u, u} l E X n).map g = f n := by
    apply ((normalizedDVRIntegralAdjunction l E X n).homEquiv _ _).injective
    have hn := congrArg (fun z ↦ z.val n) hg
    change g ≫ (sfDerivedReductionUnit l E X n).app M.obj = a n at hn
    rw [Adjunction.homEquiv_unit]
    have hu := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g
    exact hu.symm.trans hn
  refine ⟨g, hgn, ?_⟩
  intro g' hg'
  apply hb.injective
  apply Subtype.ext
  funext n
  change g' ≫ (sfDerivedReductionUnit l E X n).app M.obj =
    g ≫ (sfDerivedReductionUnit l E X n).app M.obj
  change g' ≫ (normalizedDVRIntegralAdjunction l E X n).unit.app M.obj =
    g ≫ (normalizedDVRIntegralAdjunction l E X n).unit.app M.obj
  have hu := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g
  have hu' := (normalizedDVRIntegralAdjunction l E X n).unit.naturality g'
  dsimp only [Functor.id_map, Functor.comp_map] at hu hu'
  rw [hu', hu, hg' n, hgn n]

end WeilConjectures
