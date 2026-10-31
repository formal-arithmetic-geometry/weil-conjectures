/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Separable-closure base change is conservative on abelian etale sheaves

Source: the current blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lemma lem-kun-sep-closure-conservative (blueprint: lem-kun-sep-closure-conservative).

The coefficient category here is abelian groups, including for the unbounded derived clause.
The upstream module-sheaf version is in `Etale.Derived.Stalks.Basic`.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Every geometric point of a scheme over a field lifts to its separable-closure base
change. Pullback along that base change detects isomorphisms of abelian etale sheaves and
of arbitrary objects of their unbounded derived category.

Source: the current blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lemma lem-kun-sep-closure-conservative (blueprint: lem-kun-sep-closure-conservative).

Proof:
1. For a geometric point `s : Spec Ω ⟶ X`, extend the induced map `K → Ω` to
   `SeparableClosure K → Ω`, using algebraicity of the separable closure
   (`def-pd-separable-closure`) and `IsAlgClosed.lift`
   (`lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`). The universal property
   of the fibre product (`def-pc-fibre-product`) produces a lift of `s`.
2. For each residue-field algebraic-closure point, use Step 1 to lift it through
   the base-change projection. The natural pullback-stalk comparison
   (`lemma-openclosed-stalk-upperstar`) identifies the original stalk map with a stalk
   of the pulled-back morphism, hence with an isomorphism.
3. Geometric-stalk conservativity (`lemma-weil-pbc-geometric-stalk-conservative`)
   makes the original sheaf morphism invertible. Functors preserve isomorphisms,
   giving the converse.
4. Exact inverse image commutes naturally with each cohomology functor by
   `Functor.mapDerivedCategoryHomologyFunctorIso`. Thus invertibility after derived
   pullback makes each pulled-back cohomology map invertible. Step 3 makes every
   original cohomology map invertible, and `DerivedCategory.isIso_iff` makes the
   original derived morphism invertible. The converse is functoriality; no boundedness
   is imposed. -/
theorem sepClosureBaseChange_conservative_abelian
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ t : Spec (.of Ω) ⟶
          pullback p (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))),
        t ≫ pullback.fst p
          (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))) = s) ∧
    (∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G),
      IsIso φ ↔ IsIso ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst p
          (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))))).map φ)) ∧
    (∀ (A B : _root_.DerivedCategory
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (α : A ⟶ B),
      IsIso α ↔ IsIso ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst p
          (Spec.map (CommRingCat.ofHom
            (algebraMap K (SeparableClosure K)))))).mapDerivedCategory.map α)) := by
  let q := pullback.fst p
    (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))))
  have hlift (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
      ∃ t, t ≫ q = s := by
    let := (Spec.preimage (s ≫ p)).hom.toAlgebra
    let ψ : SeparableClosure K →ₐ[K] Ω := IsAlgClosed.lift
    refine ⟨pullback.lift s (Spec.map (CommRingCat.ofHom ψ.toRingHom)) ?_, ?_⟩
    · rw [← Spec.map_comp, ← Spec.map_preimage (s ≫ p)]
      congr 1
      ext x
      exact (ψ.commutes x).symm
    · exact pullback.lift_fst _ _ _
  have hsheaf (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G) :
      IsIso φ ↔ IsIso ((upperStar AddCommGrpCat.{u + 1} q).map φ) := by
    refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
    apply Scheme.isIso_of_isIso_sheafFiber_map φ
    intro x
    obtain ⟨t, ht⟩ := hlift _ (X.algClosurePoint x)
    dsimp only [Scheme.uliftPointSmallEtale]
    rw [← ht]
    apply (NatIso.isIso_map_iff (upperStarCompUliftSheafFiberIso
      AddCommGrpCat.{u + 1} q t) φ).1
    exact Functor.map_isIso
      (((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber (A := AddCommGrpCat.{u + 1}))
      ((upperStar AddCommGrpCat.{u + 1} q).map φ)
  refine ⟨hlift, hsheaf, ?_⟩
  intro A B α
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  apply (hsheaf _ _ _).2
  exact (NatIso.isIso_map_iff
    ((upperStar AddCommGrpCat.{u + 1} q).mapDerivedCategoryHomologyFunctorIso n) α).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      ((upperStar AddCommGrpCat.{u + 1} q).mapDerivedCategory.map α))

end AlgebraicGeometry.Etale
