/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import Mathlib.FieldTheory.Galois.Profinite
import Sheaf.AlgebraicGeometry.FundamentalGroup.FieldGaloisFibreIdentification
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence

/-! # Fully faithful field points and the fundamental group

Source: Stacks Project, `pione.tex`, Tags 0BQM, 0BNE, 0BQ9 and 0BN6
(blueprint: lem-dl-a1-field-point-full-faithful-galois-map).

The fundamental group uses its existing finite-etale model `Aut (fiber _)`, identified
with the FLC model by the recorded fibre-compatible equivalence. The induced map on
these automorphism groups is whiskering by pullback followed by conjugation by
`pullbackFiberIso`. This formula works without shrinking the automorphism groups.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- A fully faithful field point gives a continuous surjection from its absolute Galois
 group, with the canonical action, separable-point comparison and section bijections.
Source: Stacks Project, `pione.tex`, Tags 0BQM, 0BNE, 0BQ9 and 0BN6
(blueprint: lem-dl-a1-field-point-full-faithful-galois-map).

Proof: (1) `lem-dl-a1-field-galois-fibre-identification` gives the unique extensions,
the profinite field group, its topological identification j, and equivariant point
bijections. The pullback universal property identifies lifts to P with lifts to P_K;
invert the field comparison to obtain b. Its equivariance identifies the subgroups
acting trivially on the two sets. (2) `lem-galois-pi1-functoriality` identifies the
induced map with whiskering followed by conjugation through `pullbackFiberIso`.
Compose with j to obtain q. On lifts this is precomposition by Spec of the unique
extension. Naturality and the homomorphism law follow from postcomposition and the
contravariance of Spec. Continuity follows by composition; `thm-galois-fundamental`
gives profiniteness of the target. (3) Under the equivalences of
`thm-galois-fundamental`, fully faithful cover pullback becomes fully faithful
restriction of finite continuous actions. The criterion
`lem-dl-a1-profinite-restriction-full-faithful` gives surjectivity of q.
(4) Full faithfulness applied to X and P gives the section restriction bijection e.
The identity cover has singleton fibre, so its equivariant maps to the fibre of P_K
are precisely fixed points. The field comparison gives d, with the stated evaluation
formula. These arguments include empty covers and imperfect fields. -/
theorem field_point_full_faithful_galois_map
    {X : Scheme.{u}} [ConnectedSpace X]
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosed Ks] [Algebra.IsSeparable K Ks]
    [Algebra Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic Ks Ω]
    [Algebra K Ω] [IsScalarTower K Ks Ω]
    (a : Spec (.of K) ⟶ X)
    (hfull : ∀ P Q : X.FiniteEtale,
      Function.Bijective (fun f : P ⟶ Q ↦ (pullback a).map f)) :
    ∃ (j : Gal(Ks/K) ≃ₜ* Aut (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))))
      (q : Gal(Ks/K) →* Aut (fiber (pointOfAlgebra Ω a))),
      (∀ σ : Gal(Ks/K), ∃! τ : Gal(Ω/K),
        ∀ x : Ks, τ (algebraMap Ks Ω x) = algebraMap Ks Ω (σ x)) ∧
      (∀ (σ : Gal(Ks/K)) (τ : Gal(Ω/K)),
        (∀ x : Ks, τ (algebraMap Ks Ω x) = algebraMap Ks Ω (σ x)) →
        (∀ (Q : (Spec (.of K)).FiniteEtale)
          (t : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj Q),
          ((j σ).hom.app Q t).left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t.left) ∧
        (∀ (P : X.FiniteEtale) (t : (fiber (pointOfAlgebra Ω a)).obj P),
          ((q σ).hom.app P t).left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t.left)) ∧
      (∀ σ : Gal(Ks/K),
        q σ = (pullbackFiberIso a (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).conjAut
          (Functor.mapAut _ ((Functor.whiskeringLeft _ _ _).obj (pullback a)) (j σ))) ∧
      Continuous q ∧ Function.Surjective q ∧
      CompactSpace Gal(Ks/K) ∧ T2Space Gal(Ks/K) ∧ TotallyDisconnectedSpace Gal(Ks/K) ∧
      CompactSpace (Aut (fiber (pointOfAlgebra Ω a))) ∧
      T2Space (Aut (fiber (pointOfAlgebra Ω a))) ∧
      TotallyDisconnectedSpace (Aut (fiber (pointOfAlgebra Ω a))) ∧
      (∃ b : ∀ P : X.FiniteEtale, (fiber (pointOfAlgebra Ω a)).obj P ≃
          (fiber (pointOfAlgebra Ks (𝟙 (Spec (.of K))))).obj ((pullback a).obj P),
        (∀ (P : X.FiniteEtale) (t : (fiber (pointOfAlgebra Ω a)).obj P),
          Spec.map (CommRingCat.ofHom (algebraMap Ks Ω)) ≫
            (b P t).left ≫ Limits.pullback.fst P.obj.hom a = t.left) ∧
        (∀ (σ : Gal(Ks/K)) (P : X.FiniteEtale)
          (t : (fiber (pointOfAlgebra Ω a)).obj P),
          b P ((q σ).hom.app P t) =
            (galoisToAut (𝟙 (Spec (.of K))) σ).hom.app ((pullback a).obj P) (b P t)) ∧
        (∀ (H : Subgroup Gal(Ks/K)) (P : X.FiniteEtale),
          (∀ (σ : H) (t : (fiber (pointOfAlgebra Ω a)).obj P),
            (q σ).hom.app P t = t) ↔
          (∀ (σ : H)
            (t : (fiber (pointOfAlgebra Ks (𝟙 (Spec (.of K))))).obj ((pullback a).obj P)),
            (galoisToAut (𝟙 (Spec (.of K))) σ).hom.app ((pullback a).obj P) t = t))) ∧
      (∀ P : X.FiniteEtale,
        ∃ (e : {v : X ⟶ P.obj.left // v ≫ P.obj.hom = 𝟙 X} ≃
            {v : Spec (.of K) ⟶ ((pullback a).obj P).obj.left //
              v ≫ ((pullback a).obj P).obj.hom = 𝟙 (Spec (.of K))})
          (d : {v : Spec (.of K) ⟶ ((pullback a).obj P).obj.left //
              v ≫ ((pullback a).obj P).obj.hom = 𝟙 (Spec (.of K))} ≃
            {t : (fiber (pointOfAlgebra Ω a)).obj P //
              ∀ σ : Gal(Ks/K), (q σ).hom.app P t = t}),
          (∀ v, (e v).val ≫ Limits.pullback.fst P.obj.hom a = a ≫ v.val) ∧
          (∀ v, (d v).val.left = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
            v.val ≫ Limits.pullback.fst P.obj.hom a)) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
