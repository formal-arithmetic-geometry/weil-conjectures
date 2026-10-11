/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.FieldTheory.IsSepClosed

/-!
# The morphism from the Hilbert scheme to the degree component of the Picard scheme

Source: Stacks Project, Tag 0BA0 (4) and its proof, and Remark 0B9J
(blueprint: lem-sc-hilb-to-pic-morphism).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The universal divisor defines the Hilbert-to-Picard morphism.
Source: Stacks Project, Tag 0BA0 (4), proof paragraph 2; Remark 0B9J
(blueprint: lem-sc-hilb-to-pic-morphism).

Proof: (1) Base changing the smooth projective curve gives a smooth relative curve, flat,
proper and of finite presentation (lem-sc-curve-base-change-relative-dimension-one,
lem-pc-smooth-flat, lem-pc-projective-proper, lem-pc-proper-base-change).
(2) The universal Hilbert subscheme is finite locally free of degree d; the Cartier criterion
makes it a relative effective Cartier divisor (lem-pc-cartier-criterion), and its dual ideal
is invertible (lem-pc-divisor-line-bundle-invertible).
(3) At every residue-field point, its base change is a degree d divisor and the line bundle
restricts to the dual ideal of that divisor (lem-pc-recd-pullback).
(4) Its degree is the length of the divisor, hence d (lem-pc-dim-base-change,
lem-pc-degree-base-change); isomorphic modules have the same Euler characteristic.
(5) Send its Picard class through sheafification and the representing equivalence to obtain
 gamma (lem-pc-yoneda). Membership in the degree component follows from step (4).
(6) For a field-valued point, naturality of the Hilbert representing equivalence identifies
its divisor with the pullback of the universal divisor (lem-pc-yoneda,
lem-pc-recd-pullback). (7) Naturality of Picard sheafification and of the representing
equivalence identifies the composite with the class of that divisor's line bundle.

`Pic^d_{C/k}` is the source's `AlgebraicGeometry.picardFunctorDegree f d` (the fppf
sheafification of the degree-`d` subfunctor `AlgebraicGeometry.picardSubfunctorDegree f d` of
the Picard presheaf), and the class of a degree-`d` invertible module in it is its image under
`toSheafify`. The Picard classes `L` and `LK` are tied to the actual dual ideal modules by
isomorphisms; they are not arbitrary representatives. -/
theorem exists_hilbertToPicardMorphism {k : Type u} [Field k] [IsSepClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [f.IsSmoothProjectiveCurve]
    [GeometricallyIntegral f] (d : ℕ)
    (H P : Over (Spec (.of k))) (eH : (hilbertPresheaf f d).RepresentableBy H)
    (eP : (picardFunctorDegree f d).obj.RepresentableBy P) :
    let D := (eH.homEquiv (𝟙 H)).1
    D.IsRelativeEffectiveCartier (pullback.snd f H.hom) ∧
      D.toModulesᵛ.IsInvertible ∧
      ∃ L : (pullback f H.hom).Pic,
        Nonempty ((fromSkeleton _).obj L.val ≅ D.toModulesᵛ) ∧
        (∀ t : H.left, picardPresheafDegree f L t = (d : ℤ)) ∧
        ∃ (hL : L ∈ (picardSubfunctorDegree f d).obj (op H)) (γ : H ⟶ P),
          eP.homEquiv γ = (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree f d).toFunctor).app (op H) ⟨L, hL⟩ ∧
          ∀ (K : Type u) [Field K] [Algebra k K]
            (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ H),
            let T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            let DK := (eH.homEquiv x).1
            DK.IsInvertible ∧ DK.toModulesᵛ.IsInvertible ∧
              ∃ (LK : (pullback f T.hom).Pic)
                (hLK : LK ∈ (picardSubfunctorDegree f d).obj (op T)),
                Nonempty ((fromSkeleton _).obj LK.val ≅ DK.toModulesᵛ) ∧
                eP.homEquiv (x ≫ γ) = (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
                  (picardSubfunctorDegree f d).toFunctor).app (op T) ⟨LK, hLK⟩ := by
  sorry

end AlgebraicGeometry
