/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.FieldTheory.GaloisUnitsCohomology
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluation
import Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluationBijective

/-!
# The geometric stalk of units and its Galois action

Source: Stacks Project, Example 03QV (2), and Tag 03QU.
(blueprint: lem-sc-etale-units-stalk-galois).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- The stalk of the units sheaf is separable-closure units, with its natural action.

Source: Stacks Project, Example 03QV (2), and Tag 03QU.
(blueprint: lem-sc-etale-units-stalk-galois).

Proof: Use the separable closure inside the algebraic closure as geometric point.
Any germ of a unit has a representative on an etale neighbourhood. Shrink to the connected
component at the given lift, which is the spectrum of a finite separable field extension.
Evaluation of its functions at that lift gives a unit of the separable closure. Evaluation
commutes with restriction, so this defines a map from the stalk. Conversely, any nonzero
separable algebraic element belongs to a finite separable field extension, so it and its
inverse define a unit on that neighbourhood. Two representatives with equal values agree
after passing to their common finite separable compositum. These facts prove bijectivity.
Multiplication of units becomes addition and the canonical universe lift/down maps
preserve it, giving the additive equivalence `c`.
Replacing a lift by its composite with an automorphism of the algebraic closure changes
its evaluated value by that automorphism. Since the evaluated value lies in the separable
closure and the automorphism restricts to `g`, this is exactly the action of `g` on units.
This proves the displayed formula on every germ. The argument applies to imperfect fields:
only separable elements occur in etale neighbourhoods, not all algebraic-closure units. -/
theorem exists_etale_units_stalk_galois_equiv (K : Type u) [Field K] :
    let Ks := SeparableClosure K
    let Ω := AlgebraicClosure K
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∃ c : (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf ≃+ Field.galoisUnitsTopRep K,
      ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (X : S.Etale) (x x' : p.fiber.obj X)
        (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
        (z : S.gmSheaf.obj.obj (op X)),
        c (p.toPresheafFiber X x' S.gmSheaf.obj z) =
          (Field.galoisUnitsTopRep K).ρ g (c (p.toPresheafFiber X x S.gmSheaf.obj z)) :=
  by
    dsimp only
    obtain ⟨f, hf⟩ := exists_etale_units_stalk_evaluation K
    let c := AddEquiv.ofBijective f (etale_units_stalk_evaluation_bijective K f hf)
    refine ⟨c, ?_⟩
    intro g τ hτ X x x' hx z
    apply Additive.toMul.injective
    apply Units.ext
    apply (algebraMap (SeparableClosure K) (AlgebraicClosure K)).injective
    change algebraMap (SeparableClosure K) (AlgebraicClosure K)
        (Additive.toMul (f (_)) : (SeparableClosure K)ˣ) = _
    rw [hf X x' z]
    let p := pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
    have hτ' := congrArg (fun φ : SeparableClosure K →+* AlgebraicClosure K ↦
      φ (Additive.toMul (f (p.toPresheafFiber X x (Spec (.of K)).gmSheaf.obj z)) :
        (SeparableClosure K)ˣ)) hτ
    change _ = algebraMap (SeparableClosure K) (AlgebraicClosure K)
      (g (Additive.toMul (f (_)) : (SeparableClosure K)ˣ))
    dsimp only [RingHom.comp_apply] at hτ'
    refine Eq.trans ?_ hτ'.symm
    dsimp only [p]
    rw [hf X x z]
    rw [hx, Hom.comp_appTop]
    have hn := ΓSpecIso_naturality (CommRingCat.ofHom τ.toRingHom)
    exact congrArg (fun φ ↦ φ (x.left.appTop
      ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)))) hn

end AlgebraicGeometry.Scheme
