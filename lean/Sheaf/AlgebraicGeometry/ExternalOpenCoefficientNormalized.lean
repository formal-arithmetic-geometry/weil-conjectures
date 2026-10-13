/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.ScalarGlobalSectionsComparison

/-! # Normalized open-base-change isomorphism of external coefficients

Source: Stacks Project, Tags 0BED, 0096, 0097 and 01CD.
(blueprint: lem-sc-external-open-coefficient-normalized).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Restriction of the external coefficient to an open base change, normalized on
sections by the pullback units.
Source: Stacks Project, Tag 0BED, omitted canonical-cup verification; Tags 0096,
0097 and 01CD.
(blueprint: lem-sc-external-open-coefficient-normalized).

Proof: Compare restriction along j with tensor pullback by leftAdjointUniq for
restrictAdjunction and the chosen tensor-pullback adjunction. Compose this with
module_pullback_tensor on the two factors. The normalized composition comparisons
identify the first factor with the pullback of F by the new first projection,
using hfst. They identify the second factor with pullback by the new second
projection of the pullback of G by V.ι, using hsnd. Compare that last pullback
with restriction of G by the inverse leftAdjointUniq comparison for V.ι.
Tensor the two factor isomorphisms to obtain κ. For s and t, the restriction
comparison's unit equation identifies the restriction from the old open with
the j-pullback unit, and module_pullback_tensor's pure-section equation splits
that unit into the two factor units. The composition comparisons' unit equations
then compose these successive units into the new projection units. The inverse
comparison for V.ι cancels its unit against the restriction unit, which is the
identity on G(V). This gives the displayed equality. Transport along hj is the
restriction-section identification, not a new section map. Every comparison is
an isomorphism for the empty open as well; no generation by global sections is
assumed in constructing the coefficient isomorphism.
-/
theorem exists_externalOpenCoefficient_normalized
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens)
    (j : Limits.pullback f (V.ι ≫ g) ⟶ Limits.pullback f g) [IsOpenImmersion j]
    (hj : j ''ᵁ ⊤ = pullback.snd f g ⁻¹ᵁ V)
    (hfst : j ≫ pullback.fst f g = pullback.fst f (V.ι ≫ g))
    (hsnd : j ≫ pullback.snd f g = pullback.snd f (V.ι ≫ g) ≫ V.ι) :
    ∃ κ : (externalCupCoefficients f g F G).restrict j ≅
        externalCupCoefficients f (V.ι ≫ g) F (G.restrict V.ι),
      ∀ (s : Γ(F, ⊤)) (t : Γ(G, V)),
        κ.hom.app ⊤
          ((externalCupCoefficients f g F G).presheaf.map (eqToHom hj).op
            (tmulSection (M := (tensorPullback (pullback.fst f g)).obj F)
              (N := (tensorPullback (pullback.snd f g)).obj G)
              (((tensorPullback (pullback.fst f g)).obj F).presheaf.map
                (homOfLE (by simp : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ ⊤)).op
                (((Classical.choose (exists_tensorPullbackAdjunction
                  (pullback.fst f g))).unit.app F).app ⊤ s))
              (((Classical.choose (exists_tensorPullbackAdjunction
                (pullback.snd f g))).unit.app G).app V t))) =
          tmulSection (M := (tensorPullback (pullback.fst f (V.ι ≫ g))).obj F)
            (N := (tensorPullback (pullback.snd f (V.ι ≫ g))).obj (G.restrict V.ι))
            (tensorPullbackTopSection (pullback.fst f (V.ι ≫ g)) F s)
            (tensorPullbackTopSection (pullback.snd f (V.ι ≫ g)) (G.restrict V.ι)
              (G.presheaf.map (eqToHom (by simp : V.ι ''ᵁ ⊤ = V)).op t)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
