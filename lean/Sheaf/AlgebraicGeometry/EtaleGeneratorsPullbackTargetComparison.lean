/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSourceComparison
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections

/-! # EtaleGeneratorsPullbackTargetComparison

Source: Stacks Project, Tags 0097 and 040E.
(blueprint: lem-sc-etale-generators-pullback-target-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- An explicit comparison factor in the generator pullback construction.
Source: Stacks Project, Tag 0097. (blueprint: lem-sc-etale-generators-pullback-target-comparison) -/
noncomputable def etaleGeneratorsPullbackTargetIso {X Y : Scheme.{u}} (f : Y ⟶ X) (W : X.Etale)
    (L : X.Modules) :
    (pullback (Limits.pullback.fst W.hom f)).obj ((pullback W.hom).obj L) ≅
      (pullback (Limits.pullback.snd W.hom f)).obj ((tensorPullback f).obj L) :=
  (pullbackComp (Limits.pullback.fst W.hom f) W.hom).app L ≪≫
    (pullbackCongr Limits.pullback.condition).app L ≪≫
    ((pullbackComp (Limits.pullback.snd W.hom f) f).app L).symm ≪≫
    (pullback (Limits.pullback.snd W.hom f)).mapIso
      (((Classical.choice (nonempty_tensorPullbackAdjunction f)).leftAdjointUniq
        (pullbackPushforwardAdjunction f)).app L).symm

/-- The target comparison commutes with etale restriction.
Source: Stacks Project, Tag 0097, Lemma 6.26.3; Tag 040E, Lemma 21.6.1.
(blueprint: lem-sc-etale-generators-pullback-target-comparison)

Proof: Write B_U(M) as the comparison p_U*U*M to q_U*f*M, followed by q_U* of the inverse
tensor/abstract pullback comparison. Naturality of c(j,q_W;q_V) with respect to this last
inverse moves that factor to q_V*. The remaining comparison identity is the associativity
coherence of the module pullback pseudofunctor: both composites identify j*p_W*W*M with q_V*f*M
through the same morphism to X. Use j followed by p_W equals p_V followed by i, i followed by W
equals V, and j followed by q_W equals q_V. Apply the three-fold composition coherence on each
path and cancel the common comparison for the total morphism. This gives K(M).inv followed by
j*B_W(M) and the q comparison equal to p_V* of c(i,W;V).hom followed by B_V(M). The argument is
natural for every module M, including the zero module, and does not use any section or
invertibility.
-/
theorem etaleGeneratorsPullbackTarget_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    {V W : X.Etale} (i : V ⟶ W) :
    (etaleGeneratorsPullbackSquareIso f i ((pullback W.hom).obj L)).inv ≫
      (pullback ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).map
        (etaleGeneratorsPullbackTargetIso f W L).hom ≫ (pullbackCompOfEq
        ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
      (Limits.pullback.snd W.hom f) (Limits.pullback.snd V.hom f)
      ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).w ((tensorPullback f).obj L)).hom =
      (pullback (Limits.pullback.fst V.hom f)).map (pullbackCompOfEq i.left W.hom V.hom i.w
        (L)).hom ≫
        (etaleGeneratorsPullbackTargetIso f V L).hom := by
  sorry

end AlgebraicGeometry.Scheme.Modules
