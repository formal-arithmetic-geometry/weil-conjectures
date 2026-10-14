module

public import Sheaf.AlgebraicGeometry.OverlapConjugateRestriction
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section
attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Adjunction.leftAdjointUniq
  Scheme.Modules.pullbackComp pullbackCompOfEq Scheme.Modules.pullbackCongr
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Factorization of one canonical chart comparison through the stage model.
Source: Stacks Project, Tags 0095, 0096 and 0097 (composition of inverse images and
uniqueness of their adjunction comparisons); Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-model-chart-factorization).

Proof: Expand the direct and stage model comparisons. The tensor composition
comparison followed by the comparisons from tensor to abstract pullback equals
abstract pullback composition followed by the comparison for the composite.
Indeed, apply the conjugation equivalence for the composite adjunctions: both
maps correspond to pushforward composition followed by congruence along h₀.
Whisker this equality by pullback along z. Use naturality to move the comparison
for q₀ through the composition isomorphisms, and use the pullback composition
pentagon on the triples (z, p₀, q₀), (l, d, q₀), and the subsequent map r₀.
The equation hz identifies their composite routes. The equations hk, hl, htr,
hvu, hδ and hzv identify both exterior routes to A. The remaining composition
comparisons cancel in inverse pairs, giving the displayed factorization.
Only invertible canonical comparisons are used. The argument also works for
identity maps, zero module sheaves and empty schemes; no faithfulness is needed. -/
theorem overlap_model_chart_factorization
    {H₀ Hₖ H K L A B C D : Scheme.{u}}
    (q₀ : Hₖ ⟶ H₀) (p₀ : H ⟶ Hₖ) (t₀ : H ⟶ H₀) (h₀ : p₀ ≫ q₀ = t₀)
    (r₀ : H₀ ⟶ A) (d : K ⟶ Hₖ) (s : K ⟶ B) (u : B ⟶ A)
    (hk : (d ≫ q₀) ≫ r₀ = s ≫ u)
    (v : H ⟶ C) (u' : C ⟶ A) (k : H ⟶ A)
    (htr : t₀ ≫ r₀ = k) (hvu : v ≫ u' = k)
    (z : L ⟶ H) (l : L ⟶ K) (hz : z ≫ p₀ = l ≫ d)
    (r : L ⟶ D) (w : D ⟶ B) (δ : D ⟶ C)
    (hl : l ≫ s = r ≫ w) (hδ : δ ≫ u' = w ≫ u) (hzv : z ≫ v = r ≫ δ)
    (N : A.Modules) :
    let F := (Scheme.Modules.pullback r₀).obj N
    let σ := Scheme.Modules.tensorPullbackCompositionIso p₀ q₀ t₀ h₀
    let E := Functor.isoWhiskerRight (overlapAdjunctionComparison p₀)
        (Scheme.Modules.pullback z) ≪≫
      Scheme.Modules.pullbackComp z p₀ ≪≫ Scheme.Modules.pullbackCongr hz ≪≫
      (Scheme.Modules.pullbackComp l d).symm
    let τ := overlapDirectModelComparison t₀ r₀ k v u' htr hvu N
    let ξ := (Scheme.Modules.pullback z).mapIso τ ≪≫
      pullbackCompOfEq z v (r ≫ δ) hzv ((Scheme.Modules.pullback u').obj N) ≪≫
      ((Scheme.Modules.pullbackComp r δ).app _).symm ≪≫
      (Scheme.Modules.pullback r).mapIso
        ((Scheme.Modules.pullbackComp w u).app N ≪≫
          (Scheme.Modules.pullbackCongr hδ.symm).app N ≪≫
          ((Scheme.Modules.pullbackComp δ u').app N).symm).symm
    let s' := overlapStageModelComparison d q₀ r₀ s u hk N
    let β := pullbackCompOfEq l s (r ≫ w) hl ((Scheme.Modules.pullback u).obj N) ≪≫
      ((Scheme.Modules.pullbackComp r w).app _).symm
    ξ = (Scheme.Modules.pullback z).mapIso (σ.app F) ≪≫
      E.app ((Scheme.Modules.tensorPullback q₀).obj F) ≪≫
      (Scheme.Modules.pullback l).mapIso s' ≪≫ β := by sorry

end
end AlgebraicGeometry
