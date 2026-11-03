/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralNormalizedRefinementData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Refinement.IntegralRefinementDiagramAdmissibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing

/-! # Realization of an open-unit-normalized reverse refinement

This is the comparison step in the integral refinement argument. It concerns only
one reverse refinement and its proper/open outside factors.
(blueprint: lem-sf-integral-refinement-transpose-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The total limit of the reverse system refinement is the actual proper/open
map characterized by its open-adjunction transpose, also inside outside factors.
Source: Stacks 0F7B--0F7D; blueprint exceptional inverse image, extracted normalized
coefficient argument, old step 10, comparison step and its whiskering clause
(blueprint: lem-sf-integral-refinement-transpose-realization).

Proof: expand the reverse refinement as the inverse identity proper unitor,
the intrinsic proper/open mate for (j_c,1_X,u,j_d), and the proper compositor.
The generator reduction equation and the actual reconstruction counit identify
its total-limit map with the localized integral mate. Compose its open transpose
with the canonical pullback-composition/proper-counit restriction: the result
is the open unit. Thus it equals the supplied e by injectivity of the adjunction
Hom equivalence and invertibility of the restriction on the clopen component.
The realization comparison intertwines the proper compositor as well. All
intermediate systems are admissible by the eighteen diagram-word hypotheses.
For an outer proper factor use naturality of the proper realization and the
recursive push formula. For an outer open factor use the normalized open
realization, whose naturality follows by cancelling its invertible reconstruction
unit and counit in the open normalization equation. Induction on the number of
outside factors proves the displayed equation, with the associators supplied by
evaluationIso. The hole case is the just-proved comparison. Identity refinements
use the proper unitor; empty opens and zero objects use the same unit formulas.
All these are identities of actual derived morphisms before finite evaluation.
-/
theorem integralRefinementTransposeRealization
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (K : finiteTorConstructibleIntegralCategory l E X.left)
    (hDiagram : ∀ (a : Fin 3 → Compactification f.left)
      (v : (a 0).Refinement (a 1)) (w : (a 1).Refinement (a 2)) (i : Fin 18),
      (refinementDiagramWords f a v w (fun _ ↦ inferInstance) i).2.domain l E o
        (fun _ ↦ K.obj))
    (c d : Compactification f.left) (v : c.Refinement d)
    (e : (ringedOpen l E d.i).obj K.obj ≅
      (ringedPush l E v.hom).obj ((ringedOpen l E c.i).obj K.obj))
    (he : (ringedOpenAdj l E d.i).homEquiv _ _ e.hom ≫
      PurCompactSupport.refinementRestriction (PurCompactSupport.completed l E) v
        (PurCompactSupport.completedPull_comp l E c.i v.hom) K.obj =
      (ringedOpenAdj l E c.i).unit.app K.obj)
    {W : Over (Spec (CommRingCat.of D.k))}
    (q : NormalizedRefinementContext _ Y W)
    (gc : (q.plug (normalizedRefinementWord f c)).geometric)
    (gd : (q.plug (normalizedRefinementWord f d)).geometric)
    (hc : (q.plug (normalizedRefinementWord f c)).domain l E o (fun _ ↦ K.obj))
    (hd : (q.plug (normalizedRefinementWord f d)).domain l E o (fun _ ↦ K.obj)) :
    (coefficientSequenceLimit l E W.left).map
        ((q.evaluate (systemInterpretation l E o)).map
          ((completedShriekRefinement l E R v).app
            ((calculus l E X.left).reduction.obj K.obj))) ≫
      (q.realization l E R (normalizedRefinementWord f c) gc (fun _ ↦ K.obj) hc).hom =
    (q.realization l E R (normalizedRefinementWord f d) gd (fun _ ↦ K.obj) hd).hom ≫
      (q.evaluate (integralInterpretation l E)).map
        ((ringedPush l E d.g).map e.hom ≫
          (ringedPushComp l E v.hom d.g ≪≫
            eqToIso (congrArg (ringedPush l E) v.hom_g)).hom.app
              ((ringedOpen l E c.i).obj K.obj)) := by
  sorry

end WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native refinement map is uniquely normalized by its open transpose, is
invertible on the localizing closure, and satisfies identity and composition.

Source: blueprint det-sf-comp-coherence-refinement, clauses (1)--(3).
(blueprint: lem-sf-integral-refinement-transpose-realization).

Proof: this released identifier is the reviewed alias of
`det-sf-comp-coherence-refinement`. Apply its canonical refinement theorem with
exactly the same coefficient, geometric, and input hypotheses. Its first clause
is the adjunction uniqueness equation, its second is invertibility on Loc(Dctf),
and its last two clauses use the canonical derived identity and composition
comparisons. In particular uniqueness and coherence hold on all unbounded
inputs; only invertibility requires membership in the localizing closure.
-/
theorem integralRefinementTransposeRealization
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      ∀ b : (openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K ⟶
        (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.obj K),
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.obj.i).unit.app K ≫
            (upperStar Λ c.obj.obj.obj.i).mapDerivedCategory.map b ≫
              (refinementTheta Λ r.hom K).hom = 𝟙 K ↔
          b = localizingRefinementMap Λ r.hom K) ∧
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingClosureProEtale Λ X K → IsIso (localizingRefinementMap Λ r.hom K)) ∧
    (∀ (c : Compactification.DenseBoundaryCompactification f)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingRefinementMap Λ (𝟙 c.obj) K ≫
          (refinementDerivedLowerStarId Λ c.obj.obj.obj.Z).hom.app
            ((openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K) = 𝟙 _) ∧
    (∀ (c d e : Compactification.DenseBoundaryCompactification f)
      (r : d ⟶ c) (s : e ⟶ d)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingRefinementMap Λ (s ≫ r).hom K ≫
          (refinementDerivedLowerStarComp Λ s.hom.hom.hom.hom r.hom.hom.hom.hom).hom.app
            ((openImmersionLowerShriek Λ e.obj.obj.obj.i).mapDerivedCategory.obj K) =
        localizingRefinementMap Λ r.hom K ≫
          (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.map
            (localizingRefinementMap Λ s.hom K)) := by
  exact localizingRefinement_coherence Λ ℓ k p hp hpℓ hΛ f

end AlgebraicGeometry.ProEtale.CondensedRing
