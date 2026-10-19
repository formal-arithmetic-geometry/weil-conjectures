/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.PQFCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
import Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare
import Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison

/-! # Quasi-coherent cohomology comparison and pullback

Source: Stacks Project, Étale Cohomology, Tag 03P2; Cohomology, Tag 01FD.
(blueprint: lem-weil-pbc-qcoherent-cohomology-comparison-pullback).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
attribute [local irreducible] moduleAbelianCohomologyLarge coherentEtaleMap
  qcoherentPullbackSection moduleCohomologyFMap IsNormalizedCoherentEtaleComparison

/-- The simultaneous normalized comparison, natural for arbitrary scheme pullback.
Source: Stacks Project, Étale Cohomology, Tag 03P2 and Cohomology, Tag 01FD.
(blueprint: lem-weil-pbc-qcoherent-cohomology-comparison-pullback).

Proof: Choose the uniquely normalized comparison on each scheme and invert it.
Its section normalization gives the degree-zero clause after cancelling the two
additive equivalences. The normalized Cech refinement square supplies the coefficient sheaf map with
its structural section formula and the required cohomology equality for the
arbitrary scheme morphism and coefficient map. For scalars, use coefficient
naturality of the normalized comparison on module cohomology, specialized to
multiplication by the scalar.
Cancel the chosen additive equivalence to obtain the scalar identity. -/
theorem exists_qcoherentCohomologyComparisonPullback :
    ∃ c : ∀ (X : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
      (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      Sheaf.H (liftedCoherentEtaleSheaf F) q ≃+
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F),
      (∀ (X : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
        (F : X.Modules) [F.IsQuasicoherent]
        (s : Γ(F, ⊤)),
        c X F 0 ((Sheaf.H.equiv₀ (liftedCoherentEtaleSheaf F)
          terminalIsTerminal).symm (ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F s))) =
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F s) ∧
      (∀ (X Y : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
        [CompactSpace Y] [Scheme.IsSeparated Y] (g : Y ⟶ X)
        (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
        (ψ : (tensorPullback g).obj F ⟶ G),
        ∃ θ : liftedCoherentEtaleSheaf F ⟶
          (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G),
          (∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
            θ.hom.app (op U) (ULift.up s) = ULift.up
              (qcoherentPullbackSection g F G ψ U
                ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
                (pullback.fst U.hom g) (pullback.condition) s)) ∧
          ∀ (q : ℕ) (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
            c Y G q (Sheaf.H.map
              ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
                (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
              q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q x)) =
            moduleCohomologyFMap g
              ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G ψ)
              q (c X F q x)) ∧
      (∀ (X : Scheme.{u}) [CompactSpace X] [Scheme.IsSeparated X]
        (F : X.Modules) [F.IsQuasicoherent] (a : Γ(X, ⊤)) (q : ℕ)
        (x : Sheaf.H (liftedCoherentEtaleSheaf F) q),
        c X F q (Sheaf.H.map (coherentEtaleMap F F (F.smulHom a)) q x) =
          (RingedSpace.moduleCohomology X.toRingedSpace q).map (F.smulHom a)
            (c X F q x)) := by
  classical
  choose d hd using fun (X : Scheme.{u}) (hC : CompactSpace X)
      (hS : Scheme.IsSeparated X) ↦
    (@exists_unique_qcoherentNormalizedComparison X hC hS).exists
  refine ⟨fun X hC hS F hF q ↦ (@d X hC hS F hF q).symm, ?_, ?_, ?_⟩
  · intro X hC hS F hF s
    have hz := (hd X hC hS).2.1
    exact (@d X hC hS F hF 0).symm_apply_eq.mpr
      ((Sheaf.H.equiv₀ (liftedCoherentEtaleSheaf F) terminalIsTerminal).symm_apply_eq.mpr
        (@hz F hF s).symm)
  · intro X Y hCX hSX hCY hSY g F G hF hG ψ
    exact @qcoherentNormalizedComparison_pullback_square X Y hCX hSX hCY hSY
      (d X hCX hSX) (d Y hCY hSY) (hd X hCX hSX).1 (hd Y hCY hSY).1
      g F G hF hG ψ
  · intro X hC hS F hF a q x
    have hn := (hd X hC hS).2.2
    have h := @hn F F hF hF (F.smulHom a) q ((@d X hC hS F hF q).symm x)
    exact (@d X hC hS F hF q).symm_apply_eq.mpr
      ((h.trans (congrArg (fun z ↦ Sheaf.H.map (coherentEtaleMap F F (F.smulHom a)) q z)
        ((@d X hC hS F hF q).apply_symm_apply x))).symm)

end
end AlgebraicGeometry.Scheme.Modules
