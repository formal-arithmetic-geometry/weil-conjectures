/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocusDual
public import WeilConjectures.AlgebraicGeometry.PicardTensorDualComparisonIso

/-! # Tautological map and section of a line subbundle

Source: Stacks Project, Tag 0FI5, `proposition-chern-class`, the line-subbundle paragraph;
Tags 01OB and 01X0.
(blueprint: def-pur-line-subbundle-projective-divisor-data).

The two definitions were moved unchanged from `LineSubbundleProjectiveDivisor` so that the
split theorems `LineSubbundleProjectiveDivisorCore` and `…FiniteType` can state their
conclusions without an import cycle. They are direct constructions: the tensor pullback of
`ι` followed by the tautological quotient, and its adjoint section followed by the inverse of
the canonical Picard tensor-dual comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry

/-- The composite `p*L → p*F → O(1)`, using the specified tensor pullback.
Source: Stacks, Tags 0FI5 and 01OB
(blueprint: def-pur-line-subbundle-projective-divisor-data). -/
def lineSubbundleProjectiveMap {S : Scheme.{u}} {L F : S.Modules}
    (P : ProjectiveBundleRealization S F) (ι : L ⟶ F) :
    (Scheme.Modules.tensorPullback P.A.data.relProjHom).obj L ⟶ P.L :=
  (Scheme.Modules.tensorPullback P.A.data.relProjHom).map ι ≫ P.quotient

/-- The actual section of `O(1) ⊗ p*(Lᵛ)` corresponding to the tautological composite.
The dual comparison is the canonical transpose of pulled evaluation, not a chosen isomorphism.
Source: Stacks, Tags 0FI5, 01OB and 01X0
(blueprint: def-pur-line-subbundle-projective-divisor-data). -/
def lineSubbundleProjectiveSection {S : Scheme.{u}} {L F : S.Modules}
    [L.IsInvertible] (P : ProjectiveBundleRealization S F) (ι : L ⟶ F) :
    𝟙_ P.A.data.relProj.Modules ⟶
      P.L ⊗ (Scheme.Modules.tensorPullback P.A.data.relProjHom).obj Lᵛ :=
  letI : ((Scheme.Modules.tensorPullback P.A.data.relProjHom).obj L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso
      ((projectiveBundleTensorPullbackIso P.A.data.relProjHom).app L).symm
  letI : SheafOfModules.IsInvertible.{u, u, u} L :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  letI : IsIso (Scheme.Modules.picardTensorDualComparison P.A.data.relProjHom L) :=
    Scheme.picardTensorDualComparison_isIso P.A.data.relProjHom L
  Scheme.Modules.Hom.adjointSection (lineSubbundleProjectiveMap P ι) ≫
    P.L ◁ (asIso (Scheme.Modules.picardTensorDualComparison P.A.data.relProjHom L)).inv

end AlgebraicGeometry
