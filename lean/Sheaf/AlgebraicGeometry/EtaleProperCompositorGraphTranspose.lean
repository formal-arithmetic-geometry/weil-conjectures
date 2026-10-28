/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.AlgebraicGeometry.EtaleProperGraphTransfer
public import Sheaf.AlgebraicGeometry.EtaleGraphChosenComparisons
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

/-! # The graph transpose of the compact-support compositor -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor canonicalEtaleCompactSupportComparison
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

/-- The transpose of compact-support composition is the clopen graph transfer.
Source: Stacks Project, Tags 0F7B, 0F7I, 0F7J; SGA 4 XVII 6.2.11.
(blueprint: lem-pur-proper-compositor-graph-transpose).

Proof in words: pull the proper part of c back along v. The lift of W to this
pullback is open and proper. Factor q through this clopen graph. Its proper
comparison is the derived inverse of extension-by-zero into direct image, since
that map is already an isomorphism on sheaves. For this tower the composition
isomorphism is open/proper interchange followed by proper composition.
Transpose the interchange under v_! adjoint to v^*: proper base change identifies
it with the unit of extension by zero along c.i, pulled back to the graph.
The triangle identities cancel the graph adjunction, leaving exactly transfer.
The common-refinement cocycle and tower independence identify this computation
with the chosen q and v models and then with c. Empty graphs give zero maps;
identity proper maps give the ordinary graph unit. No representative complex,
derived-functor unit, or sheaf transformation tau is involved in this assertion. -/
theorem properCompositor_graph_transpose
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    {f : W ⟶ Y} (hf : f = q ≫ v) [HasCompactification f]
    (c : Compactification f)
    (K : DerivedCategoryModule A W) :
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).homEquiv
        _ _ ((Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
            (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
          Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
            (graphChosenEtaleComparison A v).symm ≪≫
          unboundedEtaleLowerShriekCompIso A q v ≪≫
          unboundedEtaleLowerShriekCongr A hf.symm ≪≫
          (rightDerivedLowerShriekIso A c).symm).hom.app K) ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g v).toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) =
      ProperGraphTransfer.transfer q v hf c A K := by sorry

end AlgebraicGeometry.Etale
