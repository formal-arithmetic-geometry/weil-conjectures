module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant
public import WeilConjectures.ConstructibleSheaf.Pullback

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- The pullback of each stratum in a constructible set sheaf remains finite locally constant.
Source: the three-step proof of `lem-weil-pbc-constructible-etale-set-pullback`, with the
stratification fixed.  Pull back the trivializing covers and use the inverse-image
composition, restriction, constant-sheaf, stalk, and algebraic-structure comparisons.
Proof: Pull back finite trivializing covers along g. Composition, restriction, and constant-sheaf
comparisons preserve local constancy; stalk-germ bijections preserve finiteness; the
algebraic-structure comparison identifies the result with the underlying set sheaf.
(blueprint: lem-stage3-finite-lc-pullback-stratum). -/
theorem finiteLocallyConstant_pullback_stratum
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (S : Stratification X)
    (hS : ∀ i : Fin S.n, IsFiniteLocallyConstantEtaleSheafOfSets
      ((etaleSetPullback (S.immersion i)).obj
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))) :
    ∀ i : Fin S.n, IsFiniteLocallyConstantEtaleSheafOfSets
      ((etaleSetPullback ((S.pullback g).immersion i)).obj
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj E))) := by
  sorry
end AlgebraicGeometry.Scheme
