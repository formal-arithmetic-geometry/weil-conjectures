module

public import Sheaf.Paper.StrictEtaleSystemInterfaces

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- Explicit mate-pasting remainder for the open singleton evaluation.
Source: Zheng, Construction 5.14 and Lemma 5.16.
(blueprint: lem-pur-etale-brown-open-singleton-evaluation-core).
The defining conjugate expansion of the insertion is first reduced to this
explicit composite; the remaining equality is the scalar/open mate square. -/
theorem etaleBrownOpenSingletonEvaluationCore
    (S : StrictEtaleCompactSupport O t c) {m n : ℕ} (h : m ≤ n)
    (q : (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived)
    (hq : (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ q.hom)).natTrans = (S.openDerived.derivedTensor h).inv)
    (P : DerivedCategory (strictEtaleLevel X O t n)) :
    (S.PZ.evaluation m).map
        ((S.derivedOpen.map ((S.PX.derivedExtension n).map
          ((S.levelDerivedOpenAdjunction n).unit.app P ≫
            (S.openDerived.level n).inverse.map
              ((S.PZ.derivedAdj n).unit.app ((S.levelDerivedOpen n).obj P)))) ≫
          S.derivedOpen.map ((S.PX.derivedExtension n).map
            ((S.openDerived.inverseEvaluation n).inv.app
              ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)))) ≫
          S.derivedOpen.map ((S.PX.derivedAdj n).counit.app
            (S.openDerived.system.inverse.obj
              ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)))) ≫
          S.derivedOpenAdjunction.counit.app
            ((S.PZ.derivedExtension n).obj ((S.levelDerivedOpen n).obj P)))) ≫
      (S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P) =
    (S.openDerivedEvaluation m).hom.app ((S.PX.derivedExtension n).obj P) ≫
      (S.levelDerivedOpen m).map ((S.PX.derivedBelow h).hom.app P) ≫ q.hom.app P := by
  sorry

end AlgebraicGeometry
