module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProduct

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Unsigned Alexander--Whitney pairing on a pair of Cech rows of a resolution pairing.
Source: Stacks Project, Remark 20.25.3, equation 07MB.
(blueprint: new-cup-cech-pair-cochain)
The value at a tuple is the pairing of the restrictions of its front and back faces. -/
def cupCechPairCochain {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (D : CupResolutionPairing F G) (r s i j : ℕ)
    (a : ((cupCechDouble U D.left.K).X r).X i)
    (b : ((cupCechDouble U D.right.K).X s).X j) :
    ((cupCechDouble U D.target.K).X (r + s)).X (i + j) :=
  (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
    (D.target.K.X (r + s)).presheafModuleCat (i + j)).symm
    (fun y ↦ D.pair r s (⨅ k, U (y k))
      ((D.left.K.X r).presheaf.map (cupFaceRestriction U y (cupFront i j)).op
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
          (D.left.K.X r).presheafModuleCat i a (y ∘ cupFront i j)))
      ((D.right.K.X s).presheaf.map (cupFaceRestriction U y (cupBack i j)).op
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
          (D.right.K.X s).presheafModuleCat j b (y ∘ cupBack i j))))

end
end AlgebraicGeometry.Scheme.Modules
