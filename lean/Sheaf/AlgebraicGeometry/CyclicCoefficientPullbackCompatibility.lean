module

public import Sheaf.AlgebraicGeometry.CyclicDerivedHomComparisonMap

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Compatibility of the canonical cyclic coefficient comparisons with pullback.
Source: Stacks Project, Tag 03Q8, and the constant-sheaf pullback coherence.
(blueprint: lem-sbc-cyclic-coefficient-pullback-compatibility).

Proof: Apply `cohomologyMap_map` to the coefficient comparison on the target.
The composition identity for constant-sheaf inverse images identifies the
resulting coefficient morphism with the comparison on the source composed with
the inverse of the upper-star composition isomorphism.
-/
theorem cyclicCoefficientPullbackCompatibility {X Y : Scheme.{u}}
    (h : Y ⟶ X) (e q : ℕ) (W V : X.Etale) (v : V ⟶ W)
    (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).obj
      (Y.constantZMod e)) q) :
    let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
    let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
      (pullback.fst h V.hom) (by simp [g])
    Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).app
        (AddCommGrpCat.of (ULift (ZMod e)))).hom q
      (cohomologyMap g _ q
        (Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst h W.hom)).app
            (AddCommGrpCat.of (ULift (ZMod e)))).hom q x)) =
      Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
        (pullback.fst h V.hom)).app
          (AddCommGrpCat.of (ULift (ZMod e)))).hom q
        (Sheaf.H.map (i.inv.app (Y.constantZMod e)) q
          (cohomologyMap g _ q x)) := by
  sorry

end AlgebraicGeometry.Etale
