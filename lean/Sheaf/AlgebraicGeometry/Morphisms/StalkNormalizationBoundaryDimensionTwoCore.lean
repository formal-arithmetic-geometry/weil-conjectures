module
public import WeilConjectures.RingTheory.Depth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- Boundary points of the smooth pullback have stalk dimension at least two.
Source: Stacks Project, Tags 0EYJ, 0337, 00LK, 033C and 00H8.
(blueprint: new-stalk-normalization-boundary-dimension-two-target)
Proof: put a = S.fromSpecStalk s and f = pullback.snd c a ≫ a. Every point of
Spec O(S,s) specializes to its closed point, whose image under a is s. The
pullback identity and the boundary hypothesis show f(y) is outside U, so
minimality gives f(y) = s. The canonical map a is flat, and pullback.snd c a is
smooth, hence their composite is flat. The pullback is locally Noetherian,
since it is locally of finite type over the spectrum of the Noetherian stalk.
Apply the flat local depth formula to f.stalkMap y: the nonnegative fibre depth
shows depth at y is at least depth at s, hence at least two. The depth-support
bound for the stalk as a module over itself gives the Krull dimension bound.
The hypotheses hS and hs are retained unchanged but are not needed once hdepth
and hmin have been supplied. -/
theorem stalk_normalization_boundary_dimension_two_target {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    let a := S.fromSpecStalk s
    ∀ y : (pullback c a : Scheme.{u}),
      y ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤
        ringKrullDim ((pullback c a).presheaf.stalk y) := by
  dsimp only
  let a := S.fromSpecStalk s
  let f := pullback.snd c a ≫ a
  have : IsLocallyNoetherian (pullback c a) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd c a)
  intro y hy
  have hfy : f y = s := by
    apply hmin
    · exact ((IsLocalRing.specializes_closedPoint ((pullback.snd c a) y)).map
        a.continuous).trans (specializes_of_eq S.fromSpecStalk_closedPoint)
    · change c ((pullback.fst c a) y) ∉ U at hy
      simpa only [f, ← Hom.comp_apply, ← pullback.condition] using hy
  have hd : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk (f y)) (S.presheaf.stalk (f y)) := by
    rw [hfy]
    exact hdepth
  obtain ⟨_, hlocal, _, heq⟩ :=
    IsLocalRing.depth_eq_add_of_flat_local (f.stalkMap y).hom (Flat.stalkMap f y)
  have hdy : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := (pullback c a).presheaf.stalk y) ((pullback c a).presheaf.stalk y) := by
    rw [heq]
    exact hd.trans le_self_add
  exact (WithBot.coe_le_coe.mpr hdy).trans (by
    simpa only [Module.supportDim_self_eq_ringKrullDim] using
      IsLocalRing.depth_le_supportDim
        (R := (pullback c a).presheaf.stalk y) ((pullback c a).presheaf.stalk y))

end AlgebraicGeometry.Scheme
