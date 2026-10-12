module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-! # Injectivity of restriction on a disjoint ideal twist

Source: Stacks Project, Remark 09NW, the kernel calculation, and Lemma 09NX.
(blueprint: lem-sc-closed-immersion-disjoint-ideal-twist-mono).
-/

/-- Restriction of an ideal times an invertible module is monic when the ideal has
zero intersection with the closed-immersion ideal.

Source: Stacks Project, Remark 09NW, the calculation I/(I intersection J), and the
local trivialization argument in Lemma 09NX.
(blueprint: lem-sc-closed-immersion-disjoint-ideal-twist-mono).

Proof: put N = M.tensorPow m, which is locally free of rank one. Choose an affine
basis of Y on which N is trivial. On V = Spec A in this basis, write K = I(V) and
J = ker(A -> B), where i inverse-image V = Spec B and A -> B is surjective.
The source multiplication image has sections K, and the canonical pullback unit
restricts to K -> B, a -> its residue class. Its kernel is K intersection J,
which is zero by hzero V. Thus this map is injective on the basis. If two sections
on any open have equal images, their difference restricts to zero on every basis
open contained in it; sheaf separatedness makes the difference zero. Hence the
morphism is monic. For the chosen adjunction, compare it with the canonical one
by uniqueness of left adjoints. The unit comparison postcomposes the canonical
unit by the pushforward of an isomorphism on N. Postcomposition by an isomorphism
preserves monicity. Outside the closed image B is the zero ring and J = A, so
hzero forces K = 0; the same argument covers empty opens, m = 0 and I = 0. -/
theorem closedImmersion_disjointIdeal_twist_mono {Y X : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (I : Y.IdealSheafData)
    (hzero : ∀ U : Y.Opens, I.idealOfOpens U ⊓ i.ker.idealOfOpens U = ⊥)
    (M : Y.Modules) [M.IsInvertible] (m : ℕ) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
    Mono (image.ι μ ≫ adj.unit.app (M.tensorPow m)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
