/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
import Sheaf.AlgebraicGeometry.GroupScheme.LieLocalDimension
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension

/-!
# The Lie algebra of a group scheme of finite type over a field

The Lie algebra of a group scheme of finite type over a field.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry

/-! ### Group schemes of finite type over a field -/

section Field

variable {k : Type u} [Field k]

/-- A morphism of schemes locally of finite type over an algebraically closed field `k` which is
surjective on underlying spaces is surjective on `k`-points.

Proof sketch (not formalised): the fibre of `f` over the closed point `y` is a nonempty scheme
locally of finite type over `k`; by the Nullstellensatz its closed points have residue field `k`,
and such a point is a `k`-point of `X` over `y`. -/
theorem exists_points_comp_eq_of_surjective [IsAlgClosed k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) (hf : Function.Surjective f.left.base)
    (y : points Y k) : ∃ x : points X k, x ≫ f = y := by
  have : Surjective f.left := ⟨hf⟩
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
      simpa only [Over.w] using (inferInstance : LocallyOfFiniteType X.hom)
    exact locallyOfFiniteType_of_comp f.left Y.hom
  let Z := Limits.pullback f.left y.left
  let p : Z ⟶ Spec (.of k) := Limits.pullback.snd f.left y.left
  have : Nonempty Z := ⟨(p.surjective (IsLocalRing.closedPoint k)).choose⟩
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, -, hz⟩ :=
    nonempty_inter_closedPoints (X := Z) Set.univ_nonempty isClosed_univ.isLocallyClosed
  let s := pointOfClosedPoint p z hz
  have hs : s ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z hz
  have hlift : (s ≫ Limits.pullback.fst f.left y.left) ≫ f.left = y.left := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, Category.id_comp]
  refine ⟨Over.homMk (s ≫ Limits.pullback.fst f.left y.left) ?_, ?_⟩
  · rw [← Over.w f, ← Category.assoc, hlift]
    exact y.w
  · exact Over.OverMorphism.ext hlift


namespace GrpObj

variable (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

/-- The Lie algebra of a group scheme of finite type over a field only sees the identity
component: the differential of the open immersion `G° ⟶ G` is bijective.
(blueprint: `sk-i-cartier`) -/
theorem differential_identityComponentι_bijective :
    Function.Bijective (differential (identityComponentι G)) :=
  differential_bijective_of_isOpenImmersion (identityComponentι G)

/-- The Lie algebra of a group scheme of finite type over a field is the Lie algebra of its
identity component. (blueprint: `sk-i-cartier`) -/
noncomputable def lieEquivIdentityComponent : Lie (identityComponent G) ≃ₗ⁅k⁆ Lie G :=
  lieEquivOfIsOpenImmersion (identityComponentι G)

/-- Cartier's theorem, Lie algebra form: over a field of characteristic zero, the Lie algebra of a
group scheme `G` of finite type has dimension the dimension of `G`.

Proof sketch (not formalised): `Lie(G)` is the tangent space at the identity; in characteristic
zero `G` is smooth (`AlgebraicGeometry.GrpObj.isReduced_of_charZero`), so this tangent space has
the dimension of `G` at the identity, which is the dimension of `G` since the connected components
of `G` are translates of `G°` after base change to the algebraic closure.
(blueprint: `sk-i-cartier`) -/
theorem finrank_lie_eq_topologicalKrullDim [CharZero k] :
    (Module.finrank k (Lie G) : WithBot ℕ∞) = topologicalKrullDim G.left := by
  let : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  have : Smooth G.hom := smooth_of_grpObj_of_charZero G.hom
  exact (finrank_lie_eq_localKrullDim_of_smooth G).trans
    (localKrullDim_identity_eq_topologicalKrullDim G)

end GrpObj

end Field

end AlgebraicGeometry
