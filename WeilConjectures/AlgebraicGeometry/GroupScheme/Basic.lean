/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Geometry of group schemes over a field

Let `G` be a group scheme over a field `k`: a group object in `Over (Spec k)`. This file states
the basic facts about the underlying scheme of `G` used for algebraic groups: left translation by a
rational point is an automorphism of `G`; a group scheme of finite type has finitely many connected
components and its identity component `G°` is open; the image of a homomorphism of group schemes of
finite type is closed; and a closed subgroup of a connected reduced group of the same dimension is
the whole group.

## Main definitions

- `AlgebraicGeometry.GrpObj.onePoint`: the identity point of `G`, the image of the unit section.
- `AlgebraicGeometry.GrpObj.mulLeft`: left translation by a rational point `g` of `G`.
- `AlgebraicGeometry.GrpObj.identityComponentOpens`: the identity component `G°`, as an open
  subset of `G`.

## Main results

- `AlgebraicGeometry.finite_connectedComponents`: a group scheme of finite type over `k` has
  finitely many connected components.
- `AlgebraicGeometry.isClosed_range_of_isMonHom`: the image of a homomorphism from a group scheme
  of finite type to a group scheme locally of finite type over `k` is closed.
- `AlgebraicGeometry.isIso_left_of_topologicalKrullDim_eq`: a closed subgroup of a connected reduced
  group of the same dimension is the whole group.

## Blueprint

- `sk-p-geometry`: the identity component, images of homomorphisms and the dimension criterion.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The identity point of a group scheme `G` over a field `k`: the image of the unique point of
`Spec k` under the unit section. (blueprint: `sk-p-geometry`) -/
noncomputable def GrpObj.onePoint (G : Over (Spec (.of k))) [GrpObj G] : G.left :=
  η[G].left.base (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩)

/-- Left translation `x ↦ g * x` on a group scheme `G` over `k` by a rational point `g` of `G`.
(blueprint: `sk-p-geometry`) -/
noncomputable def GrpObj.mulLeft (G : Over (Spec (.of k))) [GrpObj G]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⟶ G :=
  lift (toUnit G ≫ g) (𝟙 G) ≫ μ[G]

/-- Left translation by a rational point is an automorphism of the underlying scheme.
(blueprint: `sk-p-geometry`) -/
theorem GrpObj.isIso_mulLeft_left (G : Over (Spec (.of k))) [GrpObj G]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : IsIso (GrpObj.mulLeft G g).left := by
  have hmul (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : GrpObj.mulLeft G g = (toUnit G ≫ g) * 𝟙 G :=
    rfl
  have hcomp (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
      GrpObj.mulLeft G g ≫ GrpObj.mulLeft G h = GrpObj.mulLeft G (h * g) := by
    rw [hmul, hmul, hmul, MonObj.comp_mul, ← Category.assoc, toUnit_unique (_ ≫ toUnit G),
      Category.comp_id, ← mul_assoc, MonObj.comp_mul]
  have hone : GrpObj.mulLeft G 1 = 𝟙 G := by
    rw [hmul, MonObj.comp_one, one_mul]
  have : IsIso (GrpObj.mulLeft G g) :=
    ⟨GrpObj.mulLeft G g⁻¹, by rw [hcomp, inv_mul_cancel, hone],
      by rw [hcomp, mul_inv_cancel, hone]⟩
  exact inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulLeft G g)))

/-- The underlying scheme of a group scheme of finite type over a field is noetherian. -/
theorem isNoetherian_left (G : Over (Spec (.of k))) [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] : IsNoetherian G.left :=
  have := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have := QuasiCompact.compactSpace_of_compactSpace G.hom
  {}

/-- A group scheme of finite type over a field has finitely many connected components.
(blueprint: `sk-p-geometry`) -/
theorem finite_connectedComponents (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    Finite (_root_.ConnectedComponents G.left) :=
  have := isNoetherian_left G
  inferInstance

/-- The connected component of the identity of a group scheme of finite type over a field is open.
(blueprint: `sk-p-geometry`) -/
theorem isOpen_connectedComponent_onePoint (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsOpen (connectedComponent (GrpObj.onePoint G)) :=
  have := isNoetherian_left G
  TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _

/-- The identity component `G°` of a group scheme `G` of finite type over a field, as an open
subset of `G`: the connected component of the identity point. (blueprint: `sk-p-geometry`) -/
noncomputable def GrpObj.identityComponentOpens (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] : G.left.Opens :=
  ⟨connectedComponent (GrpObj.onePoint G), isOpen_connectedComponent_onePoint G⟩

/-- The image of a homomorphism from a group scheme of finite type to a group scheme locally of
finite type over a field is closed (SGA 3, VI_B, Proposition 1.2).

The source must be quasi-compact: the homomorphism `ℤ ⟶ 𝔾ₐ` from the constant group scheme,
`n ↦ n`, over `ℚ` has image the infinite non-closed set of closed points `n ∈ 𝔸¹_ℚ`.

Proof sketch (not formalized): after base change to an algebraic closure the image is
constructible (Chevalley), hence contains a dense open subset of its closure; translating it by
rational points shows the image is open in its closure, hence closed. Closedness descends along
the closed surjection from the base change. The matrix-group case over an algebraically closed
field is `Matrix.GeneralLinearGroup.RationalHom.isClosed_range` (blueprint
`lem-ag-homomorphism-image-closed`). (blueprint: `sk-p-geometry`) -/
theorem isClosed_range_of_isMonHom {G K : Over (Spec (.of k))} [GrpObj G] [GrpObj K]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [LocallyOfFiniteType K.hom] (f : G ⟶ K)
    [IsMonHom f] :
    IsClosed (Set.range f.left.base) := by
  sorry

/-- A connected group scheme locally of finite type over a field is irreducible (SGA 3, VI_A,
Proposition 2.4).

Proof sketch (not formalized): having the rational point `e`, the connected scheme `G` is
geometrically connected. Over an algebraic closure the translations by rational points act
transitively on the closed points, so the finitely many irreducible components through any point
are disjoint and the connected group is irreducible; irreducibility descends along the surjection
from the base change. (blueprint: `sk-p-geometry`) -/
theorem irreducibleSpace_of_connectedSpace (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] : IrreducibleSpace G.left := by
  sorry

/-- A closed subgroup `J` of a connected reduced group scheme `G` locally of finite type over a
field, with `J` reduced of the same dimension as `G`, is all of `G`.
(blueprint: `sk-p-geometry`) -/
theorem isIso_left_of_topologicalKrullDim_eq {J G : Over (Spec (.of k))} [GrpObj J] [GrpObj G]
    [LocallyOfFiniteType G.hom] [IsReduced J.left] [IsReduced G.left] [ConnectedSpace G.left]
    (f : J ⟶ G) [IsMonHom f] [IsClosedImmersion f.left]
    (h : topologicalKrullDim J.left = topologicalKrullDim G.left) : IsIso f.left := by
  have := irreducibleSpace_of_connectedSpace G
  have : IsIntegral G.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : Surjective f.left :=
    ⟨f.left.isClosedEmbedding.isInducing.surjective_of_topologicalKrullDim_eq
      f.left.isClosedEmbedding.isClosed_range (topologicalKrullDim_ne_top G.hom) h⟩
  exact isIso_of_isClosedImmersion_of_surjective f.left

end AlgebraicGeometry
