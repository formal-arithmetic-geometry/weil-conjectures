/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The `n`-torsion subgroup scheme of an abelian variety

Let `A` be an abelian variety over a field `K` and let `n : ℕ`. Since `A` is commutative, the
multiplication by `n` map `[n] : A ⟶ A` is a homomorphism of group schemes, so it has a kernel
in the sense of `CategoryTheory.GrpObj.ker`. This kernel is the `n`-torsion subgroup scheme
`A[n]`.

## Main definitions

- `AlgebraicGeometry.IsAbelianVariety.torsion`: the `n`-torsion subgroup scheme `A[n]` of an
  abelian variety `A`, as a group scheme over `K`.

## Main results

- `AlgebraicGeometry.IsAbelianVariety.torsionHomMulEquiv`: the `T`-points of `A[n]` are exactly
  the `T`-points of `A` killed by `n`. Taking `T = Spec K`, the `K`-points of `A[n]` are the
  `n`-torsion of the group `A(K)`.
- `A[n]` is a closed subscheme of `A`, and is proper and separated over `K`.

Finiteness, étaleness and the rank of `A[n]` are not proved here; they need the isogeny theorem.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.IsAbelianVariety

universe u

variable {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] [IsAbelianVariety G] (n : ℕ)

/-- The `n`-torsion subgroup scheme `A[n]` of an abelian variety `A` over `K`: the kernel of the
multiplication by `n` isogeny `[n] : A ⟶ A`. -/
noncomputable def torsion : Over (Spec (.of K)) :=
  GrpObj.ker (GrpObj.npow G n)

/-- The `n`-torsion `A[n]` is a group scheme over `K`. -/
noncomputable instance : GrpObj (torsion G n) :=
  inferInstanceAs (GrpObj (GrpObj.ker (GrpObj.npow G n)))

/-- The inclusion `A[n] ⟶ A` is a closed immersion, since it is the base change of the identity
section of `A` along `[n]`. -/
instance : IsClosedImmersion (GrpObj.kerι (GrpObj.npow G n)).left :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    ((Over.forget (Spec (.of K))).map_isPullback
      (GrpObj.isPullback_kerι (GrpObj.npow G n)).flip)
    (inferInstanceAs (IsClosedImmersion η[G].left))

/-- The `n`-torsion of an abelian variety is proper over the base field. -/
instance : IsProper (torsion G n).hom := by
  have h : (torsion G n).hom = (GrpObj.kerι (GrpObj.npow G n)).left ≫ G.hom :=
    (Over.w (GrpObj.kerι (GrpObj.npow G n))).symm
  rw [h]
  infer_instance

/-- The `n`-torsion of an abelian variety is separated over the base field. -/
instance : IsSeparated (torsion G n).hom := inferInstance

/-- The `T`-points of `A[n]` are exactly the `n`-torsion `T`-points of `A`. Taking
`T = Spec K`, this says that the `K`-points of `A[n]` are the `n`-torsion of the group `A(K)`. -/
noncomputable def torsionHomMulEquiv (T : Over (Spec (.of K))) :
    (T ⟶ torsion G n) ≃* (powMonoidHom n : (T ⟶ G) →* (T ⟶ G)).ker :=
  (GrpObj.kerHomMulEquiv (GrpObj.npow G n) T).trans <| MulEquiv.subgroupCongr <| by
    ext x
    simp [MonoidHom.mem_ker, GrpObj.comp_npow]

@[simp]
lemma coe_torsionHomMulEquiv {T : Over (Spec (.of K))} (a : T ⟶ torsion G n) :
    ((torsionHomMulEquiv G n T a : (powMonoidHom n : (T ⟶ G) →* (T ⟶ G)).ker) : T ⟶ G) =
      a ≫ GrpObj.kerι (GrpObj.npow G n) :=
  rfl

end AlgebraicGeometry.IsAbelianVariety
