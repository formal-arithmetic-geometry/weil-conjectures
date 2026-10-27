module

public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces

/-! # Geometric coroots

Source: Milne, Algebraic Groups (2017), Theorem 21.11(d),(e), pp.428--430
(blueprint: def-sfb-geometric-coroot).

The reflection is represented in the actual normalizer inside the centralizer of the
largest subtorus of the root kernel. Thus this predicate specifies the geometric
coroot, including its central-torus component, rather than an arbitrary dual vector
with root pairing two. All conjugation identities are tested on algebra points.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.RankOneRoots

/-- The coroot cocharacter characterized by the nonidentity local Weyl reflection.
For a reductive group with maximal torus T and root alpha, Theorem 21.11(d),(e)
identifies this predicate with being alpha's coroot. The local normalizer lies in
C_G(T_alpha), where T_alpha is the largest subtorus of ker(alpha). The integer m
is the composition pairing with the test character; the last identity is the
reflection formula x ↦ x - <x,c> alpha, written multiplicatively.
Source: Milne, Theorem 21.11(d),(e), pp.428--430
(blueprint: def-sfb-geometric-coroot). -/
def IsGeometricCoroot {F : Type u} [Field F]
    {T G : Grp (Over (Spec (.of F)))} (i : T ⟶ G)
    (α : Character T) (c : Cocharacter T) : Prop :=
  α.hom.hom ≠ 1 ∧
  c.hom.hom ≫ α.hom.hom = (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (2 : ℤ) ∧
  ∃ (S : Grp (Over (Spec (.of F)))) (s : S ⟶ Grp.mk (GrpObj.ker α.hom.hom)),
    MultiplicativeType.IsLargestSubtorus s ∧
    ∃ n : normalizer i,
      n.val ∉ pointImage i (𝟙_ _) ∧
      (∀ A : CommAlgCat.{u} F,
        toUnit (StandardGroupSchemes.affine F A) ≫ n.val ∈
          ReductiveTorusCentralizer.centralizerPoints
            (Grp.homMk (s.hom.hom ≫ GrpObj.kerι α.hom.hom) ≫ i) A) ∧
      ∀ χ : Character T, ∃ m : ℤ,
        c.hom.hom ≫ χ.hom.hom = (𝟙 (StandardGroupSchemes.multiplicative F)) ^ m ∧
        ∀ (A : CommAlgCat.{u} F) (t : StandardGroupSchemes.affine F A ⟶ T.X),
          ∃ t' : StandardGroupSchemes.affine F A ⟶ T.X,
            t' ≫ i.hom.hom = ((toUnit (StandardGroupSchemes.affine F A) ≫ n.val)⁻¹ *
              (t ≫ i.hom.hom) * (toUnit (StandardGroupSchemes.affine F A) ≫ n.val)) ∧
            t' ≫ χ.hom.hom = (t ≫ χ.hom.hom) / (t ≫ α.hom.hom) ^ m

end AlgebraicGeometry.RankOneRoots
