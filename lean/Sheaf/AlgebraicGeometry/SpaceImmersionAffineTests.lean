module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-! # Immersions of algebraic spaces: affine tests, locality, and base change

Source: Stacks Project, Morphisms of Spaces, Tag 03M4, immersion cases (1), (3), (5);
Spaces, Tags 02YU and 02YW (blueprint: lem-sfb-space-immersion-affine-tests).

`IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)` expresses immersion, including
representability, using the existing scheme-test interface. Scheme `IsImmersion` is
closed immersion followed by open immersion by `IsImmersion.isImmersion_iff_exists`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Immersion can be tested on affine schemes, without assuming representability first.
Source: Stacks Project, Morphisms of Spaces, Tag 03M4, immersion cases (1) and (3)
(blueprint: lem-sfb-space-immersion-affine-tests).

Proof: (1) All scheme tests include affine tests. (2) Conversely, for any scheme `T → Y`,
cover `T` by affine opens `Tᵢ`. The affine-test hypothesis represents the restrictions
of `E = X ×_Y T` by schemes immersed in `Tᵢ`. By
[lem-trf-space-fibre-products-etale-covers], `E` is an algebraic space, hence an fppf
sheaf and a Zariski sheaf by [lem-pc-zariski-coverings-are-fppf]. Each restriction is an
open subfunctor of `E`, since open immersions are preserved by base change
[lem-weil-pbc-open-immersion-base-change]. They cover every scheme test, so
[lem-pc-schemes-criterion] glues them to a scheme representing `E`.
(3) Apply [lem-zl-immersion-near-image-locality] to its projection to `T` and the open
cover `Tᵢ`. This is an immersion; all scheme tests now satisfy the defining condition.
The argument permits the empty scheme and its empty affine cover. -/
theorem immersion_iff_affine_scheme_tests
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left) f.hom.hom ↔
      ∀ (V : Over S), IsAffine V.left → ∀ a : yoneda.obj V ⟶ Y.obj.obj,
        ∃ (U : Over S) (p : U ⟶ V) (q : yoneda.obj U ⟶ X.obj.obj),
          IsPullback q (yoneda.map p) f.hom.hom a ∧ IsImmersion p.left := by
  sorry

/-- Immersion is equivalent to immersion over some covering by open subspaces.
Source: Stacks Project, Morphisms of Spaces, Tag 03M4, immersion cases (1) and (5)
(blueprint: lem-sfb-space-immersion-affine-tests).

Proof: (1) Immersion is preserved by base change, directly from scheme tests and
fibre-product associativity [lem-trf-space-fibre-products-etale-covers]. Thus the
one-member open cover by `Y` works. (4) Conversely, pull the open-subspace covering
back to an arbitrary scheme `T → Y`. By [def-a1-space-open-subspace], its members are
open subschemes `Tₐ` covering `T`. The immersion hypothesis on each restriction gives a
scheme representing `Eₐ = (X ×_Y T) ×_T Tₐ`, immersed in `Tₐ`. The fppf sheaf
`E = X ×_Y T` is a Zariski sheaf [lem-pc-zariski-coverings-are-fppf]; its subfunctors
`Eₐ` are open by [lem-weil-pbc-open-immersion-base-change] and cover every scheme test.
Apply [lem-pc-schemes-criterion] to represent `E` by a scheme, then
[lem-zl-immersion-near-image-locality] to show `E → T` is an immersion. Since `T` was
arbitrary this proves the scheme-test condition. If the covering is empty, `T` is
empty, and both cited gluing and locality criteria allow the empty family. -/
theorem immersion_iff_exists_open_subspace_cover
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left) f.hom.hom ↔
      ∃ (I : Type (u + 1)) (U : I → OpenSubspace Y),
        IsJointlySurjective (fun i : I ↦ (U i).val.ι) ∧
          ∀ i : I, IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
            (Limits.pullback.snd f.hom.hom (U i).val.ι) := by
  sorry

/-- Immersions are preserved by arbitrary algebraic-space base change.
Source: Stacks Project, Spaces, Tag 02YW
(blueprint: lem-sfb-space-immersion-affine-tests).

Proof: (1) Given `Y' → Y` and any scheme `T → Y'`, fibre-product associativity
[lem-trf-space-fibre-products-etale-covers] identifies
`(X ×_Y Y') ×_{Y'} T` with `X ×_Y T` over `T`. The immersion hypothesis represents
the latter by a scheme immersed in `T`. Transport the representing pullback square
along this canonical isomorphism. This verifies every scheme test of the projection
`X ×_Y Y' → Y'`, with no representability hypothesis on the base-change morphism. -/
theorem immersion_presheafMap_baseChange
    {S : Scheme.{u}} (X Y Y' : AlgebraicSpace S) (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left) f.hom.hom) :
    IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (Limits.pullback.snd f.hom.hom g.hom.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
