module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource

/-! # Locally separated group algebraic spaces over fields

Source: Stacks Project, More on Groupoids in Spaces, Tags 08BH and 0B8F
(blueprint: lem-sfb-locally-separated-group-space-scheme).

The group structure is encoded by a group-valued functor whose underlying presheaf is
identified with the algebraic space. The conclusion represents this same group-valued
functor by a group scheme, so the original operations are retained.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally separated group algebraic space locally of finite type over a field is
represented by a separated group scheme locally of finite type.
Source: Stacks Project, More on Groupoids in Spaces, Tags 08BH and 0B8F
(blueprint: lem-sfb-locally-separated-group-space-scheme).

Proof: (1) The identity section is representable by closed immersions, by
[lem-sfb-locally-separated-rational-point-closed-immersion] with the identity field
extension. (2) The diagonal is its pullback along the difference map
`(g, h) ↦ g⁻¹h`; hence it is closed, using
[lem-weil-pbc-closed-immersion-base-change]. (3) Choose an algebraic closure by
[def-weil-algebraic-closure]. By [lem-sfb-separated-group-space-geometric-scheme],
the geometric base change is a scheme. Its group operations are scheme morphisms
by [lem-pc-yoneda]. Base-changed étale charts cover it by
[lem-trf-space-fibre-products-etale-covers] and are locally of finite type by
[lem-weil-pbc-lft-base-change]. Their disjoint union is étale and surjective;
[def-weil-etale-morphism] and [lem-a1-lft-flat-lfp-source-descent] give local finite
type of the geometric representing scheme. (4) By [lem-sfb-group-finite-points-affine],
every finite list of geometric rational points lies in an affine open.
(5) [lem-sfb-geometric-affine-neighbourhood-scheme-descent] descends representability
to the original field. (6) Yoneda turns the original operations into morphisms
on the representing scheme and preserves every group identity, giving the group
scheme of [def-sc-group-scheme] and the asserted isomorphism of group functors.
Its diagonal is closed by (2), and the same étale-atlas descent argument as in (3)
gives local finite type. Neither quasi-compactness, smoothness nor reducedness is used. -/
theorem exists_groupScheme_of_locallySeparated
    {k : Type u} [Field k] (G : AlgebraicSpace (Spec (.of k)))
    (F : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (e : F ⋙ forget GrpCat ≅ G.obj.obj)
    (hlft : ∀ (U : Over (Spec (.of k))) (a : yoneda.obj U ⟶ G.obj.obj),
      IsEtale a → LocallyOfFiniteType U.hom)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (prod.lift (𝟙 G.obj.obj) (𝟙 G.obj.obj))) :
    ∃ P : Grp (Over (Spec (.of k))),
      IsSeparated P.X.hom ∧ LocallyOfFiniteType P.X.hom ∧
        Nonempty (yonedaGrp.obj P ≅ F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
