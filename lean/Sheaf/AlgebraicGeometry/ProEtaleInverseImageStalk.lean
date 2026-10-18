/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.Grp.Colimits
import Sheaf.AlgebraicGeometry.ProEtaleSheafificationGeometricStalk
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.WeaklyEtaleField
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Geometric stalks commute with pro-etale inverse image

Source: Stacks Project, Tags 05V1 and 0F4F; pro-etale geometric points and
neighbourhoods, Tags 0F6B, 0F6C and 0993
(blueprint: lem-pur-proetale-inverse-image-stalk).

The germ equation characterizes the canonical comparison: the germ of the adjunction
unit at the pulled-back pointed neighbourhood maps to the original germ. Naturality
and reflection of equality at image geometric points are stated in both coefficient cases.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Geometric stalks of set sheaves commute with inverse image along every scheme morphism.
The first clause fixes the canonical comparison by its value on unit germs; the
second is naturality in the sheaf; the third reflects equality of inverse-image maps
at the image geometric point.
Source: Stacks Project, Tags 05V1, 0F4F, 0F6B, 0F6C and 0993
(blueprint: lem-pur-proetale-inverse-image-stalk).

Proof:
1. Put `P = u_{f,p} F`. A lift of `x ≫ f` to `V` pairs uniquely with `x` to
   give a lift to `u_f(V)`, by `def-pc-fibre-product`. These correspondences respect
   pointed arrows. All diagrams are small by `def-weil-size-convention`.
2. A cover of a pointed neighbourhood lifts the fixed field point to a member.
   Base change the fpqc cover (`lem-galois-fpqc-covering-base-change`); choose a
   nonempty affine fibre. Weakly etale base change and source locality reduce to
   `lem-weil-pbc-weak-etale-field`, using `def-weil-pbc-ind-etale-algebra`.
   Its residue field embeds back into the algebraically closed field by
   `lem-weil-pbc-separable-extension-embeds-separably-closed`. Transport to a skeleton.
3. In sets, local representation and local equality of sheafified sections
   (`lem-weil-pbc-site-sheafification-sections-local`), together with step 2 and
   filteredness of pointed neighbourhoods, make the stalk of the sheafification
   unit bijective, naturally in `P`.
4. In abelian groups, `lem-cbc-proetale-sheafification-geometric-stalk` gives
   the same natural isomorphism `t : P_x ≅ (f⁻¹F)_x` in abelian groups.
5. Define `a : P_x → F_{x ≫ f}` on an inner coprojection `(U,point,V,φ)` by the
   germ of its section at the lift obtained by projecting `φ(point)` to `V`.
   These maps respect the inner comma arrows and outer pointed restrictions,
   so the two colimit universal properties descend them (`def-weil-pbc-category-colimit`).
6. Define `b : F_{x ≫ f} → P_x` using `(u_f(V),paired lift,V,id)` on each
   germ. The inverse-image restriction formula identifies its restriction along
   `u_f(r)` with the coprojection `(V',u_f(r))`; the inner comma arrow from
   `(V,id)` gives compatibility, so this also descends to the colimit.
7. On original germs `ab` is the identity. On the twice-indexed coprojections,
   the pointed arrow `φ` identifies `ba` with the identity. Thus `a` and `b`
   are inverse; take `c = a t⁻¹`. This yields exactly the unit-germ equation.
8. On every inner coprojection, both naturality paths send `s` to the germ of
   `h(s)` at its projected lift. Descend twice and use naturality of `t`.
   All arrows in the abelian case are homomorphisms. Conjugating by `c` shows
   that equal inverse images give equal stalk maps at `x ≫ f`.
-/
theorem proEtaleInverseImage_setStalk
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ c : ∀ F : Sheaf (ProEt.topology Y) (Type (u + 1)),
      proEtaleGeometricStalk x ((proEtaleSheafInverseImage f (Type (u + 1))).obj F) ≅
        proEtaleGeometricStalk (x ≫ f) F,
      (∀ (F : Sheaf (ProEt.topology Y) (Type (u + 1)))
        (N : ProEtaleGeometricNeighbourhood (x ≫ f))
        (a : Over.mk x ⟶ (ProEt.forget X).obj ((proEtaleBaseChange f).obj N.right)),
        a.left ≫ pullback.fst N.right.hom f = N.hom.left →
        ((proEtaleSheafAdjunction f (Type (u + 1))).unit.app F).hom.app (op N.right) ≫
          colimit.ι (proEtaleGeometricStalkDiagram x
            ((proEtaleSheafInverseImage f (Type (u + 1))).obj F))
              (op (StructuredArrow.mk a)) ≫ (c F).hom =
        colimit.ι (proEtaleGeometricStalkDiagram (x ≫ f) F) (op N)) ∧
      (∀ (F G : Sheaf (ProEt.topology Y) (Type (u + 1))) (h : F ⟶ G),
        colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
          ((proEtaleSheafInverseImage f (Type (u + 1))).map h).hom) ≫ (c G).hom =
        (c F).hom ≫ colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom)) ∧
      (∀ (F G : Sheaf (ProEt.topology Y) (Type (u + 1))) (h k : F ⟶ G),
        (proEtaleSheafInverseImage f (Type (u + 1))).map h =
          (proEtaleSheafInverseImage f (Type (u + 1))).map k →
        colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom) =
        colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op k.hom)) := by
  sorry

/-- Geometric stalks of abelian sheaves commute with inverse image along every scheme morphism.
The first clause fixes the canonical comparison by its value on unit germs; the
second is naturality in the sheaf; the third reflects equality of inverse-image maps
at the image geometric point. The comparison is additive since it is an isomorphism
in `AddCommGrpCat`.
Source: Stacks Project, Tags 05V1, 0F4F, 0F6B, 0F6C and 0993
(blueprint: lem-pur-proetale-inverse-image-stalk).

Proof:
1. Put `P = u_{f,p} F`. A lift of `x ≫ f` to `V` pairs uniquely with `x` to
   give a lift to `u_f(V)`, by `def-pc-fibre-product`. These correspondences respect
   pointed arrows. All diagrams are small by `def-weil-size-convention`.
2. A cover of a pointed neighbourhood lifts the fixed field point to a member.
   Base change the fpqc cover (`lem-galois-fpqc-covering-base-change`); choose a
   nonempty affine fibre. Weakly etale base change and source locality reduce to
   `lem-weil-pbc-weak-etale-field`, using `def-weil-pbc-ind-etale-algebra`.
   Its residue field embeds back into the algebraically closed field by
   `lem-weil-pbc-separable-extension-embeds-separably-closed`. Transport to a skeleton.
3. In sets, local representation and local equality of sheafified sections
   (`lem-weil-pbc-site-sheafification-sections-local`), together with step 2 and
   filteredness of pointed neighbourhoods, make the stalk of the sheafification
   unit bijective, naturally in `P`.
4. In abelian groups, `lem-cbc-proetale-sheafification-geometric-stalk` gives
   the same natural isomorphism `t : P_x ≅ (f⁻¹F)_x` in abelian groups.
5. Define `a : P_x → F_{x ≫ f}` on an inner coprojection `(U,point,V,φ)` by the
   germ of its section at the lift obtained by projecting `φ(point)` to `V`.
   These maps respect the inner comma arrows and outer pointed restrictions,
   so the two colimit universal properties descend them (`def-weil-pbc-category-colimit`).
6. Define `b : F_{x ≫ f} → P_x` using `(u_f(V),paired lift,V,id)` on each
   germ. The inverse-image restriction formula identifies its restriction along
   `u_f(r)` with the coprojection `(V',u_f(r))`; the inner comma arrow from
   `(V,id)` gives compatibility, so this also descends to the colimit.
7. On original germs `ab` is the identity. On the twice-indexed coprojections,
   the pointed arrow `φ` identifies `ba` with the identity. Thus `a` and `b`
   are inverse; take `c = a t⁻¹`. This yields exactly the unit-germ equation.
8. On every inner coprojection, both naturality paths send `s` to the germ of
   `h(s)` at its projected lift. Descend twice and use naturality of `t`.
   All arrows in the abelian case are homomorphisms. Conjugating by `c` shows
   that equal inverse images give equal stalk maps at `x ≫ f`.
-/
theorem proEtaleInverseImage_abelianStalk
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ c : ∀ F : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1},
      proEtaleGeometricStalk x ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj F) ≅
        proEtaleGeometricStalk (x ≫ f) F,
      (∀ (F : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1})
        (N : ProEtaleGeometricNeighbourhood (x ≫ f))
        (a : Over.mk x ⟶ (ProEt.forget X).obj ((proEtaleBaseChange f).obj N.right)),
        a.left ≫ pullback.fst N.right.hom f = N.hom.left →
        ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app F).hom.app (op N.right) ≫
          colimit.ι (proEtaleGeometricStalkDiagram x
            ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj F))
              (op (StructuredArrow.mk a)) ≫ (c F).hom =
        colimit.ι (proEtaleGeometricStalkDiagram (x ≫ f) F) (op N)) ∧
      (∀ (F G : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}) (h : F ⟶ G),
        colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
          ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map h).hom) ≫ (c G).hom =
        (c F).hom ≫ colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom)) ∧
      (∀ (F G : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}) (h k : F ⟶ G),
        (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map h =
          (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map k →
        colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op h.hom) =
        colim.map
          (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget (x ≫ f)).op k.hom)) := by
  sorry

end AlgebraicGeometry.Scheme
