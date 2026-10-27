/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteDirectImageComposition
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Transport through a scheme isomorphism and ordinary derived transposes

Source: Stacks Project, Tags 0D6D and 0D6E; the proper symmetry paragraph of
blueprint lem-sf-kunneth-coherence.proof.md
(blueprint: lem-pur-ordinary-derived-isomorphism-transport-transpose).

The fixed-scalar sheaf presentation is the one used by finiteDirectImageComposition.
Its pullback and adjunction are the published canonical finite-coefficient operations.
All inputs belong to the ordinary unbounded derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

private theorem mapDerivedAdjunction_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) := by
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  refine (adj.mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
      _ _ _ (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ?_
  ext Z
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [← (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

private theorem derivedComposition_conjugate (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (finiteDirectImageComposition A f g).inv =
      conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom := by
  let := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  have h := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
    (lowerStarComp (ModuleCat.{u + 1} A) f g)
    (upperStarComp (ModuleCat.{u + 1} A) f g)
    (conjugateEquiv_upperStarComp_hom (ModuleCat.{u + 1} A) f g).symm
  change (Functor.rightDerivedFunctorCompIso' _ _ _).hom = _
  rw [h, mapDerivedAdjunction_eq, mapDerivedAdjunction_eq, mapDerivedAdjunction_eq]
  ext K
  simp [conjugateEquiv_apply_app, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

/-- The specified direct-image transport: apply Rq to the actual unit of s,
then the inverse finite-level compositor, then Rc to d.
Source: Stacks Tag 0D6E; blueprint proper product symmetry
(blueprint: lem-pur-ordinary-derived-isomorphism-transport-transpose). -/
def ordinaryDerivedIsomorphismTransport (P : PurityFiniteSetting.{u})
    {B X X' : Scheme.{u}} (s : X ≅ X') (q : X' ⟶ B)
    (K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (d : L(upperStar (ModuleCat.{u + 1} P.Coefficient) s.hom).obj K' ≅ K) :
    R(lowerStar (ModuleCat.{u + 1} P.Coefficient) q).obj K' ⟶
      R(lowerStar (ModuleCat.{u + 1} P.Coefficient) (s.hom ≫ q)).obj K :=
  R(lowerStar (ModuleCat.{u + 1} P.Coefficient) q).map
      ((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) s.hom).unit.app K') ≫
    (finiteDirectImageComposition P.Coefficient s.hom q).inv.app
      (L(upperStar (ModuleCat.{u + 1} P.Coefficient) s.hom).obj K') ≫
    R(lowerStar (ModuleCat.{u + 1} P.Coefficient) (s.hom ≫ q)).map d.hom

/-- Transport along s is invertible, and the transpose of its composite with any u
is d after Ps of the old transpose and the canonical pullback compositor.
Source: Stacks Tags 0D6D and 0D6E; blueprint proper product symmetry
(blueprint: lem-pur-ordinary-derived-isomorphism-transport-transpose).

Proof: (1) The source-library right-derived composition conjugacy theorem identifies
finiteDirectImageComposition.inv with the conjugate of leftDerivedUpperStarComp.hom.
To use the actual left-derived adjunctions, first compare their exact-pullback
normalization with the adjunctions for the termwise derived functors, using the
normalization of leftDerivedUpperStarIsoMapDerivedCategory.
(2) Conjugacy gives the composite counit equation for precisely this compositor.
Expand transport, use counit naturality at d, and move the pullback compositor
past u and the image of the s-unit by naturality.
(3) Counit naturality for q at the s-unit, followed by the left triangle identity
for the actual s-adjunction, leaves exactly d after Ps of the q-transpose.
(4) Pullback along a scheme isomorphism is an exact equivalence. Its termwise
unbounded derived functor is fully faithful, and the exact-pullback comparison
transfers full faithfulness to the actual left-derived functor. The actual unit
is therefore invertible. Functors preserve isomorphisms, so all three factors of
transport are invertible. -/
theorem ordinaryDerivedIsomorphismTransport_transpose (P : PurityFiniteSetting.{u})
    {B X X' : Scheme.{u}}
    [B.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [X'.Over (Spec (.of P.field.k))]
    [IsSeparated (B ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    (s : X ≅ X') (q : X' ⟶ B)
    (K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (d : L(upperStar (ModuleCat.{u + 1} P.Coefficient) s.hom).obj K' ≅ K) :
    IsIso (ordinaryDerivedIsomorphismTransport P s q K' K d) ∧
      ∀ (M : DerivedCategory
          (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)))
        (u : M ⟶ R(lowerStar (ModuleCat.{u + 1} P.Coefficient) q).obj K'),
        L(upperStar (ModuleCat.{u + 1} P.Coefficient) (s.hom ≫ q)).map
            (u ≫ ordinaryDerivedIsomorphismTransport P s q K' K d) ≫
          (derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} P.Coefficient) (s.hom ≫ q)).counit.app K =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) s.hom q).hom.app M ≫
          L(upperStar (ModuleCat.{u + 1} P.Coefficient) s.hom).map
            (L(upperStar (ModuleCat.{u + 1} P.Coefficient) q).map u ≫
              (derivedUpperStarLowerStarAdjunction
                (ModuleCat.{u + 1} P.Coefficient) q).counit.app K') ≫ d.hom := by
  let A := ModuleCat.{u + 1} P.Coefficient
  have ff := (Functor.FullyFaithful.ofFullyFaithful
    (upperStar A s.hom).mapDerivedCategory).ofIso
    (leftDerivedUpperStarIsoMapDerivedCategory A s.hom).symm
  have := ff.full
  have := ff.faithful
  constructor
  · unfold ordinaryDerivedIsomorphismTransport
    infer_instance
  · intro M u
    let F := L(upperStar A s.hom)
    let G := L(upperStar A q)
    let H := L(upperStar A (s.hom ≫ q))
    let Rs := R(lowerStar A s.hom)
    let Rq := R(lowerStar A q)
    let Rc := R(lowerStar A (s.hom ≫ q))
    let a := derivedUpperStarLowerStarAdjunction A s.hom
    let b := derivedUpperStarLowerStarAdjunction A q
    let c := derivedUpperStarLowerStarAdjunction A (s.hom ≫ q)
    let α := leftDerivedUpperStarComp A s.hom q
    let κ := finiteDirectImageComposition P.Coefficient s.hom q
    have hε (E) : H.map (κ.inv.app E) ≫ c.counit.app E =
        α.hom.app (Rq.obj (Rs.obj E)) ≫
          F.map (b.counit.app (Rs.obj E)) ≫ a.counit.app E := by
      dsimp only [κ]
      rw [derivedComposition_conjugate]
      simpa only [A, F, G, H, Rs, Rq, Rc, a, b, c, α,
        Adjunction.comp_counit_app, Functor.comp_obj, Category.assoc] using
        conjugateEquiv_counit (b.comp a) c α.hom E
    change H.map (u ≫ Rq.map (a.unit.app K') ≫ κ.inv.app (F.obj K') ≫
      Rc.map d.hom) ≫ c.counit.app K =
        α.hom.app M ≫ F.map (G.map u ≫ b.counit.app K') ≫ d.hom
    simp only [Functor.map_comp, Category.assoc]
    have hc : H.map (Rc.map d.hom) ≫ c.counit.app K =
        c.counit.app (F.obj K') ≫ d.hom := c.counit.naturality d.hom
    rw [hc]
    rw [← Category.assoc (H.map (κ.inv.app (F.obj K'))), hε]
    simp only [Category.assoc]
    erw [α.hom.naturality_assoc, α.hom.naturality_assoc]
    simp only [Functor.comp_map]
    have hb : G.map (Rq.map (a.unit.app K')) ≫
        b.counit.app (Rs.obj (F.obj K')) = b.counit.app K' ≫ a.unit.app K' :=
      b.counit.naturality (a.unit.app K')
    change α.hom.app M ≫ F.map (G.map u) ≫ F.map (G.map (Rq.map (a.unit.app K'))) ≫
      F.map (b.counit.app (Rs.obj (F.obj K'))) ≫ a.counit.app (F.obj K') ≫ d.hom = _
    rw [← F.map_comp_assoc (G.map (Rq.map (a.unit.app K'))), hb]
    simp only [Functor.map_comp, Category.assoc]
    have ha : F.map (a.unit.app K') ≫ a.counit.app (F.obj K') = 𝟙 _ :=
      a.left_triangle_components K'
    rw [← Category.assoc (F.map (a.unit.app K')), ha]
    simp

end WeilConjectures.PurityFiniteSetting
