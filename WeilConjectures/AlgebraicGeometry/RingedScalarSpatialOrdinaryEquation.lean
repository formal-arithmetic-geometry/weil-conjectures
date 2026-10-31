/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementData
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition

/-! # Ordinary scalar/spatial inverse-image coherence

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D
(`lemma-derived-pullback-composition`) and Tag 0FPI
(`lemma-adjoints-push-pull-compatibility`); agent ordinary section/conjugate
calculation, Steps 1--2 of the parent proof.
(blueprint: new-ringed-scalar-spatial-ordinary-equation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.RingedRefinement

/-- The ordinary scalar comparison `sc.ordinary` commutes with the ordinary spatial
compositor `p.ordinaryComp` on module sheaves, functor associators displayed:
`q_{gf} ∘ (α^B_{f,g} E_W) = (E_U α^A_{f,g}) ∘ (q_f F_g^A) ∘ (F_f^B q_g)`.

Source: Stacks, sites-cohomology.tex, Tags 0D6D and 0FPI; agent calculation.

Proof. Write `F^R_f`, `H^R_f` for ordinary pullback and its right adjoint
(`moduleAdjunction`), `E_W ⊣ r_W` for `sc.ordinaryAdjunction`, `ρ_f = sc.restriction f a`
and `β^R_{f,g} = p.comp f g R`.
1. The right-adjoint rectangle `ρ_{gf} ∘ (β^A_{f,g} r_U) = (r_W β^B_{f,g}) ∘ (ρ_g H^B_f) ∘
(H^A_g ρ_f)` holds: on a `B_U`-module `N` and a test object `Z` over `W`, each `ρ` is the
identity on sections (`restriction_sections`) and each `β` is `N` applied to the opposite of
`siteComp m f g` at `Z` (`comp_sections`); scalar restriction leaves the underlying additive
maps unchanged, so both sides send `x` to `N(siteComp_Z^op) x`. Equal on all sections, the two
module maps are equal. In systems mode the test objects are the pairs `(n, Z)` and `siteComp`
is the identity on `n`, so the same computation applies.
2. By `ordinary_mate`, `q_f⁻¹` has conjugate `ρ_f⁻¹` for the composite scalar/geometric
adjunctions, and by the definition of `Spatial.ordinaryComp`, `(α^{R,0}_{f,g})⁻¹` has
conjugate `β^R_{f,g}`. The pasting and change-of-adjunction formulas for conjugates
(`conjugateEquiv_comp`, `conjugateEquiv_whiskerLeft/Right`; blueprint
lem-weil-pbc-mate-pasting) send the inverses of the two sides of the claimed equation to
the two sides of Step 1. Conjugation is a bijection carrying inverses to inverses
(def-weil-pbc-adjunction-conjugate), so the claimed equation holds.
(blueprint: new-ringed-scalar-spatial-ordinary-equation) -/
theorem ordinaryScalarSpatialEquation
    (m : SheafOfModules.OpenTensorNormalization.Mode) (T : Scheme.{u})
    (c : Coefficients m T) (o : Calculus c)
    (p : Spatial o) (sc : ScalarComparisons o)
    {A B : Rings m T} (a : A ⟶ B) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) :
    (Functor.associator (o.scalar W a).E
      (o.operation g B).pullback (o.operation f B).pullback).hom ≫
        Functor.whiskerLeft (o.scalar W a).E ((p.ordinaryComp f g B).hom) ≫
        (sc.ordinary (f ≫ g) a).hom =
      Functor.whiskerRight (sc.ordinary g a).hom (o.operation f B).pullback ≫
        (Functor.associator (o.operation g A).pullback
          (o.scalar V a).E (o.operation f B).pullback).hom ≫
        Functor.whiskerLeft (o.operation g A).pullback (sc.ordinary f a).hom ≫
        (Functor.associator (o.operation g A).pullback
          (o.operation f A).pullback (o.scalar U a).E).inv ≫
        Functor.whiskerRight ((p.ordinaryComp f g A).hom)
          (o.scalar U a).E := by
  let r (X : Over T) := restrictScalars
    ((sheafCompose (SheafOfModules.OpenTensorNormalization.topology m X.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map ((c.rings X).map a))
  have hr :
      Functor.whiskerLeft (r U) (p.comp f g A).hom ≫ (sc.restriction (f ≫ g) a).hom =
        Functor.whiskerRight (sc.restriction f a).hom (o.operation g A).pushforward ≫
          Functor.whiskerLeft (o.operation f B).pushforward (sc.restriction g a).hom ≫
            Functor.whiskerRight (p.comp f g B).hom (r W) := by
    ext N Z x
    have hf := eq_of_heq (sc.restriction_sections f a N
      ((SheafOfModules.OpenTensorNormalization.baseChange m g.left).op.obj Z) x)
    have hg := eq_of_heq (sc.restriction_sections g a
      ((o.operation f B).pushforward.obj N) Z x)
    have hfg := sc.restriction_sections (f ≫ g) a N Z
    have hA := p.comp_sections f g A ((r U).obj N) Z
    have hB := p.comp_sections f g B N Z
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    change (((sc.restriction (f ≫ g) a).hom.app N).val.app Z)
        ((((p.comp f g A).hom.app ((r U).obj N)).val.app Z) x) =
      (((p.comp f g B).hom.app N).val.app Z)
        ((((sc.restriction g a).hom.app ((o.operation f B).pushforward.obj N)).val.app Z)
          ((((sc.restriction f a).hom.app N).val.app
            ((SheafOfModules.OpenTensorNormalization.baseChange m g.left).op.obj Z)) x))
    rw [hf, hg]
    have hA' := eq_of_heq hA
    have hB' := eq_of_heq hB
    rw [hA']
    rw [eq_of_heq (hfg _)]
    exact (congrFun hB' x).symm
  have hm (X Y : Over T) (k : X ⟶ Y) :
      conjugateIsoEquiv
        ((o.operation k A).moduleAdjunction.comp (sc.ordinaryAdjunction X a))
        ((sc.ordinaryAdjunction Y a).comp (o.operation k B).moduleAdjunction)
        (sc.ordinary k a) = sc.restriction k a := by
    exact congrArg Iso.symm (sc.ordinary_mate k a)
  have hc (R : Rings m T) :
      conjugateIsoEquiv
        ((o.operation g R).moduleAdjunction.comp (o.operation f R).moduleAdjunction)
        (o.operation (f ≫ g) R).moduleAdjunction
        (p.ordinaryComp f g R).symm = p.comp f g R := by
    exact (conjugateIsoEquiv _ _).apply_symm_apply _
  have hcompat : (sc.restriction (f ≫ g) a).symm =
      Functor.isoWhiskerRight (p.comp f g B).symm (r W) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (o.operation f B).pushforward (sc.restriction g a).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sc.restriction f a).symm (o.operation g A).pushforward ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (r U) (p.comp f g A) := by
    apply Iso.symm_bijective.injective
    apply Iso.ext
    apply (cancel_epi (Functor.whiskerLeft (r U) (p.comp f g A).hom)).1
    apply NatTrans.ext
    funext N
    simpa using congrArg (fun t ↦ t.app N) hr
  have h := adjunctionSquareComposition
    (sc.ordinaryAdjunction W a) (sc.ordinaryAdjunction V a) (sc.ordinaryAdjunction U a)
    (o.operation g A).moduleAdjunction (o.operation f A).moduleAdjunction
    (o.operation (f ≫ g) A).moduleAdjunction
    (o.operation g B).moduleAdjunction (o.operation f B).moduleAdjunction
    (o.operation (f ≫ g) B).moduleAdjunction
    (sc.restriction g a).symm (sc.restriction f a).symm
    (sc.restriction (f ≫ g) a).symm (p.comp f g A).symm (p.comp f g B)
    (sc.ordinary g a) (sc.ordinary f a) (sc.ordinary (f ≫ g) a)
    (p.ordinaryComp f g A).symm (p.ordinaryComp f g B)
    (hm _ _ g) (hm _ _ f) (hm _ _ (f ≫ g)) (hc A) (congrArg Iso.symm (hc B)) hcompat
  have hh := congrArg Iso.hom h
  have hh' := congrArg
    (fun t ↦ t ≫ Functor.whiskerRight (p.ordinaryComp f g A).hom (o.scalar U a).E) hh
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Category.assoc,
    ← Functor.whiskerRight_comp, Iso.inv_hom_id, Functor.whiskerRight_id',
    Category.comp_id] using hh'.symm

end SheafOfModules.RingedRefinement
