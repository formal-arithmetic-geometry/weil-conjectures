/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptional
public import WeilConjectures.AlgebraicGeometry.Compact.CompactCoefficientComposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek

/-!
# Finite coefficient reduction preserves the canonical exceptional mates

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 2 and 4
(blueprint: lem-pur-finite-adjoint-mate-compatibility).

The first three clauses are written in the canonical etale-origin coordinates of
`def-pur-co-smoothness`. Every bounded constructible pro-etale object has such an
origin. Comparison is fully faithful there, preserves the Tor interval, and identifies
pullback, tensor, compact supports and the constructible exceptional adjunction.
Consequently these are equations of the specified pro-etale maps for every input,
independently of its origin witness. The last clause uses the recorded intrinsic
pro-etale finite-Tor subcategories and their normalized adjunction directly.

## Main statements

* `PurityFiniteSetting.finite_adjoint_mate_tensor`: the canonical tensor-map square.
* `PurityFiniteSetting.finite_adjoint_mate_composition`: the exceptional compositor square.
* `PurityFiniteSetting.finite_adjoint_mate_baseChange`: every Cartesian extraordinary square.
* `FiniteExceptional.finite_adjoint_mate_transpose`: the transpose of every morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar

section CompositionMate
universe v w
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type w}
  [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
  [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
  {Lf : C₀ ⥤ C₁} {Rf : C₁ ⥤ C₀} {Lg : C₁ ⥤ C₂} {Rg : C₂ ⥤ C₁}
  {Lh : C₀ ⥤ C₂} {Rh : C₂ ⥤ C₀}
  {Lf' : D₀ ⥤ D₁} {Rf' : D₁ ⥤ D₀} {Lg' : D₁ ⥤ D₂} {Rg' : D₂ ⥤ D₁}
  {Lh' : D₀ ⥤ D₂} {Rh' : D₂ ⥤ D₀}
  {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A coherent left-adjoint coefficient composition square induces the right-mate square.
The composite mate has the composite counit equation by naturality of the first counit.
Apply pointwise coefficient exchange to the two adjunction compositors and remove the
identity horizontal functors. Source: reduction proof Step 2, compatibility with
exceptional composition (blueprint: lem-pur-finite-adjoint-mate-compatibility). -/
private theorem finiteMate_composition
    (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (ah : Lh ⊣ Rh)
    (bf : Lf' ⊣ Rf') (bg : Lg' ⊣ Rg') (bh : Lh' ⊣ Rh')
    (p : Lf ⋙ Lg ≅ Lh) (p' : Lf' ⋙ Lg' ≅ Lh')
    (qf : Lf ⋙ Q₁ ≅ Q₀ ⋙ Lf') (qg : Lg ⋙ Q₂ ≅ Q₁ ⋙ Lg')
    (qh : Lh ⋙ Q₂ ≅ Q₀ ⋙ Lh')
    (K : C₂)
    (δf : Q₀.obj (Rf.obj (Rg.obj K)) ⟶ Rf'.obj (Q₁.obj (Rg.obj K)))
    (δg : Q₁.obj (Rg.obj K) ⟶ Rg'.obj (Q₂.obj K))
    (δh : Q₀.obj (Rh.obj K) ⟶ Rh'.obj (Q₂.obj K))
    (hδf : Lf'.map δf ≫ bf.counit.app (Q₁.obj (Rg.obj K)) =
      qf.inv.app (Rf.obj (Rg.obj K)) ≫ Q₁.map (af.counit.app (Rg.obj K)))
    (hδg : Lg'.map δg ≫ bg.counit.app (Q₂.obj K) =
      qg.inv.app (Rg.obj K) ≫ Q₂.map (ag.counit.app K))
    (hδh : Lh'.map δh ≫ bh.counit.app (Q₂.obj K) =
      qh.inv.app (Rh.obj K) ≫ Q₂.map (ah.counit.app K))
    (hc : Q₂.map (p.hom.app (Rh.obj K)) ≫ qh.hom.app (Rh.obj K) =
      qg.hom.app (Lf.obj (Rh.obj K)) ≫ Lg'.map (qf.hom.app (Rh.obj K)) ≫
        p'.hom.app (Q₀.obj (Rh.obj K))) :
    Q₀.map ((conjugateIsoEquiv ah (af.comp ag) p).hom.app K) ≫
        δf ≫ Rf'.map (δg) =
      δh ≫ (conjugateIsoEquiv bh (bf.comp bg) p').hom.app (Q₂.obj K) := by
  let qp : (Lf ⋙ Lg) ⋙ Q₂ ≅ Q₀ ⋙ (Lf' ⋙ Lg') :=
    Functor.associator Lf Lg Q₂ ≪≫ Functor.isoWhiskerLeft Lf qg ≪≫
      (Functor.associator Lf Q₁ Lg').symm ≪≫ Functor.isoWhiskerRight qf Lg' ≪≫
        Functor.associator Q₀ Lf' Lg'
  have hp :
      (Lf' ⋙ Lg').map (δf ≫ Rf'.map (δg)) ≫
        (bf.comp bg).counit.app (Q₂.obj K) =
      qp.inv.app ((Rg ⋙ Rf).obj K) ≫ Q₂.map ((af.comp ag).counit.app K) := by
    have hn := bf.counit.naturality (δg)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
    have hn' := congrArg Lg'.map hn
    simp only [Functor.map_comp] at hn'
    simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp,
      Adjunction.comp_counit_app, Category.assoc]
    rw [reassoc_of% hn', ← Lg'.map_comp_assoc, hδf, Lg'.map_comp,
      Category.assoc, hδg]
    have hq := qg.inv.naturality (af.counit.app (Rg.obj K))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hq
    simp only [qp, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    rw [reassoc_of% hq]
  have hcube : Adjunction.coefficientPullbackSquare
      (TwoSquare.mk (𝟭 C₀) Lh (Lf ⋙ Lg) (𝟭 C₂) p.hom)
      (TwoSquare.mk (𝟭 D₀) Lh' (Lf' ⋙ Lg') (𝟭 D₂) p'.hom)
      qh qp (Q₀.leftUnitor.hom ≫ Q₀.rightUnitor.inv)
      (Q₂.leftUnitor.hom ≫ Q₂.rightUnitor.inv) (Rh.obj K) := by
    simpa only [Adjunction.coefficientPullbackSquare, qp, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.id_map, Functor.comp_map, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id,
      Functor.comp_obj, Functor.id_obj, TwoSquare.mk, Category.assoc] using hc
  have hh := Adjunction.coefficient_exchange_of_counit_at ah (af.comp ag) bh (bf.comp bg)
    (TwoSquare.mk (𝟭 C₀) Lh (Lf ⋙ Lg) (𝟭 C₂) p.hom)
    (TwoSquare.mk (𝟭 D₀) Lh' (Lf' ⋙ Lg') (𝟭 D₂) p'.hom) K
    ((conjugateEquiv ah (af.comp ag) p.hom).app K)
    ((conjugateEquiv bh (bf.comp bg) p'.hom).app (Q₂.obj K))
    (conjugateEquiv_counit ah (af.comp ag) p.hom K)
    (conjugateEquiv_counit bh (bf.comp bg) p'.hom (Q₂.obj K))
    qh qp (Q₀.leftUnitor.hom ≫ Q₀.rightUnitor.inv)
    (Q₂.leftUnitor.hom ≫ Q₂.rightUnitor.inv) (δh)
    (δf ≫ Rf'.map (δg)) hδh hp hcube
  have hi₀ : (Q₀.leftUnitor.hom ≫ Q₀.rightUnitor.inv).app (Rh.obj K) =
      𝟙 (Q₀.obj (Rh.obj K)) := by simp
  have hi₂ : (Q₂.leftUnitor.hom ≫ Q₂.rightUnitor.inv).app K = 𝟙 (Q₂.obj K) := by simp
  rw [hi₀, hi₂, (Rg' ⋙ Rf').map_id (Q₂.obj K), Functor.id_map] at hh
  have he := Category.id_comp
    (δh ≫ (conjugateEquiv bh (bf.comp bg) p'.hom).app (Q₂.obj K))
  have he' := Category.comp_id
    (Q₀.map ((conjugateEquiv ah (af.comp ag) p.hom).app K) ≫ (δf ≫ Rf'.map δg))
  have hh' := he.symm.trans (hh.trans ((Category.assoc _ _ _).symm.trans he'))
  simpa only [conjugateIsoEquiv_apply_hom] using hh'.symm

end CompositionMate

namespace WeilConjectures

namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u}) (m : ℕ+) (hmn : (m : ℕ) ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

variable [Xsep : IsSeparated (X ↘ Spec (.of P.field.k))]
variable [Ysep : IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [fbase : f.IsOver (Spec (.of P.field.k))]

include Xsep Ysep fbase

include P m hmn in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] Etale.rightDerivedUpperShriekAdjunction
  Etale.rightDerivedUpperShriek
  Etale.unboundedEtaleLowerShriekCompIso in
attribute [-instance] CategoryTheory.catToReflQuiver in
end PurityFiniteSetting

namespace FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
variable {T U : Scheme.{u}}
  [T.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  [IsSeparated (T ↘ Spec (.of D.k))] [IsSeparated (U ↘ Spec (.of D.k))]
variable (h : T ⟶ U) [h.IsOver (Spec (.of D.k))]
  [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] (c : Compactification h)

end FiniteExceptional
end WeilConjectures
