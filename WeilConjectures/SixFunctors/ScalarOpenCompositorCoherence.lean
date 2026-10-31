/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionCoherence
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization

/-! # Scalar comparison and the open-extension compositor

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Composition paragraph
(blueprint: lem-sfb-scalar-open-compositor-coherence).

The open compositor is written out as the `Adjunction.leftAdjointCompIso` of the three
derived open-immersion adjunctions and the inverse of the canonical pullback compositor
`scalarSixPullComp` of det-prop-scalar-six-pullback. This is the body of `sfbScalarOpenComp`
in `WeilConjectures.SixFunctors.ScalarCompositeModelPasting` (whose `RootCoordinateFace.upperComp` has
the same definition as `scalarSixPullComp`). That module is not imported: its node cites this
lemma as a proof dependency, so the import would close an import cycle at stage 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem scalarComposition
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {La : A ⥤ D} {Ra : D ⥤ A} {Lb : B ⥤ E} {Rb : E ⥤ B}
    {Lc : C ⥤ F} {Rc : F ⥤ C}
    {H : A ⥤ B} {S : B ⥤ A} {I : B ⥤ C} {T : C ⥤ B}
    {J : A ⥤ C} {U : C ⥤ A}
    {P : D ⥤ E} {Rp : E ⥤ D} {Q : E ⥤ F} {Rq : F ⥤ E}
    {R : D ⥤ F} {Rr : F ⥤ D}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc)
    (h : H ⊣ S) (i : I ⊣ T) (j : J ⊣ U)
    (p : P ⊣ Rp) (q : Q ⊣ Rq) (r : R ⊣ Rr)
    (α01 : Rp ⋙ Ra ≅ Rb ⋙ S) (α12 : Rq ⋙ Rb ≅ Rc ⋙ T)
    (α02 : Rr ⋙ Ra ≅ Rc ⋙ U) (β : U ≅ T ⋙ S) (γ : Rq ⋙ Rp ≅ Rr)
    (μ : J ≅ H ⋙ I) (κ : R ≅ P ⋙ Q)
    (hμ : conjugateIsoEquiv (h.comp i) j μ = β.symm)
    (hκ : conjugateIsoEquiv (p.comp q) r κ = γ)
    (hr : α02 = Functor.isoWhiskerRight γ.symm Ra ≪≫
      Functor.associator Rq Rp Ra ≪≫ Functor.isoWhiskerLeft Rq α01 ≪≫
      (Functor.associator Rq Rb S).symm ≪≫ Functor.isoWhiskerRight α12 S ≪≫
      Functor.associator Rc T S ≪≫ Functor.isoWhiskerLeft Rc β.symm)
    (K : A) :
    Lc.map (μ.inv.app K) ≫
        ((conjugateIsoEquiv (a.comp r) (j.comp c)).symm α02).hom.app K =
      ((conjugateIsoEquiv (b.comp q) (i.comp c)).symm α12).hom.app (H.obj K) ≫
        Q.map (((conjugateIsoEquiv (a.comp p) (h.comp b)).symm α01).hom.app K) ≫
          κ.inv.app (La.obj K) := by
  let t01 := (conjugateIsoEquiv (a.comp p) (h.comp b)).symm α01
  let t12 := (conjugateIsoEquiv (b.comp q) (i.comp c)).symm α12
  let t02 := (conjugateIsoEquiv (a.comp r) (j.comp c)).symm α02
  have he := adjunctionSquareComposition a b c h i j p q r
    α01 α12 α02 β γ t01.symm t12.symm t02.symm μ κ.symm
    (by simp only [t01, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply])
    (by simp only [t12, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply])
    (by simp only [t02, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]) hμ
    (by rw [conjugateIsoEquiv_iso_symm, hκ]) hr
  have he' := congrArg (fun z ↦ z.inv.app K) he
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id] at he'
  have hh := congrArg (fun z ↦ z ≫ κ.inv.app (La.obj K)) he'.symm
  simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc, Category.comp_id] using hh

set_option maxHeartbeats 800000 in
-- Keep the concrete derived square and the composite adjunctions folded.
/-- The coefficient-change comparison commutes with the canonical compositor for two
quasi-compact open immersions `j : X ⟶ B`, `i : B ⟶ C`, for every listed (possibly non-flat)
coefficient map and every unbounded derived object `A`. The compositor `ω_Λ(j,i)` is the
`Adjunction.leftAdjointCompIso` of the derived `j_! ⊣ j^*`, `i_! ⊣ i^*`, `(j ≫ i)_! ⊣ (j ≫ i)^*`
adjunctions and the inverse of the pullback compositor `scalarSixPullComp`.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Composition paragraph
(blueprint: lem-sfb-scalar-open-compositor-coherence).

Proof (functional composition):
1. Put `G_u = D(u^*)`, `G'_u = D(u^*_{Λ'})`, `R_Z = D(Res_{a_Z})`, and
   `e_u : R_{source u} G'_u ≅ G_u R_{target u}` the comparison of
   def-sfb-derived-comap-upper-star-iso; `c`, `c'` the pullback compositors. By
   def-sfb-derived-open-immersion-shriek-iso, `δ_u` is conjugate to `e_u`; by the definition of
   `ω`, `ω` is conjugate to `c`. Conjugation is def-weil-pbc-adjunction-conjugate.
2. On module sheaves, new-comap-upper-star-iso-composition for `f = j`, `g = i`, precomposed
   with `e_{ij}`, gives `e_{ij}; c R_C = R_X c'; (e_j G'_i); (G_j e_i)`.
3. Pass this square to the unbounded derived categories by
   lem-pod-derived-exact-square-composition (geometric pullbacks exact by
   det-prop-sfb-module-pullback-exact-main, restriction exact by sk-def-sfb-change-of-scalars
   (4)); the squares are the `e_u` of def-sfb-derived-comap-upper-star-iso. This gives (*).
4. By def-weil-pbc-adjunction-conjugate and lem-weil-pbc-mate-pasting (1)--(3) the conjugate of
   the left side is `e_{ij}; c R_C` and of the right side `R_X c'; e_j G'_i; G_j e_i`; (*) and
   injectivity of conjugation equate the two transformations.
5. Evaluate at `A`; no flatness of `a` was used (def-sfb-derived-open-immersion-shriek-iso). -/
theorem scalarOpenCompositorCoherence
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_ha : ListedCoefficientMap ell a)
    {X B C : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (j : X ⟶ B) (i : B ⟶ C)
    [IsOpenImmersion j.left] [QuasiCompact j.left]
    [IsOpenImmersion i.left] [QuasiCompact i.left] :
    ∀ (A : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)),
      (scalarSixChange a C.left).map
          ((Adjunction.leftAdjointCompIso
            (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j.left)
            (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X i.left)
            (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (j.left ≫ i.left))
            (scalarSixPullComp Λ j.left i.left).symm).hom.app A) ≫
        (derivedOpenImmersionShriekIso
          (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (j.left ≫ i.left)).hom.app A =
      (derivedOpenImmersionShriekIso
          (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom i.left).hom.app
          ((openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.obj A) ≫
        ((openImmersionLowerShriek Λ'.X i.left).mapDerivedCategory.map
          ((derivedOpenImmersionShriekIso
            (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j.left).hom.app A)) ≫
        (Adjunction.leftAdjointCompIso
          (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j.left)
          (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X i.left)
          (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X (j.left ≫ i.left))
          (scalarSixPullComp Λ' j.left i.left).symm).hom.app
          ((scalarSixChange a X.left).obj A) := by
  intro A
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  let sx := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)
  let sb := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom B.left)
  let sc := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom C.left)
  let hj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j.left
  let hi := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X i.left
  let hc := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (j.left ≫ i.left)
  let pj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j.left
  let pi := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X i.left
  let pc := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X (j.left ≫ i.left)
  let w := Adjunction.leftAdjointCompIso hj hi hc (scalarSixPullComp Λ j.left i.left).symm
  let w' := Adjunction.leftAdjointCompIso pj pi pc (scalarSixPullComp Λ' j.left i.left).symm
  have hr : derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom (j.left ≫ i.left) =
      Functor.isoWhiskerRight (scalarSixPullComp Λ' j.left i.left)
        (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
          a.hom.hom X.left)).mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (scalarSixPull Λ' i.left)
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom i.left)
        (scalarSixPull Λ j.left) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom C.left)).mapDerivedCategory
        (scalarSixPullComp Λ j.left i.left).symm := by
    apply Iso.ext_inv
    apply NatTrans.ext
    funext N
    simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
      Category.comp_id]
    have hh := congrArg (fun z ↦ z ≫
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
        a.hom.hom X.left)).mapDerivedCategory.map
          ((scalarSixPullComp Λ' j.left i.left).inv.app N))
      (scalarSixRestrictionComp a j.left i.left N)
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hh
    rw [(Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom X.left)).mapDerivedCategory.map_id
        ((scalarSixPull Λ' (j.left ≫ i.left)).obj N)] at hh
    erw [Category.comp_id] at hh
    simpa only [Category.assoc] using hh
  have h := scalarComposition sx sb sc hj hi hc pj pi pc
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j.left)
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom i.left)
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom (j.left ≫ i.left))
    (scalarSixPullComp Λ j.left i.left) (scalarSixPullComp Λ' j.left i.left).symm
    w.symm w'.symm
    (by
      dsimp only [w, Adjunction.leftAdjointCompIso]
      exact Equiv.apply_symm_apply _ _)
    (by
      dsimp only [w', Adjunction.leftAdjointCompIso]
      exact Equiv.apply_symm_apply _ _)
    hr A
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
