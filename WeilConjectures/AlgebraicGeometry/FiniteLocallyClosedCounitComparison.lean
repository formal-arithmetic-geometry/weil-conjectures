/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedCounitComparison
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Derived.DerivedImmersionComparisonNormalization
import WeilConjectures.AlgebraicGeometry.FiniteDualityClosedComparisonGeneral
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# The specified locally closed counit mate for arbitrary finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-weil-finite-duality-site-comparison.proof.md, paragraph 2, locally closed sentence;
Wei Yang #1441 item 28 and #1423
(blueprint: lem-sf-locally-closed-counit-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

private theorem counit_mate_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R R' : D ⥤ C} {P : E ⥤ F} {Q Q' : F ⥤ E}
    (a : L ⊣ R) (a' : L ⊣ R') (b : P ⊣ Q) (b' : P ⊣ Q')
    (X : C ⥤ E) (Y : D ⥤ F)
    (d : L ⋙ Y ≅ X ⋙ P) (M : D) :
    b.homEquiv _ _ (d.inv.app (R.obj M) ≫ Y.map (a.counit.app M)) ≫
        (b.rightAdjointUniq b').hom.app (Y.obj M) =
      X.map ((a.rightAdjointUniq a').hom.app M) ≫
        b'.homEquiv _ _ (d.inv.app (R'.obj M) ≫ Y.map (a'.counit.app M)) := by
  apply (b'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.rightAdjointUniq_hom_app_counit]
  dsimp only [Functor.id_obj]
  rw [← b.homEquiv_counit, Equiv.symm_apply_apply]
  rw [← b'.homEquiv_counit, Equiv.symm_apply_apply]
  have hd := d.inv.naturality ((a.rightAdjointUniq a').hom.app M)
  dsimp only [Functor.comp_map] at hd
  rw [← Category.assoc, hd, Category.assoc, ← Y.map_comp,
    Adjunction.rightAdjointUniq_hom_app_counit]

private theorem open_counit_mate_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} [IsLocallyNoetherian T] [CompactSpace T]
    (v : V ⟶ T) [IsOpenImmersion v]
    (M : Etale.DerivedCategoryModule A T) :
    IsIso (((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction).homEquiv _ _
      ((derivedImmersionOpenExtensionComparison A v).inv.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj M) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
          (((Etale.openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction).counit.app M))) := by
  let X := (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory
  let Y := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let a := derivedImmersionOpenEtaleAdjunction A v
  let b := derivedImmersionOpenProEtaleAdjunction A v
  let a' := (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction
  let b' := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) v).mapDerivedCategoryAdjunction
  let d := derivedImmersionOpenExtensionComparison A v
  have he : b.homEquiv _ _
      (d.inv.app ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) v
        ).mapDerivedCategory.obj M) ≫ Y.map (a.counit.app M)) =
      (derivedImmersionOpenPullbackComparison A v).hom.app M := by
    apply (b.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    have hc := (derivedImmersionOpen_normalization A v).2.1 M
    exact ((cancel_epi (d.hom.app _)).1 (by simpa [d, Y, Category.assoc] using hc)).symm
  have ht := counit_mate_transport a a' b b' X Y d M
  rw [he] at ht
  have hi : IsIso (X.map ((a.rightAdjointUniq a').hom.app M) ≫
      b'.homEquiv _ _ (d.inv.app _ ≫ Y.map (a'.counit.app M))) := by
    rw [← ht]
    infer_instance
  exact (isIso_comp_left_iff _ _).1 hi


private theorem direct_image_delta_refl
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V : Scheme.{u}} (c : S ⟶ V) [IsClosedImmersion c]
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    finiteDualityClosedComparisonDelta c L.obj L (Iso.refl _) =
      (fixedDirectImageComparisonIso A c).hom.app L := by
  simp only [finiteDualityClosedComparisonDelta, fixedDirectImageComparisonIso,
    Iso.refl_hom, Iso.refl_inv,
    Functor.map_comp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc, asIso_hom]
  dsimp only [Etale.rightDerivedLowerStar]
  repeat erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]

private theorem closed_counit_mate_isIso
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hchar : ringChar k ≠ ell)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ell : A) ^ n = 0)
    {S V : Scheme.{u}} (aS : S ⟶ Spec (.of k)) (aV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    [LocallyOfFiniteType aV] [QuasiCompact aV] [IsSeparated aV]
    [IsNoetherian V] (c : S ⟶ V) [IsClosedImmersion c]
    (hs : c ≫ aV = aS) (a : LocallyClosedComparisonAdjoints A c)
    (N : Etale.BoundedConstructibleDerivedCategory A V)
    (hN : DerivedCategory.TStructure.t.plus (a.etale.obj N.obj)) :
    IsIso (a.proetaleAdjunction.homEquiv _ _
      ((fixedDirectImageComparisonIso A c).inv.app ⟨a.etale.obj N.obj, hN⟩ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.map
          (a.etaleAdjunction.counit.app N.obj))) := by
  let U : V.Opens := ⟨(Set.range c.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding c).isClosed_range.isOpen_compl⟩
  have hij : IsCompl (Set.range c.base) (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have hc := finiteDualityClosedComparisonGeneral ell k hbase hchar A
    (by obtain ⟨n, hn⟩ := hA; exact ⟨n, by simpa [nsmul_eq_mul] using hn⟩)
    V S U aV aS c U.ι hs hij N.obj N.property
  let RE := Etale.rightDerivedLowerStar (ModuleCat.{u + 1} A) c
  letI : RE.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A c
  let a0 := Adjunction.ofIsLeftAdjoint RE
  let b0 := derivedLowerStarClosedUpperShriekAdjunction (R := A) c U.ι hij
  let X := (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory
  let Y := (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory
  obtain ⟨L, ⟨e⟩⟩ := hc.1
  have h0 : DerivedCategory.TStructure.t.plus (RE.rightAdjoint.obj N.obj) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso e.symm L.property
  let H0 : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨RE.rightAdjoint.obj N.obj, h0⟩
  let H : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨a.etale.obj N.obj, hN⟩
  have hi0 := (hc.2 H0 (Iso.refl _)).1
  have hd0 := direct_image_delta_refl A c H0
  have hi : IsIso (b0.homEquiv _ _
      ((fixedDirectImageComparisonIso A c).inv.app H0 ≫ Y.map (a0.counit.app N.obj))) := by
    have hdi : (asIso (finiteDualityClosedComparisonDelta c H0.obj H0
        (Iso.refl _))).inv = (fixedDirectImageComparisonIso A c).inv.app H0 := by
      apply (cancel_epi (finiteDualityClosedComparisonDelta c H0.obj H0 (Iso.refl _))).1
      change (asIso (finiteDualityClosedComparisonDelta c H0.obj H0 (Iso.refl _))).hom ≫
        (asIso (finiteDualityClosedComparisonDelta c H0.obj H0 (Iso.refl _))).inv = _
      rw [Iso.hom_inv_id, hd0, Iso.hom_inv_id_app]
      rfl
    change IsIso (b0.homEquiv _ _
      ((asIso (finiteDualityClosedComparisonDelta c H0.obj H0 (Iso.refl _))).inv ≫
        Y.map (a0.counit.app N.obj))) at hi0
    rwa [hdi] at hi0
  let r := a0.rightAdjointUniq a.etaleAdjunction
  let q := b0.rightAdjointUniq a.proetaleAdjunction
  have ht : b0.homEquiv _ _
      ((fixedDirectImageComparisonIso A c).inv.app H0 ≫ Y.map (a0.counit.app N.obj)) ≫
        q.hom.app (Y.obj N.obj) =
      X.map (r.hom.app N.obj) ≫ a.proetaleAdjunction.homEquiv _ _
        ((fixedDirectImageComparisonIso A c).inv.app H ≫
          Y.map (a.etaleAdjunction.counit.app N.obj)) := by
    apply (a.proetaleAdjunction.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm]
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      q, Adjunction.rightAdjointUniq_hom_app_counit]
    dsimp only [Functor.id_obj]
    rw [← b0.homEquiv_counit, Equiv.symm_apply_apply]
    rw [← a.proetaleAdjunction.homEquiv_counit,
      Equiv.symm_apply_apply]
    let f : H0 ⟶ H := ObjectProperty.homMk (r.hom.app N.obj)
    have hd := (fixedDirectImageComparisonIso A c).inv.naturality f
    change (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.map
        (X.map (r.hom.app N.obj)) ≫ (fixedDirectImageComparisonIso A c).inv.app H =
      (fixedDirectImageComparisonIso A c).inv.app H0 ≫
        Y.map (RE.map (r.hom.app N.obj)) at hd
    rw [← Category.assoc, hd, Category.assoc, ← Y.map_comp]
    exact (congrArg (fun z ↦ (fixedDirectImageComparisonIso A c).inv.app H0 ≫ Y.map z)
      (a0.rightAdjointUniq_hom_app_counit a.etaleAdjunction N.obj)).symm
  have hi' : IsIso (X.map (r.hom.app N.obj) ≫ a.proetaleAdjunction.homEquiv _ _
      ((fixedDirectImageComparisonIso A c).inv.app H ≫
        Y.map (a.etaleAdjunction.counit.app N.obj))) := by
    rw [← ht]
    letI := hi
    infer_instance
  exact (isIso_comp_left_iff _ _).1 hi'

/-- The specified counit mate is invertible for every bounded constructible input,
for arbitrary finite commutative ell-primary coefficients and every supplied pair
of ambient closed adjunctions. The morphism is the existing `locallyClosedCounitMate`:
its component is the pro-etale pasted-adjunction transpose of the inverse of
`locallyClosedExtensionComparison` followed by comparison applied to the etale counit.
The comparison Delta uses the named closed direct-image mate and open extension map.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-weil-finite-duality-site-comparison.proof.md, paragraph 2, locally closed sentence;
Wei Yang #1441 item 28 and #1423
(blueprint: lem-sf-locally-closed-counit-comparison).

Proof: finite type over the field makes S and T Noetherian. Open restriction makes V
Noetherian and separated of finite type, and carries M to a bounded constructible N.
Apply the closed exceptional comparison to c and N. Transport its closed adjunctions
and specified direct-image comparison to the supplied adjoints by the unique
counit-compatible right-adjoint isomorphisms. Compose its invertible closed comparison
alpha with I_p applied to the canonical open restriction comparison b, obtaining g.
The closed counit identity, naturality of the closed counit and open extension
comparison, and the normalized derived open counit identity give
  Delta ≫ F_p(g) ≫ epsilon_p = C_T(epsilon_e).
Here Delta is evaluated at J_e M, whose bounded-below property is exactly hb M.
Expand the pasted counit by Adjunction.comp_counit_app. The adjunction inverse law
then identifies g with the prescribed transpose, locallyClosedCounitMate.app M.
Both alpha and b are invertible, so g and hence that prescribed component are
invertible. This argument uses recollement and pre-duality closed comparison,
never biduality or an independently chosen isomorphism. -/
theorem locallyClosedCounitMate_isIso_finiteCoefficients
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hchar : ringChar k ≠ ell)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ell : A) ^ n = 0)
    {S V T : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (hs : (c ≫ v) ≫ aT = aS)
    (adjoints : LocallyClosedComparisonAdjoints A c)
    (hb : ∀ M : Etale.BoundedConstructibleDerivedCategory A T,
      _root_.DerivedCategory.TStructure.t.plus ((adjoints.etaleRight v).obj M.obj))
    (M : Etale.BoundedConstructibleDerivedCategory A T) :
    IsIso ((locallyClosedCounitMate A c v adjoints hb).app M) := by
  let B := ModuleCat.{u + 1} A
  letI : IsNoetherian T := {
    __ := LocallyOfFiniteType.isLocallyNoetherian aT
    __ := QuasiCompact.compactSpace_of_compactSpace aT }
  letI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian v
  letI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace v
  letI : IsNoetherian V := ⟨⟩
  let P := Etale.upperStar B v
  let Nobj := P.mapDerivedCategory.obj M.obj
  have hN : Etale.DerivedCategory.isBoundedConstructible A V Nobj := by
    obtain ⟨hc, a, b, hab, hz⟩ := M.property
    refine ⟨?_, a, b, hab, ?_⟩
    · intro n
      apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      letI := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc n)
      have hP : Scheme.IsConstructibleSheaf
          (P.obj ((_root_.DerivedCategory.homologyFunctor _ n).obj M.obj)) :=
        Scheme.IsConstructibleSheaf.upperStar v _
      exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
        ((P.mapDerivedCategoryHomologyFunctorIso n).app M.obj) hP
    · intro n hn
      exact P.isZero_homologyFunctor_mapDerivedCategory_obj (hz n hn)
  let N : Etale.BoundedConstructibleDerivedCategory A V := ⟨Nobj, hN⟩
  have ha := closed_counit_mate_isIso k hbase ell hchar A hA aS (v ≫ aT) c
    (by simpa only [Category.assoc] using hs) adjoints N (hb M)
  let CS := (comparisonUpperStar B S).mapDerivedCategory
  let CV := (comparisonUpperStar B V).mapDerivedCategory
  let CT := (comparisonUpperStar B T).mapDerivedCategory
  let Qe := (Etale.openImmersionLowerShriek B v).mapDerivedCategory
  let Qp := (openImmersionLowerShriek B v).mapDerivedCategory
  let ao := (Etale.openImmersionLowerShriekUpperStarAdjunction B v
    ).mapDerivedCategoryAdjunction
  let bo := (openImmersionLowerShriekUpperStarAdjunction B v).mapDerivedCategoryAdjunction
  let H : DerivedCategory.Plus (Sheaf S.smallEtaleTopology B) :=
    ⟨adjoints.etale.obj Nobj, hb M⟩
  let d := fixedDirectImageComparisonIso A c
  let o := derivedImmersionOpenExtensionComparison A v
  let f := d.inv.app H ≫ CV.map (adjoints.etaleAdjunction.counit.app Nobj)
  let alpha := adjoints.proetaleAdjunction.homEquiv _ _ f
  let beta := bo.homEquiv _ _ (o.inv.app Nobj ≫ CT.map (ao.counit.app M.obj))
  have halpha : IsIso alpha := ha
  have hbeta : IsIso beta := open_counit_mate_isIso A v M.obj
  have heq : (locallyClosedCounitMate A c v adjoints hb).app M =
      alpha ≫ adjoints.proetale.map beta := by
    change (adjoints.proetaleAdjunction.comp bo).homEquiv _ _
      ((locallyClosedExtensionComparison A c v).inv.app H ≫
        CT.map ((adjoints.etaleAdjunction.comp ao).counit.app M.obj)) = _
    have hd : (locallyClosedExtensionComparison A c v).inv.app H =
        Qp.map (d.inv.app H) ≫
          o.inv.app ((Etale.lowerStar B c).rightDerivedFunctor.obj H.obj) := rfl
    rw [hd, Adjunction.comp_counit_app, CT.map_comp]
    have hn := o.inv.naturality (adjoints.etaleAdjunction.counit.app Nobj)
    dsimp only [Functor.comp_map] at hn
    change Qp.map (CV.map (adjoints.etaleAdjunction.counit.app Nobj)) ≫
      o.inv.app Nobj = o.inv.app ((Etale.lowerStar B c).rightDerivedFunctor.obj H.obj) ≫
      CT.map (Qe.map (adjoints.etaleAdjunction.counit.app Nobj)) at hn
    simp only [Category.assoc]
    rw [← reassoc_of% hn]
    rw [← Category.assoc, ← Qp.map_comp]
    rw [Adjunction.comp_homEquiv]
    change adjoints.proetaleAdjunction.homEquiv _ _
      (bo.homEquiv _ _ (Qp.map f ≫ (o.inv.app Nobj ≫ CT.map (ao.counit.app M.obj)))) = _
    rw [bo.homEquiv_naturality_left,
      adjoints.proetaleAdjunction.homEquiv_naturality_right]
    rfl
  rw [heq]
  letI := halpha
  letI := hbeta
  infer_instance

end AlgebraicGeometry.ProEtale
