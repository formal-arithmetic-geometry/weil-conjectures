/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicTensorReindexing
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRightRepresentatives
import all WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceScalarUnit

/-! # Cochain left unitor for ordinary adic reindexing

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Project, Tags 03EK and 0FPT.
(blueprint: lem-sf-adic-reindexing-unit-complex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite WeilConjectures CategoryTheory.RingedForgetTensorTransposition
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] coefficientTotalTensor
  homComplexFunctor homComplexπ derivedInternalHomOfUniverses coefficientHomResolutionIso
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors DerivedCategory
  instCategoryDerivedCategory DerivedCategory.Q SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients
private theorem complex_iso_inv_apply
    {Z : Type (u + 1)} [Category.{u} Z] {J : GrothendieckTopology Z}
    {R₀ : Sheaf J RingCat.{u + 1}}
    {P Q : CochainComplex (SheafOfModules.{u + 1} R₀) ℤ} (e : P ≅ Q)
    (n : ℤ) (W : Zᵒᵖ) (x : (P.X n).val.obj W) (y : (Q.X n).val.obj W)
    (h : (e.hom.f n).val.app W x = y) : (e.inv.f n).val.app W y = x := by
  have hh := congrArg (fun f ↦ (f.f n).val.app W x) e.hom_inv_id
  change (e.inv.f n).val.app W ((e.hom.f n).val.app W x) = x at hh
  exact (congrArg (fun z ↦ (e.inv.f n).val.app W z) h).symm.trans hh

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  {R : LocallyFiniteAdicRealization.Realization l X}
  {S : LocallyFiniteAdicRealization.Realization l Y}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  {A : At l X R} {B : At l Y S} {r : RingReindex l X g R S}
  (V : ReindexTensor l X g A B r)

private theorem reindex_pure_at
    (P Q : CochainComplex (modules l Y S) ℤ) (p q n : ℤ) (h : p + q = n)
    (W : X.ProEtᵒᵖ)
    (x : (P.X p).val.obj ((proEtaleIsoPostcompose g).op.obj W))
    (y : (Q.X q).val.obj ((proEtaleIsoPostcompose g).op.obj W)) :
    ((V.cochain.hom.app (P, Q)).f n).val.app W
      (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S)
        P Q p q n h ((proEtaleIsoPostcompose g).op.obj W) x y) =
    coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
      (((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj P)
      (((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj Q) p q n h W x y := by
  subst n
  exact V.pure P Q p q W x y

omit [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)] in
private theorem reindex_smul (r : RingReindex l X g R S) (M : modules l Y S) (W : X.ProEtᵒᵖ)
    (a : (ring l Y S).obj.obj ((proEtaleIsoPostcompose g).op.obj W))
    (y : M.val.obj ((proEtaleIsoPostcompose g).op.obj W)) :
    ((((modulePull l X g r).obj M).val.obj W).smul (r.iso.hom.hom.app W a)).hom y =
      ((M.val.obj ((proEtaleIsoPostcompose g).op.obj W)).smul a).hom y := by
  let c := ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso r.iso).hom
  change ((inv c).hom.app W (c.hom.app W a)) • y = a • y
  have ha := congrArg (fun f ↦ f.hom.app W a) (IsIso.hom_inv_id c)
  change (inv c).hom.app W (c.hom.app W a) = a at ha
  exact congrArg (fun a ↦ a • y) ha

/-- The chain left-unit square for ordinary adic reindexing and any two
multiplication-normalized left-unitor representatives.
Source: BS Remark 6.8.15; Stacks 03EK and 0FPT.
(blueprint: lem-sf-adic-reindexing-unit-complex).

Proof: precompose the inverse cochain comparison and test totalization summands
and sheafified pure tensors. Nonzero first degrees vanish. In degree (0,n),
write the first section as the coefficient-unit section of a. The pure-section
equation identifies the inverse tensor comparison on this generator. Naturality
of the total tensor moves the unit comparison to that first factor. Its recorded
section equation applies the coefficient-ring isomorphism to a. The reindexed
module action uses the inverse isomorphism, so both left-unitor models multiply
by the same original coefficient a. -/
theorem reindexing_left_unitor_chain
    (P : CochainComplex (modules l Y S) ℤ)
    (bB : (coefficientTotalTensor.{u + 1, u + 1, u}
      (ProEt.topology Y) (ring l Y S)).obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S), P) ≅ P)
    (bA : (coefficientTotalTensor.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R)).obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R),
        ((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj P)
    (hbB : ∀ (n : ℤ) (h : 0 + n = n) (W : Y.ProEtᵒᵖ) (a : (ring l Y S).obj.obj W)
      (x : (P.X n).val.obj W),
      (bB.hom.f n).val.app W (coefficientTensorGenerator.{u + 1, u + 1, u}
        (ProEt.topology Y) (ring l Y S)
        (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S))
        P 0 n n h W
        (ringedTensorUnitSection.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S) W a) x) =
        a • x)
    (hbA : ∀ (n : ℤ) (h : 0 + n = n) (W : X.ProEtᵒᵖ) (a : (ring l X R).obj.obj W)
      (x : ((((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj P).X n).val.obj W),
      (bA.hom.f n).val.app W (coefficientTensorGenerator.{u + 1, u + 1, u}
        (ProEt.topology X) (ring l X R)
        (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R))
        (((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj P) 0 n n h W
        (ringedTensorUnitSection.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R) W a) x) =
        a • x) :
    ((modulePull l X g r).mapHomologicalComplex (.up ℤ)).map bB.hom =
      V.cochain.hom.app
        (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S), P) ≫
      (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)).map
        (X := (((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj
          (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)),
          ((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj P))
        (Y := (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R),
          ((modulePull l X g r).mapHomologicalComplex (.up ℤ)).obj P))
        (V.unitCochain.hom, 𝟙 _) ≫ bA.hom := by
  let F := (modulePull l X g r).mapHomologicalComplex (.up ℤ)
  let O := ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)
  let O' := ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
  let t := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (ring l X R)
  let := SheafOfModules.monoidalCategory (ring l X R)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients (ring l X R)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (ring l X R)
  change F.map bB.hom = V.cochain.hom.app (O, P) ≫
    t.map (X := (F.obj O, F.obj P)) (Y := (O', F.obj P))
      (V.unitCochain.hom, 𝟙 (F.obj P)) ≫ bA.hom
  apply (cancel_epi (V.cochain.inv.app (O, P))).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply CategoryTheory.RingedForgetTensorTransposition.total_hom_ext.{u + 1, u, u + 1}
    (ProEt.topology X) (ring l X R)
    (F.obj O) (F.obj P) (F.obj P)
  intro n p q hpq
  simp only [HomologicalComplex.comp_f]
  by_cases hp : p = 0
  · subst p
    have hn : q = n := by omega
    subst q
    apply CategoryTheory.RingedForgetTensorTransposition.pure_ext.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R)
      _ _ _
    intro W x y
    let sy := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
      (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S)))
    let a : (ring l Y S).obj.obj ((proEtaleIsoPostcompose g).op.obj W) :=
      sy.hom.val.app ((proEtaleIsoPostcompose g).op.obj W) x
    have hx : ringedTensorUnitSection.{u + 1, u, u + 1}
        (ProEt.topology Y) (ring l Y S) ((proEtaleIsoPostcompose g).op.obj W) a = x := by
      exact congrArg (fun f ↦ f.val.app ((proEtaleIsoPostcompose g).op.obj W) x)
        sy.hom_inv_id
    have hi : ((V.cochain.hom.app (O, P)).f n).val.app W
        (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S)
          O P 0 n n hpq ((proEtaleIsoPostcompose g).op.obj W) x y) =
        coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
          (F.obj O) (F.obj P) 0 n n hpq W x y := by
      exact reindex_pure_at l g V O P 0 n n hpq W x y
    have hgen : ((V.cochain.inv.app (O, P)).f n).val.app W
        (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
          (F.obj O) (F.obj P) 0 n n hpq W x y) =
        coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S)
          O P 0 n n hpq ((proEtaleIsoPostcompose g).op.obj W) x y :=
      complex_iso_inv_apply (V.cochain.app (O, P)) n W _ _ hi
    have hm := CategoryTheory.tensorGenerator_map.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) V.unitCochain.hom (𝟙 (F.obj P))
      0 n n hpq W x y
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at hm
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    change (bB.hom.f n).val.app ((proEtaleIsoPostcompose g).op.obj W)
        (((V.cochain.inv.app (O, P)).f n).val.app W
          (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
            (F.obj O) (F.obj P) 0 n n hpq W x y)) =
      (bA.hom.f n).val.app W
        (((t.map (V.unitCochain.hom, 𝟙 (F.obj P))).f n).val.app W
          (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
            (F.obj O) (F.obj P) 0 n n hpq W x y))
    refine (congrArg (fun z ↦ (bB.hom.f n).val.app
      ((proEtaleIsoPostcompose g).op.obj W) z) hgen).trans ?_
    refine Eq.trans ?_ (congrArg (fun z ↦ (bA.hom.f n).val.app W z) hm.symm)
    have hxU : (V.unitCochain.hom.f 0).val.app W x =
        ringedTensorUnitSection.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
          W (r.iso.hom.hom.app W a) :=
      (congrArg (fun z ↦ (V.unitCochain.hom.f 0).val.app W z) hx).symm.trans
        (V.unit_sections W a)
    calc
      _ = (((P.X n).val.obj ((proEtaleIsoPostcompose g).op.obj W)).smul a).hom y := by
        have hh := hbB n hpq ((proEtaleIsoPostcompose g).op.obj W) a y
        rw [hx] at hh
        exact hh
      _ = ((((F.obj P).X n).val.obj W).smul (r.iso.hom.hom.app W a)).hom y :=
        (reindex_smul l g r (P.X n) W a y).symm
      _ = _ := by
        have hh := hbA n hpq W (r.iso.hom.hom.app W a) y
        exact hh.symm.trans (congrArg (fun z ↦ (bA.hom.f n).val.app W
          (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
            O' (F.obj P) 0 n n hpq W z y)) hxU.symm)
  · apply IsZero.eq_of_src
    apply (tensorRight ((F.obj P).X q)).map_isZero
    exact (modulePull l X g r).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp)

end WeilConjectures.AdicQbarRealization
