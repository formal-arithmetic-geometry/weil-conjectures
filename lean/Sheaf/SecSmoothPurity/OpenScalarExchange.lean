/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.ProjectionFormulaCompactified
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.SecSmoothPurity.OpenBaseChangeDerivedUnit
import Sheaf.SecSmoothPurity.TensorPullbackSquare

/-! Scalar extension respects the open base-change comparison.
Source: Stacks Project, Tag 03S6, label `lemma-shriek-base-change`, together with
Tags 07A4 and 09AE (blueprint: lem-fix-open-scalar-exchange).

All objects are in the constant-ring module coordinates `proEtaleConstantRing T A`
(`A` lifted to the site's coefficient universe) of def-weil-pbc-proetale-operations.
The open base-change map is the recorded `StrictTower.singleBeta` of
lem-cbc-proetale-extension-zero-base-change, at the lifted coefficient ring; its
constant coefficients, module pullback and open extension are definitionally the ones below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Derived scalar extension `S_T = - ⊗^L_{A_T} B_T` along a constant coefficient-ring map.
Source: Stacks Tag 06YY (blueprint: lem-pur-derived-change-of-rings). -/
noncomputable abbrev scalarExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B)) :=
  Scheme.proEtaleRingDerivedExtension
    (Scheme.proEtaleConstantRingMap (T := T) φ)

/-- Derived restriction of scalars `Res_T`, right adjoint to `scalarExtension`.
Source: Stacks Tag 07A6 (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable abbrev scalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) :=
  (Scheme.proEtaleRingRestrictScalars
    (Scheme.proEtaleConstantRingMap (T := T) φ)).mapDerivedCategory

/-- The exact derived constant-coefficient inverse image `f_A^{-1}`.
Source: Stacks Section 0735 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev constantPullback {A : Type u} [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X) :
    DerivedCategory (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A)) :=
  Scheme.proEtaleRingDerivedPullback f
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison f A)

/-- The exact derived extension by zero `j_!^A`, left adjoint to `j_A^{-1}`.
Source: Stacks Tags 03DI and 09AE (blueprint: lem-cbc-proetale-extension-zero). -/
noncomputable abbrev openExtension {A : Type u} [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory (Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  Scheme.proEtaleRingDerivedOpenExtension j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j A)

/-- The canonical tensor/inverse-image comparison `λ_f : f_B^{-1} S_X ≅ S_U f_A^{-1}`,
the inverse of the mate of the restriction/pullback identification; on K-flat
representatives it is the balancing map.
Source: Stacks Tags 07A4 and 0G7E
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def tensorPullbackIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (f : U ⟶ X) :
    scalarExtension φ X ⋙ constantPullback f ≅
      constantPullback f ⋙ scalarExtension φ U :=
  Scheme.proEtaleReductionPullbackIso f
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing X B)
    (Scheme.proEtaleConstantRing U A) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingMap (T := X) φ)
    (Scheme.proEtaleConstantRingMap (T := U) φ)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison f B)
    (by
      simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
        (Scheme.proEtaleConstantInverseImageMap_naturality f
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)

/-- The scalar/open comparison `β_j : S_X j_!^A ≅ j_!^B S_U`, the unique isomorphism of
left adjoints whose right-adjoint comparison is the identification
`j_A^{-1} Res_X = Res_U j_B^{-1}` of lem-weil-pbc-ring-sheaf-change-adjunction.
Source: Stacks Tags 07A6 and 03DI (blueprint: lem-fix-open-scalar-exchange). -/
noncomputable def openScalarIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openExtension j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ openExtension j := by
  let adjA := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j A)
  let adjB := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X B) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingComparison j B)
  let adjX := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := X) φ)
  let adjU := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := U) φ)
  let rightIso := Scheme.proEtaleRingRestrictionDerivedPullback j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing X B)
    (Scheme.proEtaleConstantRing U A) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingMap (T := X) φ)
    (Scheme.proEtaleConstantRingMap (T := U) φ)
    (Scheme.proEtaleConstantRingComparison j A)
    (Scheme.proEtaleConstantRingComparison j B) (by
      simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
        (Scheme.proEtaleConstantInverseImageMap_naturality j
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)
  exact (adjA.comp adjX).leftAdjointUniq
    ((adjU.comp adjB).ofNatIsoRight rightIso)

/-- The actual open base-change map `e_j : g^{-1} j_! ≅ j'_! h^{-1}` of
lem-cbc-proetale-extension-zero-base-change, i.e. the recorded `StrictTower.singleBeta`
at the lifted coefficient ring; its inverse is the `j'_! ⊣ j'^{-1}` adjunct of `h^{-1} η_j`
followed by the cartesian inverse-image identification.
Source: Stacks Tags 03S6 and 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def openBaseChangeIso {A : Type u} [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j'] :
    openExtension (A := A) j ⋙ constantPullback (A := A) g ≅
      constantPullback (A := A) gU ⋙ openExtension (A := A) j' :=
  StrictTower.singleBeta (ULift.{u + 1, u} A) gU j' j g sq.toCommSq.w
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)

set_option backward.defeqAttrib.useBackward true in
private theorem scalarOpenTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) (K : C) :
    b.unit.app (SU.obj K) ≫ JB.map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      SU.map (a.unit.app K) ≫
        ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K) := by
  apply (u.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((u.comp b).ofNatIsoRight q) (a.comp x) K
  change ((u.comp b).ofNatIsoRight q).unit.app K ≫
      (RX ⋙ JA).map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      (a.comp x).unit.app K at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] at h
  have hn := q.hom.naturality
    (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [Functor.comp_obj] at h
  rw [← hn] at h
  have hm := unit_mateEquiv_symm x u (TwoSquare.mk _ _ _ _ q.inv) (LA.obj K)
  change JA.map (x.unit.app (LA.obj K)) ≫ q.inv.app (SX.obj (LA.obj K)) =
    u.unit.app (JA.obj (LA.obj K)) ≫ RU.map
      (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K)) at hm
  have hu := u.unit.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
  rw [← reassoc_of% hu, ← hm]
  apply (cancel_mono (q.hom.app (SX.obj (LA.obj K)))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj,
    Adjunction.comp_unit_app] using h

private theorem openScalarIso_unit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (Scheme.proEtaleRingModules U
      (Scheme.proEtaleConstantRing U A))) :
    (Scheme.proEtaleRingDerivedOpenAdjunction j
      (Scheme.proEtaleConstantRing X B) (Scheme.proEtaleConstantRing U B)
      (Scheme.proEtaleConstantRingComparison j B)).unit.app ((scalarExtension φ U).obj K) ≫
        (constantPullback j).map ((openScalarIso φ j).inv.app K) =
      (scalarExtension φ U).map ((Scheme.proEtaleRingDerivedOpenAdjunction j
        (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
        (Scheme.proEtaleConstantRingComparison j A)).unit.app K) ≫
          (tensorPullbackIso φ j).inv.app ((openExtension j).obj K) := by
  let adjA := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j A)
  let adjB := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X B) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingComparison j B)
  let adjX := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := X) φ)
  let adjU := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := U) φ)
  let rightIso := Scheme.proEtaleRingRestrictionDerivedPullback j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing X B)
    (Scheme.proEtaleConstantRing U A) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingMap (T := X) φ)
    (Scheme.proEtaleConstantRingMap (T := U) φ)
    (Scheme.proEtaleConstantRingComparison j A)
    (Scheme.proEtaleConstantRingComparison j B) (by
      simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
        (Scheme.proEtaleConstantInverseImageMap_naturality j
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)
  exact scalarOpenTranspose adjA adjB adjX adjU rightIso K

/-- Scalar extension respects the open base-change comparison, naturally in the input:
`j'_!(λ_{h,K}) ∘ e^B_{j,S_U K} ∘ g_B^{-1}(β_{j,K})
  = β_{j',h^{-1}K} ∘ S_{X'}(e^A_{j,K}) ∘ λ_{g,j_!K}`.
Source: Stacks Project, Tag 03S6, label `lemma-shriek-base-change`
(blueprint: lem-fix-open-scalar-exchange).
Proof: the scalar/open comparison is the unique isomorphism of composite left adjoints.
Its inverse transpose is scalar extension of the open unit followed by the inverse
tensor comparison, by scalarOpenTranspose and openScalarIso_unit. The equation
openBaseChangeDerivedUnit gives the inverse transpose of the specified open exchange
at A and B. The theorem tensorPullbackSquare gives coherence of the tensor comparisons
with the specified inverse-image square; it follows from ordinary restriction
coherence, exact localization, and scalar-adjunction mates. Compare the inverses of
the two asserted composites under the open B-adjunction Hom equivalence. Naturality
of the open unit, the two base-change unit equations, openScalarIso_unit, tensor-square
coherence and naturality of the inverse tensor comparison identify their transposes.
Injectivity of that equivalence identifies the inverses and hence the original maps. -/
theorem openScalarExchange
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (K : DerivedCategory (Scheme.proEtaleRingModules U
      (Scheme.proEtaleConstantRing U A))) :
    (constantPullback g).map ((openScalarIso φ j).hom.app K) ≫
      (openBaseChangeIso gU j' j g sq).hom.app ((scalarExtension φ U).obj K) ≫
      (openExtension j').map ((tensorPullbackIso φ gU).hom.app K) =
    (tensorPullbackIso φ g).hom.app ((openExtension j).obj K) ≫
      (scalarExtension φ X').map ((openBaseChangeIso gU j' j g sq).hom.app K) ≫
      (openScalarIso φ j').hom.app ((constantPullback gU).obj K) := by
  let a (R : Type u) [CommRing R] := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X R) (Scheme.proEtaleConstantRing U R)
    (Scheme.proEtaleConstantRingComparison j R)
  let b (R : Type u) [CommRing R] := Scheme.proEtaleRingDerivedOpenAdjunction j'
    (Scheme.proEtaleConstantRing X' R) (Scheme.proEtaleConstantRing U' R)
    (Scheme.proEtaleConstantRingComparison j' R)
  let c (R : Type u) [CommRing R] := Functor.mapDerivedCategorySquareIso
    (StrictTower.moduleSquareG (ULift.{u + 1, u} R) gU j' j g sq.toCommSq.w)
  let N := (openExtension (A := A) j).obj K
  let L := (constantPullback (A := B) g).mapIso ((openScalarIso φ j).app K) ≪≫
    (openBaseChangeIso (A := B) gU j' j g sq).app ((scalarExtension φ U).obj K) ≪≫
      (openExtension (A := B) j').mapIso ((tensorPullbackIso φ gU).app K)
  let R := (tensorPullbackIso φ g).app N ≪≫
    (scalarExtension φ X').mapIso ((openBaseChangeIso (A := A) gU j' j g sq).app K) ≪≫
      (openScalarIso φ j').app ((constantPullback (A := A) gU).obj K)
  have hA := openBaseChangeDerivedUnit (A := A) gU j' j g sq K
  have hB := openBaseChangeDerivedUnit (A := B) gU j' j g sq
    ((scalarExtension φ U).obj K)
  change (b A).unit.app ((constantPullback gU).obj K) ≫
      (constantPullback j').map ((openBaseChangeIso gU j' j g sq).inv.app K) =
    (constantPullback gU).map ((a A).unit.app K) ≫ (c A).inv.app N at hA
  change (b B).unit.app ((constantPullback gU).obj ((scalarExtension φ U).obj K)) ≫
      (constantPullback j').map
        ((openBaseChangeIso gU j' j g sq).inv.app ((scalarExtension φ U).obj K)) =
    (constantPullback gU).map ((a B).unit.app ((scalarExtension φ U).obj K)) ≫
      (c B).inv.app ((openExtension j).obj ((scalarExtension φ U).obj K)) at hB
  have hc := tensorPullbackSquare φ gU j' j g sq N
  change (scalarExtension φ U').map ((c A).inv.app N) ≫
      (tensorPullbackIso φ j').inv.app ((constantPullback g).obj N) ≫
        (constantPullback j').map ((tensorPullbackIso φ g).inv.app N) =
    (tensorPullbackIso φ gU).inv.app ((constantPullback j).obj N) ≫
      (constantPullback gU).map ((tensorPullbackIso φ j).inv.app N) ≫
        (c B).inv.app ((scalarExtension φ X).obj N) at hc
  have hi : L.inv = R.inv := by
    apply ((b B).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, L, R, Iso.trans_inv, Functor.mapIso_inv,
      Iso.app_inv, Category.assoc]
    change (b B).unit.app _ ≫ (constantPullback (A := B) j').map
        ((openExtension j').map ((tensorPullbackIso φ gU).inv.app K) ≫
          (openBaseChangeIso gU j' j g sq).inv.app ((scalarExtension φ U).obj K) ≫
            (constantPullback g).map ((openScalarIso φ j).inv.app K)) =
      (b B).unit.app _ ≫ (constantPullback (A := B) j').map
        ((openScalarIso φ j').inv.app ((constantPullback gU).obj K) ≫
          (scalarExtension φ X').map ((openBaseChangeIso gU j' j g sq).inv.app K) ≫
            (tensorPullbackIso φ g).inv.app N)
    simp only [Functor.map_comp]
    have hu := (b B).unit.naturality ((tensorPullbackIso φ gU).inv.app K)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
    dsimp only [Functor.comp_obj]
    rw [← reassoc_of% hu, reassoc_of% hB]
    have hn := (c B).inv.naturality ((openScalarIso φ j).inv.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    change (constantPullback (A := B) gU).map
        ((constantPullback j).map ((openScalarIso φ j).inv.app K)) ≫
          (c B).inv.app ((scalarExtension φ X).obj N) =
        (c B).inv.app ((openExtension j).obj ((scalarExtension φ U).obj K)) ≫
          (constantPullback j').map
            ((constantPullback g).map ((openScalarIso φ j).inv.app K)) at hn
    rw [← hn]
    rw [← (constantPullback (A := B) gU).map_comp_assoc, openScalarIso_unit]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc ((b B).unit.app _), openScalarIso_unit]
    simp only [Category.assoc]
    have ht := (tensorPullbackIso φ j').inv.naturality
      ((openBaseChangeIso (A := A) gU j' j g sq).inv.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at ht
    rw [← reassoc_of% ht]
    rw [← (scalarExtension φ U').map_comp_assoc, hA]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc]
    have hl := (tensorPullbackIso φ gU).inv.naturality ((a A).unit.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hl
    rw [reassoc_of% hl]
  have he : L.symm = R.symm := Iso.ext hi
  have he' := congrArg (fun e ↦ e.inv) he
  simpa only [L, R, Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc] using he'

end AlgebraicGeometry.ProEtale
