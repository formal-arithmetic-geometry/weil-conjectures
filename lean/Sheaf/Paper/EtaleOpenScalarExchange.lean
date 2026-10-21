/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.Paper.ProperOpenCoefficientRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import Sheaf.Paper.ScalarPullbackComposition
import all Sheaf.SixFunctors.EtaleOpenTensorDefs
import all Sheaf.Paper.EtaleProEtaleScalarMate
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange

/-! # Scalar extension respects ordinary étale open base change

Source: Stacks Project, etale-cohomology.tex, Tag 03S6,
`lemma-shriek-base-change`, with the coefficient/unit calculation in the DAG
(blueprint: lem-pur-etale-open-scalar-exchange).

All functors act on the ordinary unbounded small étale derived categories.
The open coefficient map is the existing balancing isomorphism `openScalarExtension`.
The exact pullback comparison is `properOpenCoefficientPullbackIso`, and the open
base-change map is the inverse of the published degreewise-derived isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

-- Compare the two inverse composites by their open-adjunction transposes (steps 3–6).
private theorem mate_cube
    {C D E F Cb Db Eb Fb : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category Cb] [Category Db] [Category Eb] [Category Fb]
    {LA : C ⥤ D} {JA : D ⥤ C} {LA' : E ⥤ F} {JA' : F ⥤ E}
    {LB : Cb ⥤ Db} {JB : Db ⥤ Cb} {LB' : Eb ⥤ Fb} {JB' : Fb ⥤ Eb}
    (a : LA ⊣ JA) (a' : LA' ⊣ JA') (b : LB ⊣ JB) (b' : LB' ⊣ JB')
    {HA : C ⥤ E} {GA : D ⥤ F} {HB : Cb ⥤ Eb} {GB : Db ⥤ Fb}
    {S : C ⥤ Cb} {Q : D ⥤ Db} {S' : E ⥤ Eb} {Q' : F ⥤ Fb}
    (β : LA ⋙ Q ≅ S ⋙ LB) (β' : LA' ⋙ Q' ≅ S' ⋙ LB')
    (dA : HA ⋙ LA' ≅ LA ⋙ GA) (dB : HB ⋙ LB' ≅ LB ⋙ GB)
    (lj : Q ⋙ JB ≅ JA ⋙ S) (lj' : Q' ⋙ JB' ≅ JA' ⋙ S')
    (lh : S ⋙ HB ≅ HA ⋙ S') (lg : Q ⋙ GB ≅ GA ⋙ Q')
    (cA : JA ⋙ HA ≅ GA ⋙ JA') (cB : JB ⋙ HB ≅ GB ⋙ JB')
    (hi : ∀ M, b.unit.app (S.obj M) ≫ JB.map (β.inv.app M) =
      S.map (a.unit.app M) ≫ lj.inv.app (LA.obj M))
    (hi' : ∀ M, b'.unit.app (S'.obj M) ≫ JB'.map (β'.inv.app M) =
      S'.map (a'.unit.app M) ≫ lj'.inv.app (LA'.obj M))
    (hdA : ∀ M, a'.unit.app (HA.obj M) ≫ JA'.map (dA.hom.app M) =
      HA.map (a.unit.app M) ≫ cA.hom.app (LA.obj M))
    (hdB : ∀ M, b'.unit.app (HB.obj M) ≫ JB'.map (dB.hom.app M) =
      HB.map (b.unit.app M) ≫ cB.hom.app (LB.obj M))
    (hc : ∀ N, S'.map (cA.hom.app N) ≫ lj'.inv.app (GA.obj N) ≫
        JB'.map (lg.inv.app N) =
      lh.inv.app (JA.obj N) ≫ HB.map (lj.inv.app N) ≫ cB.hom.app (Q.obj N))
    (M : C) :
    LB'.map (lh.inv.app M) ≫ dB.hom.app (S.obj M) ≫ GB.map (β.inv.app M) =
      β'.inv.app (HA.obj M) ≫ Q'.map (dA.hom.app M) ≫ lg.inv.app (LA.obj M) := by
  set_option backward.isDefEq.respectTransparency false in
    apply (b'.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
    have hn := b'.unit.naturality (lh.inv.app M)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn, reassoc_of% hdB]
    have hn := cB.hom.naturality (β.inv.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← hn, ← HB.map_comp_assoc, hi, HB.map_comp, Category.assoc]
    have hn := lh.inv.naturality (a.unit.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn]
    rw [reassoc_of% hi']
    have hn := lj'.inv.naturality (dA.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn, ← S'.map_comp_assoc, hdA, S'.map_comp, Category.assoc]
    rw [hc]

-- Identify the restriction mate with the normalized exact-pullback comparison (step 1).
private theorem openScalarRestriction_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    (openScalarRestriction φ j).hom = (properOpenCoefficientPullbackIso φ j).inv := by
  set_option backward.isDefEq.respectTransparency false in
    let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
    let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
    let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom
    let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j
    let e' := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j
    have heq : TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)).hom =
        TwoSquare.mk _ _ _ _
          (Functor.whiskerLeft (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
            e.inv ≫ x.natTrans ≫
            Functor.whiskerRight e'.hom
              (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)) := by
      ext M
      dsimp only [x, e, e', scalarRestrictionPullbackIso, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
      erw [Category.comp_id]
    change openScalarRestrictionMap φ j = _
    unfold openScalarRestrictionMap openDerivedRestrictScalarsIso
    rw [derived_square_symm φ j (Iso.ext (openRestrictScalarsIso_inv_eq φ j))]
    rw [heq, inverse_mate_transport a b x e e']
    have hm : ((mateEquiv a b).symm x).natTrans = (scalarPullbackIso φ j).inv :=
      congrArg Iso.inv (scalarPullback_eq φ j)
    rw [hm]
    ext M
    simp only [properOpenCoefficientPullbackIso, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, e, e', Category.assoc,
      scalarExtension, ProEtale.pbcFixedScalarExtension]

private theorem scalarOpen_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (M : DerivedCategoryModule A U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).unit.app
        ((scalarExtension φ U).obj M) ≫
      (derivedRestriction (A := B) j).map ((openScalarExtension φ j).inv.app M) =
    (scalarExtension φ U).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).unit.app M) ≫
      (properOpenCoefficientPullbackIso φ j).inv.app ((derivedExtension j).obj M) := by
  set_option backward.isDefEq.respectTransparency false in
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
    let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
    let l := (derivedRestriction (A := B) j).mapIso ((openScalarExtension φ j).app M) ≪≫
      (asIso (b.unit.app ((scalarExtension φ U).obj M))).symm
    let r := (openScalarRestriction φ j).symm.app ((derivedExtension j).obj M) ≪≫
      (scalarExtension φ U).mapIso (asIso (a.unit.app M)).symm
    have h : l.hom = r.hom := (etaleOpenTensorComparisons φ j).q_restricts M
    have hi := congrArg Iso.inv (Iso.ext h)
    simpa only [l, r, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Iso.app_inv, Iso.app_hom, asIso_hom, a, b, openScalarRestriction_eq] using hi

-- Cancel the comparison for the common composite to obtain the inverse square (step 2).
private theorem scalarPullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U' U T' T : Scheme.{u}}
    (h : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    (sq : CommSq h j' j g) (N : DerivedCategoryModule A T) :
    (scalarExtension φ U').map
        ((Functor.mapDerivedCategorySquareIso (openImmersionSquareIso
          (ModuleCat.{u + 1} A) sq)).hom.app N) ≫
      (properOpenCoefficientPullbackIso φ j').inv.app
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j').mapDerivedCategory.map
        ((properOpenCoefficientPullbackIso φ g).inv.app N) =
    (properOpenCoefficientPullbackIso φ h).inv.app
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.map
        ((properOpenCoefficientPullbackIso φ j).inv.app N) ≫
      (Functor.mapDerivedCategorySquareIso (openImmersionSquareIso
        (ModuleCat.{u + 1} B) sq)).hom.app ((scalarExtension φ T).obj N) := by
  set_option backward.isDefEq.respectTransparency false in
    let k := h ≫ j
    let aA := Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) h j k rfl) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    let aB := Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} B) h j k rfl) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    let bA := Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) j' g k sq.w) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    let bB := Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} B) j' g k sq.w) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    have hleft := scalarPullback_composition φ j h k rfl N
    have hright := scalarPullback_composition φ g j' k sq.w.symm N
    change aB.hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ j).hom.app N) ≫
        (properOpenCoefficientPullbackIso φ h).hom.app _ =
      (properOpenCoefficientPullbackIso φ k).hom.app N ≫
        (scalarExtension φ U').map (aA.hom.app N) at hleft
    change bB.hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} B) j').mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ g).hom.app N) ≫
        (properOpenCoefficientPullbackIso φ j').hom.app _ =
      (properOpenCoefficientPullbackIso φ k).hom.app N ≫
        (scalarExtension φ U').map (bA.hom.app N) at hright
    have hcA : (Functor.mapDerivedCategorySquareIso
        (openImmersionSquareIso (ModuleCat.{u + 1} A) sq)).hom.app N =
        aA.inv.app N ≫ bA.hom.app N := by
      simp [Functor.mapDerivedCategorySquareIso, openImmersionSquareIso,
        aA, bA, k, Functor.mapDerivedCategoryNatIso_trans,
        Functor.mapDerivedCategoryNatIso_symm]
    have hcB : (Functor.mapDerivedCategorySquareIso
        (openImmersionSquareIso (ModuleCat.{u + 1} B) sq)).hom.app
          ((scalarExtension φ T).obj N) =
        aB.inv.app _ ≫ bB.hom.app _ := by
      simp [Functor.mapDerivedCategorySquareIso, openImmersionSquareIso,
        aB, bB, k, Functor.mapDerivedCategoryNatIso_trans,
        Functor.mapDerivedCategoryNatIso_symm]
    rw [hcA, hcB]
    apply (cancel_epi ((properOpenCoefficientPullbackIso φ h).hom.app _)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    apply (cancel_epi ((upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.map
      ((properOpenCoefficientPullbackIso φ j).hom.app N))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    apply (cancel_epi (aB.hom.app ((scalarExtension φ T).obj N))).mp
    rw [reassoc_of% hleft]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% hright]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Scalar balancing commutes with ordinary étale open base change, naturally on
all unbounded derived objects. Here the pullback is `T' ×_T U`, with open projection
`pullback.fst g j` and other projection `pullback.snd g j`.
Source: Stacks Project, etale-cohomology.tex, Tag 03S6, `lemma-shriek-base-change`
(blueprint: lem-pur-etale-open-scalar-exchange).

Proof:
1. Write L, J for open extension and restriction, G, H for pullback along g, h,
and Q, Q', S, S' for scalar extension on T, T', U, U'. Write i and i' for the
inverses of the open balancing maps, d_R for the inverse open base-change maps,
and c_R : H_R J_R ≅ J'_R G_R for the canonical square comparison. The prescribed
open-unit transpose formulas give J_B(i) eta_B = lambda_j inverse S(eta_A),
and J'_R(d_R) eta'_R = c_R H_R(eta_R). These are the degreewise-normalized open
adjunctions and comparisons of lem-coef-etale-open-tensor,
def-pur-open-coefficient-normalizations and lem-cbc-extension-zero-base-change.
2. Apply lem-sf-scalar-pullback-composition to (j,h) and (g,j'). Their composite
scheme maps agree. Eliminate the common scalar comparison for that composite.
After multiplying by inverse scalar comparisons, the resulting square identity is
J'_B(lambda_g inverse) lambda_j' inverse S'(c_A) =
c_B H_B(lambda_j inverse) lambda_h inverse.
3. Invert both composites in the asserted equality. The resulting maps are
x = G_B(i) d_B L'_B(lambda_h inverse) and
y = lambda_g inverse Q'(d_A) i', both out of L'_B S' H_A M.
It suffices to compare their transposes under L'_B adjoint to J'_B.
4. Naturality of the open unit, the formula for d_B, naturality of c_B, the formula
for i, and naturality of lambda_h inverse give the transpose of x as
c_B H_B(lambda_j inverse) lambda_h inverse S'H_A(eta_A).
5. The formula for i', naturality of lambda_j' inverse, and the formula for d_A
give the transpose of y as
J'_B(lambda_g inverse) lambda_j' inverse S'(c_A) S'H_A(eta_A).
6. Apply the square identity of step 2 at L_A M and precompose with S'H_A(eta_A).
The transposes coincide, so injectivity of the adjunction bijection gives x = y.
Taking inverses proves the displayed equality. Every factor is natural in M.
The argument uses no boundedness, coefficient flatness, or quasi-compactness. -/
theorem etaleOpenScalarExchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U T T' : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (g : T' ⟶ T) (M : DerivedCategoryModule A U) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((openScalarExtension φ j).hom.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} B) (IsPullback.of_hasPullback g j).flip).inv.app
          ((scalarExtension φ U).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B)
        (pullback.fst g j)).mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ (pullback.snd g j)).hom.app M) =
    (properOpenCoefficientPullbackIso φ g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (scalarExtension φ T').map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback g j).flip).inv.app M) ≫
      (openScalarExtension φ (pullback.fst g j)).hom.app
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd g j)).mapDerivedCategory.obj M) := by
  set_option backward.isDefEq.respectTransparency false in
    let h := pullback.snd g j
    let j' := pullback.fst g j
    let sq := (IsPullback.of_hasPullback g j).flip
    let LA := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
    let LB' := (openImmersionLowerShriek (ModuleCat.{u + 1} B) j').mapDerivedCategory
    let GB := (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory
    let HA := (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
    let Q' := scalarExtension φ T'
    let S := scalarExtension φ U
    let dA := mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) sq
    let dB := mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} B) sq
    let cA := Functor.mapDerivedCategorySquareIso
      (openImmersionSquareIso (ModuleCat.{u + 1} A) sq.toCommSq)
    let cB := Functor.mapDerivedCategorySquareIso
      (openImmersionSquareIso (ModuleCat.{u + 1} B) sq.toCommSq)
    have hi := mate_cube
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j')
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j')
      (openScalarExtension φ j) (openScalarExtension φ j') dA dB
      (properOpenCoefficientPullbackIso φ j) (properOpenCoefficientPullbackIso φ j')
      (properOpenCoefficientPullbackIso φ h) (properOpenCoefficientPullbackIso φ g) cA cB
      (scalarOpen_unit φ j) (scalarOpen_unit φ j')
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate _ sq)
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate _ sq)
      (scalarPullback_square φ h j' j g sq.toCommSq) M
    let l := LB'.mapIso ((properOpenCoefficientPullbackIso φ h).symm.app M) ≪≫
      dB.app (S.obj M) ≪≫ GB.mapIso ((openScalarExtension φ j).symm.app M)
    let r := (openScalarExtension φ j').symm.app (HA.obj M) ≪≫
      Q'.mapIso (dA.app M) ≪≫ (properOpenCoefficientPullbackIso φ g).symm.app (LA.obj M)
    have he : l.hom = r.hom := hi
    have hinv := congrArg Iso.inv (Iso.ext he)
    simpa only [l, r, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv,
      Category.assoc] using hinv

end AlgebraicGeometry.Etale
