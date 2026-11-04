/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionPullTensorChain
public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionFlatRepresentatives
public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionReductionFlat
public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionPullCompCoherence

/-! # Tensor coherence of the native pullback reduction comparison

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

The pullback reduction comparison `m.pull g` is monoidal for the oplax structure of `Lg^*`, the
tensor comparisons `(m.tensor T).mu` and the system tensor pullback `(m.systemPull g).iso`.

Both sides are natural, so it suffices to treat flat-term K-flat representatives. There, all
the comparisons are computed by their representative normalizations: the tensorator of `Lg^*`
by the degreewise ordinary tensorator (`ringedPull_δ_Q`), the pullback comparison by the model
`PullReductionModel`, the tensor comparisons by `TensorPresentation.localization` and the
system tensor pullback by `TensorComparisonModel.derived`. The resulting chain maps agree by
`pull_tensor_chain_identity`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

section Generic

variable {SY SZ : Type*} [Category SY] [Category SZ]

private lemma mkHom_comp_mkHom {C D : Type*} [Category C] [Category D] {X₁ X₂ X₃ : C}
    {Y₁ Y₂ Y₃ : D} (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃) (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) :
    Prod.mkHom f g ≫ Prod.mkHom f' g' = Prod.mkHom (f ≫ f') (g ≫ g') :=
  rfl

private instance isIso_mkHom {C D : Type*} [Category C] [Category D] {X₁ X₂ : C}
    {Y₁ Y₂ : D} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [IsIso f] [IsIso g] : IsIso (Prod.mkHom f g) :=
  ⟨⟨Prod.mkHom (inv f) (inv g), by simp, by simp⟩⟩

/-- The diagram chase behind the tensor coherence of a pullback comparison on representatives:
the comparisons are given by their representative formulas and the two chain maps agree. -/
theorem pull_tensor_representative_chase (G : SY ⥤ SZ) (TY : SY × SY ⥤ SY)
    (TZ : SZ × SZ ⥤ SZ) (sys : TY ⋙ G ≅ (G.prod G) ⋙ TZ)
    {yAB yA yB yP yQ y1 y2 y3 : SY}
    {muY : yAB ⟶ TY.obj (yA, yB)} {εP : yA ⟶ yP} {εQ : yB ⟶ yQ} [IsIso εP] [IsIso εQ]
    {rμ : yAB ⟶ y1} {ε12 : y1 ⟶ y2} {qch : y2 ⟶ y3} (tmiY : y3 ≅ TY.obj (yP, yQ))
    (H8 : muY ≫ TY.map (Prod.mkHom εP εQ) = rμ ≫ ε12 ≫ qch ≫ tmiY.hom)
    {z0 z1 zA zB z0' z0'' z1' z1'' zcP zcQ zeP zeQ zfP zfQ g0 e12 e12' e12'' h12 htot : SZ}
    {d : z0 ⟶ z1} {muZ1 : z1 ⟶ TZ.obj (zA, zB)} {nA : zA ⟶ G.obj yA} {nB : zB ⟶ G.obj yB}
    {n0 : z0 ⟶ G.obj yAB} (facsP : G.obj yP ≅ zfP) (facsQ : G.obj yQ ≅ zfQ)
    {xP : zA ⟶ zcP} {xQ : zB ⟶ zcQ} {yP' : zcP ⟶ zeP} {yQ' : zcQ ⟶ zeQ}
    {oP : zeP ⟶ zfP} {oQ : zeQ ⟶ zfQ}
    (H1P : xP ≫ yP' ≫ oP = nA ≫ G.map εP ≫ facsP.hom)
    (H1Q : xQ ≫ yQ' ≫ oQ = nB ≫ G.map εQ ≫ facsQ.hom)
    {xx : z1 ⟶ z1'} {muZ2 : z1' ⟶ TZ.obj (zcP, zcQ)}
    (H2 : muZ1 ≫ TZ.map (Prod.mkHom xP xQ) = xx ≫ muZ2)
    {w1 : z1' ⟶ z1''} {ε12Z : z1'' ⟶ e12} {qc : e12 ⟶ e12'} {tmiZ1 : e12' ⟶ TZ.obj (zeP, zeQ)}
    (H3 : muZ2 ≫ TZ.map (Prod.mkHom yP' yQ') = w1 ≫ ε12Z ≫ qc ≫ tmiZ1)
    {v1 : z0 ⟶ z0'} {v2 : z0' ⟶ z0''} {v3 : z0'' ⟶ z1''}
    (H4 : v1 ≫ v2 ≫ v3 = d ≫ xx ≫ w1)
    {εZ0 : z0'' ⟶ g0} {oδ : g0 ⟶ e12} (H5 : v3 ≫ ε12Z = εZ0 ≫ oδ)
    {qtot : e12' ⟶ e12''} (tmiZ2 : e12'' ≅ TZ.obj (zfP, zfQ))
    (H6 : qtot ≫ tmiZ2.hom = tmiZ1 ≫ TZ.map (Prod.mkHom oP oQ))
    {n1 : z0' ⟶ G.obj y1} (H7 : v1 ≫ n1 = n0 ≫ G.map rμ)
    {facs12 : G.obj y2 ⟶ h12} {ord12 : g0 ⟶ h12}
    (H10 : v2 ≫ εZ0 ≫ ord12 = n1 ≫ G.map ε12 ≫ facs12)
    (facsTot : G.obj y3 ≅ htot) {pch : h12 ⟶ htot}
    (H11 : G.map qch ≫ facsTot.hom = facs12 ≫ pch)
    {mch : e12'' ⟶ htot}
    (H12 : tmiZ2.hom ≫ TZ.map (Prod.mkHom facsP.inv facsQ.inv) ≫ sys.inv.app (yP, yQ) ≫
      G.map tmiY.inv ≫ facsTot.hom = mch)
    (H13 : oδ ≫ qc ≫ qtot ≫ mch = ord12 ≫ pch) :
    d ≫ muZ1 ≫ TZ.map (Prod.mkHom nA nB) = n0 ≫ G.map muY ≫ sys.hom.app (yA, yB) := by
  have hΦ : IsIso (TZ.map (Prod.mkHom (G.map εP ≫ facsP.hom) (G.map εQ ≫ facsQ.hom))) :=
    inferInstance
  refine (cancel_mono (TZ.map (Prod.mkHom (G.map εP ≫ facsP.hom) (G.map εQ ≫ facsQ.hom)))).1 ?_
  -- the representative form of `H12`
  have : IsIso mch := by
    have := isIso_mkHom facsP.inv facsQ.inv
    rw [← H12]
    infer_instance
  have H12' : G.map tmiY.hom ≫ sys.hom.app (yP, yQ) ≫ TZ.map (Prod.mkHom facsP.hom facsQ.hom) =
      facsTot.hom ≫ inv mch ≫ tmiZ2.hom := by
    rw [← cancel_epi facsTot.inv, Iso.inv_hom_id_assoc, ← cancel_epi mch, IsIso.hom_inv_id_assoc,
      ← H12]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc, ← TZ.map_comp, mkHom_comp_mkHom, Iso.inv_hom_id, Iso.inv_hom_id]
    exact (congrArg (tmiZ2.hom ≫ ·) (TZ.map_id _)).trans (Category.comp_id _)
  have hsys := sys.hom.naturality (Prod.mkHom εP εQ)
  simp only [Functor.comp_map, Functor.prod_map] at hsys
  -- the right hand side
  have hR : (n0 ≫ G.map muY ≫ sys.hom.app (yA, yB)) ≫
      TZ.map (Prod.mkHom (G.map εP ≫ facsP.hom) (G.map εQ ≫ facsQ.hom)) =
      v1 ≫ v2 ≫ εZ0 ≫ oδ ≫ qc ≫ qtot ≫ tmiZ2.hom := by
    have e : TZ.map (Prod.mkHom (G.map εP ≫ facsP.hom) (G.map εQ ≫ facsQ.hom)) =
        TZ.map (Prod.mkHom (G.map εP) (G.map εQ)) ≫ TZ.map (Prod.mkHom facsP.hom facsQ.hom) := by
      rw [← TZ.map_comp, mkHom_comp_mkHom]
    rw [e, Category.assoc, Category.assoc, ← reassoc_of% hsys, ← G.map_comp_assoc, H8]
    simp only [G.map_comp, Category.assoc]
    rw [H12', reassoc_of% H11, ← reassoc_of% H7, reassoc_of% H10.symm, ← reassoc_of% H13,
      IsIso.hom_inv_id_assoc]
  -- the left hand side
  have hL : (d ≫ muZ1 ≫ TZ.map (Prod.mkHom nA nB)) ≫
      TZ.map (Prod.mkHom (G.map εP ≫ facsP.hom) (G.map εQ ≫ facsQ.hom)) =
      v1 ≫ v2 ≫ εZ0 ≫ oδ ≫ qc ≫ qtot ≫ tmiZ2.hom := by
    have e : TZ.map (Prod.mkHom nA nB) ≫
        TZ.map (Prod.mkHom (G.map εP ≫ facsP.hom) (G.map εQ ≫ facsQ.hom)) =
        TZ.map (Prod.mkHom xP xQ) ≫ TZ.map (Prod.mkHom yP' yQ') ≫
          TZ.map (Prod.mkHom oP oQ) := by
      rw [← TZ.map_comp, ← TZ.map_comp, ← TZ.map_comp, mkHom_comp_mkHom,
        mkHom_comp_mkHom, mkHom_comp_mkHom, H1P, H1Q]
    rw [Category.assoc, Category.assoc, e, reassoc_of% H2, reassoc_of% H3, ← H6,
      ← reassoc_of% H4, reassoc_of% H5]
  rw [hL, hR]

/-- Tensor coherence of a pullback comparison transfers along isomorphisms of the inputs. -/
theorem pull_tensor_coherence_of_iso {CY CZ : Type*} [Category CY] [Category CZ]
    [MonoidalCategory CY] [MonoidalCategory CZ] (L : CY ⥤ CZ) [L.OplaxMonoidal]
    (redY : CY ⥤ SY) (redZ : CZ ⥤ SZ) (G : SY ⥤ SZ) (TY : SY × SY ⥤ SY)
    (TZ : SZ × SZ ⥤ SZ)
    (muY : Functor.uncurry.obj (curriedTensor CY) ⋙ redY ≅ (redY.prod redY) ⋙ TY)
    (muZ : Functor.uncurry.obj (curriedTensor CZ) ⋙ redZ ≅ (redZ.prod redZ) ⋙ TZ)
    (nu : L ⋙ redZ ≅ redY ⋙ G) (sys : TY ⋙ G ≅ (G.prod G) ⋙ TZ)
    {A B A' B' : CY} (eA : A' ≅ A) (eB : B' ≅ B)
    (h : redZ.map (Functor.OplaxMonoidal.δ L A' B') ≫ muZ.hom.app (L.obj A', L.obj B') ≫
        TZ.map (Prod.mkHom (nu.hom.app A') (nu.hom.app B')) =
      nu.hom.app (A' ⊗ B') ≫ G.map (muY.hom.app (A', B')) ≫
        sys.hom.app (redY.obj A', redY.obj B')) :
    redZ.map (Functor.OplaxMonoidal.δ L A B) ≫ muZ.hom.app (L.obj A, L.obj B) ≫
        TZ.map (Prod.mkHom (nu.hom.app A) (nu.hom.app B)) =
      nu.hom.app (A ⊗ B) ≫ G.map (muY.hom.app (A, B)) ≫
        sys.hom.app (redY.obj A, redY.obj B) := by
  have hδ := Functor.OplaxMonoidal.δ_natural L eA.hom eB.hom
  have hmuZ := muZ.hom.naturality (Prod.mkHom (L.map eA.hom) (L.map eB.hom))
  have hmuY := muY.hom.naturality (Prod.mkHom eA.hom eB.hom)
  have hnA := nu.hom.naturality eA.hom
  have hnB := nu.hom.naturality eB.hom
  have hnAB := nu.hom.naturality (eA.hom ⊗ₘ eB.hom)
  have hsys := sys.hom.naturality (Prod.mkHom (redY.map eA.hom) (redY.map eB.hom))
  simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    curriedTensor_map_app, curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def]
    at hmuZ hmuY hnA hnB hnAB hsys
  refine (cancel_epi (redZ.map (L.map (eA.hom ⊗ₘ eB.hom)))).1 ?_
  rw [← redZ.map_comp_assoc, ← hδ, redZ.map_comp, Category.assoc, reassoc_of% hmuZ,
    reassoc_of% hnAB]
  have e : TZ.map (Prod.mkHom (redZ.map (L.map eA.hom)) (redZ.map (L.map eB.hom))) ≫
      TZ.map (Prod.mkHom (nu.hom.app A) (nu.hom.app B)) =
      TZ.map (Prod.mkHom (nu.hom.app A') (nu.hom.app B')) ≫
        TZ.map (Prod.mkHom (G.map (redY.map eA.hom)) (G.map (redY.map eB.hom))) := by
    rw [← TZ.map_comp, ← TZ.map_comp, mkHom_comp_mkHom, mkHom_comp_mkHom, hnA, hnB]
  rw [e, reassoc_of% h, ← G.map_comp_assoc, hmuY, G.map_comp, Category.assoc, hsys]

end Generic

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary reduction comparison is invertible on flat representatives. -/
theorem isIso_reductionEpsilon_of_flatRepresentative (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (P : CochainComplex (Modules l E T) ℤ) (hP : FlatRepresentative l E T P) :
    IsIso (reductionEpsilon l E T D R P) := by
  let := D.hasDerived
  let := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  have hc : IsIso (R.counit.app
      (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P)) :=
    R.computes _ hP.1
  dsimp only [reductionEpsilon]
  infer_instance

/-- A tensor comparison of uncurried tensor functors, natural in both variables. -/
private theorem uncurry_tensor_naturality {C S : Type*} [Category C] [MonoidalCategory C]
    [Category S] (red : C ⥤ S) (T : S × S ⥤ S)
    (mu : Functor.uncurry.obj (curriedTensor C) ⋙ red ⟶ (red.prod red) ⋙ T)
    {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
    mu.app (A, B) ≫ T.map (Prod.mkHom (red.map f) (red.map g)) =
      red.map (f ⊗ₘ g) ≫ mu.app (A', B') := by
  have h := mu.naturality (Prod.mkHom f g)
  simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    curriedTensor_map_app, curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def] at h
  exact h.symm

private theorem map_comp_three {C S : Type*} [Category C] [Category S] (F : C ⥤ S)
    {W X X' Y Y' Z : C} {a : W ⟶ X} {b : X ⟶ Y} {c : Y ⟶ Z} {a' : W ⟶ X'} {b' : X' ⟶ Y'}
    {c' : Y' ⟶ Z} (h : a ≫ b ≫ c = a' ≫ b' ≫ c') :
    F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map b' ≫ F.map c' := by
  rw [← F.map_comp, ← F.map_comp, h, F.map_comp, F.map_comp]

private theorem map_comp_four_two {C S : Type*} [Category C] [Category S] (F : C ⥤ S)
    {W X Y V Z X' : C} {a : W ⟶ X} {b : X ⟶ Y} {c : Y ⟶ V} {d : V ⟶ Z} {a' : W ⟶ X'}
    {b' : X' ⟶ Z} (h : a ≫ b ≫ c ≫ d = a' ≫ b') :
    F.map a ≫ F.map b ≫ F.map c ≫ F.map d = F.map a' ≫ F.map b' := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, h, F.map_comp]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
/-- The K-flat tensor model isomorphism of a system calculus is natural. -/
private theorem tensorModelIso_naturality_sys (T : Scheme.{u}) (S : Calculus l E T)
    (P P' Q Q' : CochainComplex (VaryingRing.Modules (rings l E) (transitions l E) T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := sysSite T) (R := sysRing l E T) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (J := sysSite T) (R := sysRing l E T) P')
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := sysSite T) (R := sysRing l E T) Q)
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients (J := sysSite T) (R := sysRing l E T) Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((SemilinearSections.totalTensor.{u + 1, u, u + 1} (sysSite T)
        (sysRing l E T)).map (Prod.mkHom f g)) ≫
      (tensorModelIso.{u + 1, u, u + 1} (sysSite T) (sysRing l E T) S.closed S.tensorModels
        P' Q' hP' hQ').hom =
    (tensorModelIso.{u + 1, u, u + 1} (sysSite T) (sysRing l E T) S.closed S.tensorModels
        P Q hP hQ).hom ≫
      S.closed.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) := by
  let ρ : ObjectProperty (CochainComplex (VaryingRing.Modules (rings l E) (transitions l E) T) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := sysSite T) (R := sysRing l E T)
  let f' : (⟨P, hP⟩ : ρ.FullSubcategory) ⟶ ⟨P', hP'⟩ := ObjectProperty.homMk f
  let g' : (⟨Q, hQ⟩ : ρ.FullSubcategory) ⟶ ⟨Q', hQ'⟩ := ObjectProperty.homMk g
  exact S.tensorModels.comparison.hom.naturality (Prod.mkHom f' g')

set_option maxHeartbeats 1000000 in
-- instantiating the representative chase elaborates all the comparison data at once
/-- The tensor coherence of the pullback reduction comparison on flat representatives.
Source: blueprint, sec-smooth-purity, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1). -/
theorem pull_tensor_coherence_flat (m : DescentModels l E) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (P Q : CochainComplex (Modules l E Y) ℤ) (hP : FlatRepresentative l E Y P)
    (hQ : FlatRepresentative l E Y Q) :
    (red l E m Z).map (Functor.OplaxMonoidal.δ (ringedPull l E g) (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj Q)) ≫
        (m.tensor Z).mu.hom.app ((ringedPull l E g).obj (DerivedCategory.Q.obj P),
          (ringedPull l E g).obj (DerivedCategory.Q.obj Q)) ≫
        (m.systems Z).closed.tensor.map
          (Prod.mkHom ((m.pull g).hom.app (DerivedCategory.Q.obj P))
            ((m.pull g).hom.app (DerivedCategory.Q.obj Q))) =
      (m.pull g).hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        (VaryingRing.G (rings l E) (transitions l E) g).map
          ((m.tensor Y).mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (m.systemPull g).iso.hom.app ((red l E m Y).obj (DerivedCategory.Q.obj P),
          (red l E m Y).obj (DerivedCategory.Q.obj Q)) := by
  obtain ⟨ordinary, hgen, hder⟩ := m.pull_model g
  have hgP := flatRepresentative_pull l E g P hP
  have hgQ := flatRepresentative_pull l E g Q hQ
  have := isIso_reductionEpsilon_of_flatRepresentative l E Y (m.abelian Y) (m.red Y) P hP
  have := isIso_reductionEpsilon_of_flatRepresentative l E Y (m.abelian Y) (m.red Y) Q hQ
  have kP := (m.tensor Y).kflat P hP
  have kQ := (m.tensor Y).kflat Q hQ
  have fP := flatTerms_ordinaryReduction l E Y (m.abelian Y) (m.red Y) P hP
  have fQ := flatTerms_ordinaryReduction l E Y (m.abelian Y) (m.red Y) Q hQ
  have h2 := uncurry_tensor_naturality (red l E m Z) (m.systems Z).closed.tensor
    (m.tensor Z).mu.hom (pullComplexComparison l E g P).hom (pullComplexComparison l E g Q).hom
  have h4 := map_comp_three (red l E m Z) (ringedPull_δ_Q l E g P Q)
  have h5 := reductionEpsilon_naturality Z (m.abelian Z) (m.red Z) (pullTensorChain l E g P Q)
  have h13 := map_comp_four_two DerivedCategory.Q
    (pull_tensor_chain_identity l E m g ordinary hgen P Q)
  exact pull_tensor_representative_chase (VaryingRing.G (rings l E) (transitions l E) g)
    (m.systems Y).closed.tensor (m.systems Z).closed.tensor (m.systemPull g).iso
    (tensorModelIso.{u + 1, u, u + 1} (sysSite Y) (sysRing l E Y) (m.systems Y).closed
      (m.systems Y).tensorModels _ _ kP kQ)
    ((m.tensor Y).localization P Q hP hQ)
    ((VaryingRing.pull (rings l E) (transitions l E) g).mapDerivedCategoryFactors.app _)
    ((VaryingRing.pull (rings l E) (transitions l E) g).mapDerivedCategoryFactors.app _)
    (hder P) (hder Q) h2 ((m.tensor Z).localization _ _ hgP hgQ) h4 h5
    (tensorModelIso.{u + 1, u, u + 1} (sysSite Z) (sysRing l E Z) (m.systems Z).closed
      (m.systems Z).tensorModels _ _ ((m.systemPull g).model.kflat _ kP fP)
      ((m.systemPull g).model.kflat _ kQ fQ))
    (tensorModelIso_naturality_sys l E Z (m.systems Z) _ _ _ _ _ _ _ _ _ _)
    ((m.pull g).hom.naturality (Functor.LaxMonoidal.μ DerivedCategory.Q P Q))
    (hder (P ⊗ Q))
    ((VaryingRing.pull (rings l E) (transitions l E) g).mapDerivedCategoryFactors.app _)
    ((VaryingRing.pull (rings l E) (transitions l E) g).mapDerivedCategoryFactors.hom.naturality
      ((m.tensor Y).chain.hom.app (P, Q)))
    ((m.systemPull g).model.derived _ _ kP kQ fP fQ) h13

variable {l E} in
/-- The pullback reduction comparison is monoidal: under reduction, the tensorator of the
derived pullback `Lg^*` corresponds to the system tensor pullback.
Source: blueprint, sec-smooth-purity, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

Proof: both sides are natural in `A` and `B`, so by `exists_flatRepresentative` it suffices to
treat flat representatives, which is `pull_tensor_coherence_flat`. -/
theorem pull_tensor_coherence_proof (m : DescentModels l E) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (A B : Integral l E Y) :
    (red l E m Z).map (Functor.OplaxMonoidal.δ (ringedPull l E g) A B) ≫
        (m.tensor Z).mu.hom.app ((ringedPull l E g).obj A, (ringedPull l E g).obj B) ≫
        (m.systems Z).closed.tensor.map
          (Prod.mkHom ((m.pull g).hom.app A) ((m.pull g).hom.app B)) =
      (m.pull g).hom.app (A ⊗ B) ≫
        (VaryingRing.G (rings l E) (transitions l E) g).map ((m.tensor Y).mu.hom.app (A, B)) ≫
        (m.systemPull g).iso.hom.app ((red l E m Y).obj A, (red l E m Y).obj B) := by
  obtain ⟨P, hP, ⟨eA⟩⟩ := exists_flatRepresentative _ _ Y A
  obtain ⟨Q, hQ, ⟨eB⟩⟩ := exists_flatRepresentative _ _ Y B
  exact pull_tensor_coherence_of_iso (ringedPull l E g) (red l E m Y) (red l E m Z)
    (VaryingRing.G (rings l E) (transitions l E) g) (m.systems Y).closed.tensor
    (m.systems Z).closed.tensor (m.tensor Y).mu (m.tensor Z).mu (m.pull g)
    (m.systemPull g).iso eA eB (pull_tensor_coherence_flat _ _ m g P Q hP hQ)

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
