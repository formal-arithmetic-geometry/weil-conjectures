/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup
public import Sheaf.Algebra.Homology.DerivedTensorModuleTorComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Algebra.Homology.KunnethCanonicalGradedTensor
import Sheaf.Algebra.Homology.LocalizedFilteredConvergence

/-! # Canonical convolution first page

Source: Stacks Project, Tags 0H7X, 0H7Y and 0H7Z.
(blueprint: lem-kun-canonical-filtered-first-page).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open scoped ZeroObject

namespace DerivedCategory

variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem filteredHomExt {K L : FilteredObject (ModuleCat.{u} R)}
    {f g : K ⟶ L} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

private noncomputable def transportFiltration {A : ModuleCat.{u} R}
    (K : FilteredObject (ModuleCat.{u} R)) (e : K.obj ≅ A) :
    DecreasingFiltration A where
  F i := Subobject.mk ((K.filtration.F i).arrow ≫ e.hom)
  F_succ_le i := Subobject.mk_le_mk_of_comm
    (Subobject.ofLE _ _ (K.filtration.F_succ_le i)) (by
      simp only [Subobject.ofLE_arrow_assoc])

private noncomputable def transportFiltrationIso {A : ModuleCat.{u} R}
    (K : FilteredObject (ModuleCat.{u} R)) (e : K.obj ≅ A) :
    K ≅ (⟨A, transportFiltration R K e⟩ : FilteredObject (ModuleCat.{u} R)) where
  hom :=
    { hom := e.hom
      preserves i := ⟨(Subobject.underlyingIso ((K.filtration.F i).arrow ≫ e.hom)).inv,
        Subobject.underlyingIso_arrow _⟩ }
  inv :=
    { hom := e.inv
      preserves i := ⟨(Subobject.underlyingIso ((K.filtration.F i).arrow ≫ e.hom)).hom,
        by
          change _ = (Subobject.mk ((K.filtration.F i).arrow ≫ e.hom)).arrow ≫ e.inv
          rw [← Subobject.underlyingIso_hom_comp_eq_mk
            ((K.filtration.F i).arrow ≫ e.hom), Category.assoc,
            Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩ }
  hom_inv_id := by
    apply filteredHomExt
    exact e.hom_inv_id
  inv_hom_id := by
    apply filteredHomExt
    exact e.inv_hom_id

private theorem descend_iso (R : Type u) [CommRing R]
    {C : Type*} [Category.{w} C]
    (F G : finiteFilteredModuleDerivedCategory R ⥤ C)
    (e : finiteFilteredDerivedQuotient R ⋙ F ≅ finiteFilteredDerivedQuotient R ⋙ G) :
    ∃ ebar : F ≅ G, ∀ U : CochainComplex.FiniteFilteredModuleComplex R,
      ebar.hom.app ((finiteFilteredDerivedQuotient R).obj U) = e.hom.app U := by
  let q := CochainComplex.finiteFilteredModuleHomotopyQuotient R
  let L := finiteFilteredModuleLocalizationFunctor R
  let W := CochainComplex.finiteFilteredModuleQuasiIso R
  have := Localization.full_whiskeringLeft L W C
  have := Localization.faithful_whiskeringLeft L W C
  let T := (Functor.whiskeringLeft _ _ C).obj L ⋙
    (Functor.whiskeringLeft _ _ C).obj q
  have : T.Full := by
    dsimp only [T, q, CochainComplex.finiteFilteredModuleHomotopyQuotient]
    infer_instance
  have : T.Faithful := by
    dsimp only [T, q, CochainComplex.finiteFilteredModuleHomotopyQuotient]
    infer_instance
  let e' : T.obj F ≅ T.obj G :=
    (Functor.associator q L F).symm ≪≫ e ≪≫ Functor.associator q L G
  refine ⟨T.preimageIso e', ?_⟩
  intro U
  have he := congrArg (fun τ ↦ τ.app U) (T.map_preimage e'.hom)
  change (T.preimage e'.hom).app ((finiteFilteredDerivedQuotient R).obj U) =
    e'.hom.app U at he
  have he' : e'.hom.app U = e.hom.app U := by
    change 𝟙 _ ≫ (e.hom.app U ≫ 𝟙 _) = e.hom.app U
    exact (Category.id_comp _).trans (Category.comp_id _)
  exact he.trans he'

private theorem compareCohomology (d : FilteredPageLocalizationData R)
    (omega : finiteFilteredModuleDerivedCategory R ⥤ DerivedCategory (ModuleCat.{u} R))
    (eForget : ∀ P : CochainComplex.FiniteFilteredModuleComplex R,
      omega.obj ((finiteFilteredDerivedQuotient R).obj P) ≅ Q.obj P.obj.obj)
    (hForget : ∀ {P P' : CochainComplex.FiniteFilteredModuleComplex R} (f : P ⟶ P'),
      omega.map ((finiteFilteredDerivedQuotient R).map f) ≫ (eForget P').hom =
        (eForget P).hom ≫ Q.map f.hom.hom) (n : ℤ) :
    Nonempty (d.Hbar n ⋙ finiteFilteredCohomologyForget R ≅
      omega ⋙ homologyFunctor (ModuleCat.{u} R) n) := by
  let q := finiteFilteredDerivedQuotient R
  let V := finiteFilteredCohomologyForget R
  let H := homologyFunctor (ModuleCat.{u} R) n
  let eF : q ⋙ omega ≅ finiteFilteredComplexForget R ⋙ Q :=
    NatIso.ofComponents eForget (by intro P P' f; exact hForget f)
  let eA : q ⋙ (d.Hbar n ⋙ V) ≅
      finiteFilteredComplexForget R ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n :=
    (Functor.associator q (d.Hbar n) V).symm ≪≫ Functor.isoWhiskerRight (d.eH n) V
  let eB : q ⋙ (omega ⋙ H) ≅
      finiteFilteredComplexForget R ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n :=
    (Functor.associator q omega H).symm ≪≫ Functor.isoWhiskerRight eF H ≪≫
      Functor.associator (finiteFilteredComplexForget R) Q H ≪≫
        Functor.isoWhiskerLeft (finiteFilteredComplexForget R)
          (homologyFunctorFactors (ModuleCat.{u} R) n)
  obtain ⟨e, _⟩ := descend_iso R _ _ (eA ≪≫ eB.symm)
  exact ⟨e⟩

private def pageOneEval (a b : ℤ) :
    CohomologicalSpectralSequence (ModuleCat.{u} R) 1 ⥤ ModuleCat.{u} R where
  obj S := (S.page 1).X (a, b)
  map f := (f.hom 1).f (a, b)
  map_id S := rfl
  map_comp f g := rfl

private theorem comparePageOne (d : FilteredPageLocalizationData R)
    (gr : ℤ → finiteFilteredModuleDerivedCategory R ⥤ DerivedCategory (ModuleCat.{u} R))
    (eGrade : ∀ (i : ℤ) (P : CochainComplex.FiniteFilteredModuleComplex R),
      (gr i).obj ((finiteFilteredDerivedQuotient R).obj P) ≅
        Q.obj (P.obj.filtration.gradedPiece i))
    (hGrade : ∀ (i : ℤ) {P P' : CochainComplex.FiniteFilteredModuleComplex R} (f : P ⟶ P'),
      (gr i).map ((finiteFilteredDerivedQuotient R).map f) ≫ (eGrade i P').hom =
        (eGrade i P).hom ≫ Q.map (FilteredObject.gradedMapSteps f.hom i)) (a b : ℤ) :
    Nonempty (d.Sbar ⋙ pageOneEval R a b ≅
      gr a ⋙ homologyFunctor (ModuleCat.{u} R) (a + b)) := by
  let q := finiteFilteredDerivedQuotient R
  let H := homologyFunctor (ModuleCat.{u} R) (a + b)
  let G : CochainComplex.FiniteFilteredModuleComplex R ⥤
      CochainComplex (ModuleCat.{u} R) ℤ :=
    { obj P := P.obj.filtration.gradedPiece a
      map f := FilteredObject.gradedMapSteps f.hom a
      map_id P := by
        change (kunnethGradedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) a).map (𝟙 P.obj) = _
        exact (kunnethGradedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) a).map_id P.obj
      map_comp f g := by
        change (kunnethGradedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) a).map (f.hom ≫ g.hom) = _
        exact (kunnethGradedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) a).map_comp f.hom g.hom }
  let eG : q ⋙ gr a ≅ G ⋙ Q :=
    NatIso.ofComponents (eGrade a) (by intro P P' f; exact hGrade a f)
  let eP : finiteFilteredPageFunctor R ⋙ pageOneEval R a b ≅
      G ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (a + b) :=
    NatIso.ofComponents (fun P ↦ finiteFilteredPageFirstIso R P a b)
      (by intro P P' f; exact d.page_one_chain f a b)
  let eA : q ⋙ (d.Sbar ⋙ pageOneEval R a b) ≅
      G ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (a + b) :=
    (Functor.associator q d.Sbar (pageOneEval R a b)).symm ≪≫
      Functor.isoWhiskerRight d.eS (pageOneEval R a b) ≪≫ eP
  let eB : q ⋙ (gr a ⋙ H) ≅
      G ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (a + b) :=
    (Functor.associator q (gr a) H).symm ≪≫ Functor.isoWhiskerRight eG H ≪≫
      Functor.associator G Q H ≪≫
        Functor.isoWhiskerLeft G (homologyFunctorFactors (ModuleCat.{u} R) (a + b))
  obtain ⟨e, _⟩ := descend_iso R _ _ (eA ≪≫ eB.symm)
  exact ⟨e⟩

private def indexIso {A : Type*} (P : ℤ → ℤ → A → ModuleCat.{u} R)
    {i j p q : ℤ} (hi : i = p) (hj : j = q) {X : ModuleCat.{u} R} {a : A}
    (e : X ≅ P i j a) : X ≅ P p q a := hi ▸ hj ▸ e

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem indexIso_naturality {A : Type*} (P : ℤ → ℤ → A → ModuleCat.{u} R)
    {a b : A} (m : ∀ i j, P i j a ⟶ P i j b) {i j p q : ℤ}
    (hi : i = p) (hj : j = q) {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    (e : X ≅ P i j a) (e' : Y ≅ P i j b)
    (h : f ≫ e'.hom = e.hom ≫ m i j) :
    f ≫ (indexIso R P hi hj e').hom = (indexIso R P hi hj e).hom ≫ m p q := by
  subst p
  subst q
  exact h

set_option maxHeartbeats 1000000 in
-- Comparing normalized functors carries several dependent coproduct indices.
/-- The canonical convolution filtration realizes the tensor with the cohomological
first-page formula, before its identification with Tor.
Source: Stacks Project, Tags 0H7X and 0H7Y; Tag 0H7Z, the displayed E1 formula
before identifying tensor cohomology with Tor.
(blueprint: lem-kun-canonical-filtered-first-page).

Proof. Apply the declared canonical filtration lift T to both bounded arguments,
then compose with the declared convolution bifunctor star. Compare their forgetful
and graded functors by descent of the natural comparisons on filtered complexes.
The underlying tensor comparison gives omega(U(C,D)) isomorphic to C tensor D,
naturally in both objects. Compare cohomology with d through the normalized cochain
cohomology comparisons; transport the filtration of d.Hbar along the resulting
module isomorphism. Conjugating filtered maps gives the final normalization equation.
The graded convolution comparison expresses gr^a U as a finite biproduct of
gr^i(T C) tensor gr^(a-i)(T D). The canonical graded comparisons identify these
factors with H^-i(C)[i] and H^-(a-i)(D)[a-i]. Cohomology preserves finite biproducts;
the tensor-shift comparison makes its unshifted degree 2a+b. Set a=-q and b=p+2q,
giving degree p, and replace the diagonal index i by -i to obtain cohomology degrees
summing to q. Replace the finite biproduct by the displayed coproduct: all omitted
summands are zero by bounded cohomological support. Use common finite supports for
maps and the support-extension equations. Naturality of these comparisons and
d.page_one gives exactly the displayed coproduct-map equation. This uses neither
Tor nor convergence, and needs no bound on tensor cohomology. -/
theorem exists_kunnethCanonicalFirstPage (d : FilteredPageLocalizationData R) :
    let P (p q : ℤ) (C D : Bounded (ModuleCat.{u} R)) : ModuleCat.{u} R :=
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
        ((kunnethModuleTensorHomology R p).obj
            ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj)
    let m (p q : ℤ) {C C' D D' : Bounded (ModuleCat.{u} R)}
        (f : C ⟶ C') (g : D ⟶ D') : P p q C D ⟶ P p q C' D' :=
      Limits.Sigma.map fun ij ↦
        ((kunnethModuleTensorHomology R p).map
            ((homologyFunctor (ModuleCat.{u} R) ij.val.1).map f.hom)).app
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj) ≫
          ((kunnethModuleTensorHomology R p).obj
            ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C'.obj)).map
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).map g.hom)
    ∃ (U : Bounded (ModuleCat.{u} R) ⥤ Bounded (ModuleCat.{u} R) ⥤
          finiteFilteredModuleDerivedCategory R)
      (F : ∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        DecreasingFiltration ((homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj)))
      (eH : ∀ (C D : Bounded (ModuleCat.{u} R)) (n : ℤ),
        (d.Hbar n).obj ((U.obj C).obj D) ≅
          (⟨(homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj),
            F C D n⟩ : FilteredObject (ModuleCat.{u} R)))
      (e₁ : ∀ (C D : Bounded (ModuleCat.{u} R)) (p q : ℤ),
        ((d.Sbar.obj ((U.obj C).obj D)).page 1).X (-q, p + 2 * q) ≅ P p q C D),
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D')
          (p q : ℤ),
        ((d.Sbar.map ((U.map f).app D ≫ (U.obj C').map g)).hom 1).f (-q, p + 2 * q) ≫
            (e₁ C' D' p q).hom =
          (e₁ C D p q).hom ≫ m p q f g) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D') (n : ℤ),
        ∃ h : (⟨(homologyFunctor (ModuleCat.{u} R) n).obj (C.obj ⊗ D.obj), F C D n⟩ :
            FilteredObject (ModuleCat.{u} R)) ⟶
          ⟨(homologyFunctor (ModuleCat.{u} R) n).obj (C'.obj ⊗ D'.obj), F C' D' n⟩,
          h.hom = (homologyFunctor (ModuleCat.{u} R) n).map (f.hom ⊗ₘ g.hom) ∧
          (d.Hbar n).map ((U.map f).app D ≫ (U.obj C').map g) ≫ (eH C' D' n).hom =
            (eH C D n).hom ≫ h) := by
  dsimp only
  obtain ⟨omega, gr, eForget, eGrade, U, eTensor, eGr,
    hForget, hGrade, hTensor, hGr⟩ := exists_kunnethCanonicalGradedTensor R
  let P (p q : ℤ) (C D : Bounded (ModuleCat.{u} R)) : ModuleCat.{u} R :=
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
        ((kunnethModuleTensorHomology R p).obj
            ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj)
  let m (p q : ℤ) {C C' D D' : Bounded (ModuleCat.{u} R)}
        (f : C ⟶ C') (g : D ⟶ D') : P p q C D ⟶ P p q C' D' :=
      Limits.Sigma.map fun ij ↦
        ((kunnethModuleTensorHomology R p).map
            ((homologyFunctor (ModuleCat.{u} R) ij.val.1).map f.hom)).app
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj) ≫
          ((kunnethModuleTensorHomology R p).obj
            ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C'.obj)).map
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).map g.hom)
  let eC (n : ℤ) := (compareCohomology R d omega eForget hForget n).some
  let e (C D : Bounded (ModuleCat.{u} R)) (n : ℤ) :=
    (eC n).app ((U.obj C).obj D) ≪≫
      (homologyFunctor (ModuleCat.{u} R) n).mapIso (eTensor C D)
  let F (C D : Bounded (ModuleCat.{u} R)) (n : ℤ) :=
    transportFiltration R ((d.Hbar n).obj ((U.obj C).obj D)) (e C D n)
  let eH (C D : Bounded (ModuleCat.{u} R)) (n : ℤ) :=
    transportFiltrationIso R ((d.Hbar n).obj ((U.obj C).obj D)) (e C D n)
  let eP (a b : ℤ) := (comparePageOne R d gr eGrade hGrade a b).some
  let e₀ (C D : Bounded (ModuleCat.{u} R)) (a b : ℤ) :=
    (eP a b).app ((U.obj C).obj D) ≪≫ eGr C D (a + b) a
  let PP (p q : ℤ) (CD : Bounded (ModuleCat.{u} R) × Bounded (ModuleCat.{u} R)) :=
    P p q CD.1 CD.2
  let e₁ (C D : Bounded (ModuleCat.{u} R)) (p q : ℤ) :=
    indexIso R PP (show -q + (p + 2 * q) + -q = p by omega) (neg_neg q)
      (a := (C, D)) (e₀ C D (-q) (p + 2 * q))
  refine ⟨U, F, eH, e₁, ?_, ?_⟩
  · intro C C' D D' f g p q
    have h₀ (a b : ℤ) :
        ((d.Sbar.map ((U.map f).app D ≫ (U.obj C').map g)).hom 1).f (a, b) ≫
            (e₀ C' D' a b).hom =
          (e₀ C D a b).hom ≫ m (a + b + a) (-a) f g := by
      dsimp only [e₀, Iso.trans_hom, Iso.app_hom]
      rw [← Category.assoc]
      have h := (eP a b).hom.naturality ((U.map f).app D ≫ (U.obj C').map g)
      change ((d.Sbar.map ((U.map f).app D ≫ (U.obj C').map g)).hom 1).f (a, b) ≫
          (eP a b).hom.app ((U.obj C').obj D') =
        (eP a b).hom.app ((U.obj C).obj D) ≫
          (homologyFunctor (ModuleCat.{u} R) (a + b)).map
            ((gr a).map ((U.map f).app D ≫ (U.obj C').map g)) at h
      rw [h, Category.assoc, hGr C C' D D' f g (a + b) a]
      rfl
    exact indexIso_naturality R PP (a := (C, D)) (b := (C', D'))
      (fun i j ↦ m i j f g)
      (show -q + (p + 2 * q) + -q = p by omega) (neg_neg q)
      _ _ _ (h₀ (-q) (p + 2 * q))
  · intro C C' D D' f g n
    let t := (U.map f).app D ≫ (U.obj C').map g
    let h : (⟨_, F C D n⟩ : FilteredObject (ModuleCat.{u} R)) ⟶ ⟨_, F C' D' n⟩ :=
      (eH C D n).inv ≫ (d.Hbar n).map t ≫ (eH C' D' n).hom
    have hn : (d.Hbar n).map t ≫ (eH C' D' n).hom = (eH C D n).hom ≫ h := by
      dsimp only [h]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    refine ⟨h, ?_, hn⟩
    have he : ((d.Hbar n).map t).hom ≫ (e C' D' n).hom =
        (e C D n).hom ≫ (homologyFunctor (ModuleCat.{u} R) n).map (f.hom ⊗ₘ g.hom) := by
      dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
      rw [← Category.assoc]
      have hc := (eC n).hom.naturality t
      change ((d.Hbar n).map t).hom ≫ (eC n).hom.app _ = _ at hc
      rw [hc, Category.assoc]
      dsimp only [Functor.comp_map]
      rw [← Functor.map_comp, hTensor C C' D D' f g,
        Functor.map_comp]
      exact (Category.assoc _ _ _).symm
    change (e C D n).inv ≫ ((d.Hbar n).map t).hom ≫ (e C' D' n).hom = _
    rw [he, Iso.inv_hom_id_assoc]

end DerivedCategory
