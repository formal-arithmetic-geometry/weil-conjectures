/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionCoefficientUnits
import all WeilConjectures.Algebra.Homology.TotalTensorSigns.TotalTensorHomotopyConeSigns

/-! # Raw coordinates of the strict Koszul/Roos comparison

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.5.5 (comparison a)
(blueprint: lem-sp-perfect-reduction-koszul-delta-raw-data).

The comparison maps from the total tensor of the two-term Koszul complex with a strict Roos
limit to the strict Roos limit of the levelwise tensor tower, together with their shifted
(signed) and unshifted coordinate formulas. That these maps are isomorphisms is the separate
statement `nonempty_koszulDeltaIso`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wR wA
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings
namespace CategoryTheory.PerfectReductionRoos
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

/-- Chain maps `K ⊗ R lim P ⟶ R lim (K ⊗ P)` for the Koszul complexes `K = principalKoszul R t m`,
with their coordinates on every summand `K^p ⊗ (R lim P)^(i+1)`: into the shifted product the
coordinate is `(-1)^p` times the tensor of the shifted Roos coordinate, into the unshifted product
it is the tensor of the unshifted Roos coordinate. Since the summands `ι` are jointly epimorphic
and the products and biproduct are jointly monomorphic, the two formulas determine `hom`.
Source: Bhatt--Scholze 3.5.5 (blueprint: lem-sp-perfect-reduction-koszul-delta-raw-data). -/
structure KoszulDeltaRawData where
  hom : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ⟶
    roosF.obj (tensorTower R (principalKoszul R t m) P)
  shifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
          (hom m P).f (n + 1) ≫
          (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
            (op k)) j).f n =
        p.negOnePow • ((tensor R).obj ((principalKoszul R t m).X p)).map
          ((roosχ P i).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f i) ≫
          ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p i n (by omega)
  unshifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
          (hom m P).f (n + 1) ≫
          (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
            (op k)) j).f (n + 1) =
        ((tensor R).obj ((principalKoszul R t m).X p)).map
          ((roosχ P i).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
          ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) h

omit [HasSheafify J CommRingCat]
  [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)] in
section

private def tensorProductComparison (K : CochainComplex (RegularQuotientCone.Modules R) ℤ)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) :
    ((total R).obj K).obj (roosP P) ⟶ roosP (tensorTower R K P) :=
  piComparison ((total R).obj K) (fun j : ℕ ↦ P.asFunctor.obj (op j))

private theorem tensorProductComparison_π
    (K : CochainComplex (RegularQuotientCone.Modules R) ℤ)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) (n : ℤ) (j : ℕ) :
    (tensorProductComparison R K P).f n ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R K P).asFunctor.obj (op k)) j).f n =
      (((total R).obj K).map
        (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j)).f n := by
  exact congrArg (fun f ↦ f.f n)
    (piComparison_comp_π ((total R).obj K) (fun k : ℕ ↦ P.asFunctor.obj (op k)) j)

private theorem tensorProductComparison_u
    (K : CochainComplex (RegularQuotientCone.Modules R) ℤ)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) :
    ((total R).obj K).map (roosU P) ≫ tensorProductComparison R K P =
      tensorProductComparison R K P ≫ roosU (tensorTower R K P) := by
  let F := (total R).obj K
  change F.map (roosU P) ≫ piComparison F _ = piComparison F _ ≫
    towerTransitionEndomorphism
      (fun j : ℕ ↦ F.map (P.asFunctor.map (homOfLE (Nat.le_succ j)).op))
  apply Pi.hom_ext
  intro j
  simp [roosU, towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, Functor.map_comp]

private def tensorRoosHom (K : CochainComplex (RegularQuotientCone.Modules R) ℤ)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) :
    ((total R).obj K).obj (roosF.obj P) ⟶ roosF.obj (tensorTower R K P) :=
  (shiftLeft R K (CochainComplex.mappingCone (roosU P)) (-1)).hom ≫
    (coneLeft R K (roosU P)).hom⟦(-1 : ℤ)⟧' ≫
    (CochainComplex.mappingCone.map _ _ (tensorProductComparison R K P)
      (tensorProductComparison R K P) (tensorProductComparison_u R K P))⟦(-1 : ℤ)⟧'

omit [HasCountableProducts (RegularQuotientCone.Modules R)] in
private theorem tensorCone_fst
    (K X Y : CochainComplex (RegularQuotientCone.Modules R) ℤ) (f : X ⟶ Y)
    (p q n : ℤ) (h : p + q = n) :
    ι R K (CochainComplex.mappingCone f) p q n h ≫ (coneLeft R K f).hom.f n ≫
        (CochainComplex.mappingCone.fst (((total R).obj K).map f)).1.v
          n (n + 1) rfl =
      p.negOnePow • (((tensor R).obj (K.X p)).map
        ((CochainComplex.mappingCone.fst f).1.v q (q + 1) rfl) ≫
          ι R K X p (q + 1) (n + 1) (by omega)) := by
  let F := (tensor R).obj (K.X p)
  have hi := congrArg F.map (CochainComplex.mappingCone.id_X f q (q + 1) rfl)
  simp only [Functor.map_add, Functor.map_comp, Functor.map_id] at hi
  calc
    _ = (F.map ((CochainComplex.mappingCone.fst f).1.v q (q + 1) rfl) ≫
        F.map ((CochainComplex.mappingCone.inl f).v (q + 1) q (by omega)) +
        F.map ((CochainComplex.mappingCone.snd f).v q q (add_zero q)) ≫
        F.map ((CochainComplex.mappingCone.inr f).f q)) ≫
        ι R K (CochainComplex.mappingCone f) p q n h ≫ (coneLeft R K f).hom.f n ≫
        (CochainComplex.mappingCone.fst (((total R).obj K).map f)).1.v
          n (n + 1) rfl := by rw [hi, Category.id_comp]
    _ = _ := by
      simp only [Preadditive.add_comp, Category.assoc]
      have h₁ : F.map ((CochainComplex.mappingCone.inl f).v (q + 1) q (by omega)) ≫
          ι R K (CochainComplex.mappingCone f) p q n h ≫ (coneLeft R K f).hom.f n =
          p.negOnePow • (ι R K X p (q + 1) (n + 1) (by omega) ≫
            (CochainComplex.mappingCone.inl (((total R).obj K).map f)).v
              (n + 1) n (by omega)) := by
        exact Generic.coneLeft_ι (RegularQuotientCone.Modules R) K f p q n h
      have h₂ : F.map ((CochainComplex.mappingCone.inr f).f q) ≫
          ι R K (CochainComplex.mappingCone f) p q n h ≫ (coneLeft R K f).hom.f n =
          ι R K Y p q n h ≫
            (CochainComplex.mappingCone.inr (((total R).obj K).map f)).f n := by
        exact Generic.coneLeft_inr_ι (RegularQuotientCone.Modules R) K f p q n h
      rw [reassoc_of% h₁, reassoc_of% h₂]
      simp [F, Linear.comp_units_smul, Linear.units_smul_comp]

omit [HasCountableProducts (RegularQuotientCone.Modules R)] in
private theorem tensorCone_snd
    (K X Y : CochainComplex (RegularQuotientCone.Modules R) ℤ) (f : X ⟶ Y)
    (p q n : ℤ) (h : p + q = n) :
    ι R K (CochainComplex.mappingCone f) p q n h ≫ (coneLeft R K f).hom.f n ≫
        (CochainComplex.mappingCone.snd (((total R).obj K).map f)).v n n (add_zero n) =
      ((tensor R).obj (K.X p)).map
        ((CochainComplex.mappingCone.snd f).v q q (add_zero q)) ≫
          ι R K Y p q n h := by
  let F := (tensor R).obj (K.X p)
  have hi := congrArg F.map (CochainComplex.mappingCone.id_X f q (q + 1) rfl)
  simp only [Functor.map_add, Functor.map_comp, Functor.map_id] at hi
  calc
    _ = (F.map ((CochainComplex.mappingCone.fst f).1.v q (q + 1) rfl) ≫
        F.map ((CochainComplex.mappingCone.inl f).v (q + 1) q (by omega)) +
        F.map ((CochainComplex.mappingCone.snd f).v q q (add_zero q)) ≫
        F.map ((CochainComplex.mappingCone.inr f).f q)) ≫
        ι R K (CochainComplex.mappingCone f) p q n h ≫ (coneLeft R K f).hom.f n ≫
        (CochainComplex.mappingCone.snd (((total R).obj K).map f)).v n n (add_zero n) := by
          rw [hi, Category.id_comp]
    _ = _ := by
      simp only [Preadditive.add_comp, Category.assoc]
      have h₁ : F.map ((CochainComplex.mappingCone.inl f).v (q + 1) q (by omega)) ≫
          ι R K (CochainComplex.mappingCone f) p q n h ≫ (coneLeft R K f).hom.f n =
          p.negOnePow • (ι R K X p (q + 1) (n + 1) (by omega) ≫
            (CochainComplex.mappingCone.inl (((total R).obj K).map f)).v
              (n + 1) n (by omega)) := by
        exact Generic.coneLeft_ι (RegularQuotientCone.Modules R) K f p q n h
      have h₂ : F.map ((CochainComplex.mappingCone.inr f).f q) ≫
          ι R K (CochainComplex.mappingCone f) p q n h ≫ (coneLeft R K f).hom.f n =
          ι R K Y p q n h ≫
            (CochainComplex.mappingCone.inr (((total R).obj K).map f)).f n := by
        exact Generic.coneLeft_inr_ι (RegularQuotientCone.Modules R) K f p q n h
      rw [reassoc_of% h₁, reassoc_of% h₂]
      simp [F, Linear.units_smul_comp]

omit [EssentiallySmall.{r} C] in
private theorem roosChi_fst
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) (i : ℤ) :
    (roosχ P i).hom ≫ biprod.fst =
      ((CochainComplex.mappingCone (roosU P)).shiftFunctorObjXIso
        (-1) (i + 1) i (by omega)).hom ≫
      (CochainComplex.mappingCone.snd (roosU P)).v i i (add_zero i) := by
  have hs : HomologicalComplex.homotopyCofiber.sndX (roosU P) i =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU P) i (i + 1) rfl).hom ≫
        biprod.snd := by
    apply HomologicalComplex.homotopyCofiber.ext_from_X (roosU P) (i + 1) i rfl
    · simp
    · simp
  simp [roosχ, CochainComplex.mappingCone.snd,
    CochainComplex.HomComplex.Cochain.ofHoms, hs]

omit [EssentiallySmall.{r} C] in
private theorem roosChi_snd
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ) (i : ℤ) :
    (roosχ P i).hom ≫ biprod.snd =
      ((CochainComplex.mappingCone (roosU P)).shiftFunctorObjXIso
        (-1) (i + 1) i (by omega)).hom ≫
      (CochainComplex.mappingCone.fst (roosU P)).1.v i (i + 1) rfl := by
  simp [roosχ, CochainComplex.mappingCone.fst,
    HomologicalComplex.homotopyCofiber.fstX]

omit [EssentiallySmall.{r} C]
  [HasCountableProducts (RegularQuotientCone.Modules R)] in
private theorem coneMap_fst {X Y X' Y' : CochainComplex (RegularQuotientCone.Modules R) ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (n : ℤ) :
    (CochainComplex.mappingCone.map f g a b h).f n ≫
        (CochainComplex.mappingCone.fst g).1.v n (n + 1) rfl =
      (CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
  rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc_f _ _ _ _ n
    (n + 1) rfl]
  simp [Preadditive.add_comp, Category.assoc]

omit [EssentiallySmall.{r} C]
  [HasCountableProducts (RegularQuotientCone.Modules R)] in
private theorem coneMap_snd {X Y X' Y' : CochainComplex (RegularQuotientCone.Modules R) ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (n : ℤ) :
    (CochainComplex.mappingCone.map f g a b h).f n ≫
        (CochainComplex.mappingCone.snd g).v n n (add_zero n) =
      (CochainComplex.mappingCone.snd f).v n n (add_zero n) ≫ b.f n := by
  rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc_f _ _ _ _ n
    (n + 1) rfl]
  simp [Preadditive.add_comp, Category.assoc]

omit [EssentiallySmall.{r} C]
  [HasCountableProducts (RegularQuotientCone.Modules R)] in
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
private theorem shiftMap_naturality
    {X Y : CochainComplex (RegularQuotientCone.Modules R) ℤ} (f : X ⟶ Y) (n : ℤ) :
    (f⟦(-1 : ℤ)⟧').f (n + 1) ≫
        (Y.shiftFunctorObjXIso (-1) (n + 1) n (by omega)).hom =
      (X.shiftFunctorObjXIso (-1) (n + 1) n (by omega)).hom ≫ f.f n := by
  exact HomologicalComplex.XIsoOfEq_hom_naturality f
    (show (n + 1) + (-1 : ℤ) = n by omega)

omit [HasCountableProducts (RegularQuotientCone.Modules R)] in
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
private theorem tensor_ι_map
    (K X Y : CochainComplex (RegularQuotientCone.Modules R) ℤ) (f : X ⟶ Y)
    (p q n : ℤ) (h : p + q = n) :
    ι R K X p q n h ≫ (((total R).obj K).map f).f n =
      ((tensor R).obj (K.X p)).map (f.f q) ≫ ι R K Y p q n h := by
  simpa only [ι, total, CochainComplex.ιMapBifunctor,
    Functor.map₂CochainComplex, Functor.map₂HomologicalComplex,
    HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp,
    tensor, MonoidalCategory.curriedTensor] using
    (HomologicalComplex.ι_mapBifunctorMap (𝟙 K) f (tensor R) (.up ℤ) p q n h)

private theorem tensorRoosHom_shifted
    (K : CochainComplex (RegularQuotientCone.Modules R) ℤ)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ)
    (i p n : ℤ) (h : p + (i + 1) = n + 1) :
    ι R K (roosF.obj P) p (i + 1) (n + 1) h ≫
        (tensorRoosHom R K P).f (n + 1) ≫
        (roosχ (tensorTower R K P) n).hom ≫ biprod.fst =
      p.negOnePow • (((tensor R).obj (K.X p)).map
        ((roosχ P i).hom ≫ biprod.fst) ≫
          ι R K (roosP P) p i n (by omega) ≫ (tensorProductComparison R K P).f n) := by
  simp only [tensorRoosHom, HomologicalComplex.comp_f, Category.assoc]
  dsimp only [roosF, roosConeFunctor, Functor.comp_obj]
  rw [roosChi_fst, reassoc_of% (shiftMap_naturality (R := R)),
    coneMap_snd, reassoc_of% (shiftMap_naturality (R := R))]
  dsimp only [ι, shiftLeft]
  rw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc K
    (CochainComplex.mappingCone (roosU P)) (tensor R) (-1)
    p (i + 1) (n + 1) h i n (by omega) (by omega)]
  dsimp only [total, Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Linear.units_smul_comp]
  have hc := tensorCone_snd R K (roosP P) (roosP P) (roosU P) p i n (by omega)
  dsimp only [ι, total, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex] at hc
  rw [reassoc_of% hc]
  rw [roosChi_fst, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  simp

private theorem tensorRoosHom_unshifted
    (K : CochainComplex (RegularQuotientCone.Modules R) ℤ)
    (P : CochainComplex (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R) ℤ)
    (i p n : ℤ) (h : p + (i + 1) = n + 1) :
    ι R K (roosF.obj P) p (i + 1) (n + 1) h ≫
        (tensorRoosHom R K P).f (n + 1) ≫
        (roosχ (tensorTower R K P) n).hom ≫ biprod.snd =
      ((tensor R).obj (K.X p)).map ((roosχ P i).hom ≫ biprod.snd) ≫
        ι R K (roosP P) p (i + 1) (n + 1) h ≫
          (tensorProductComparison R K P).f (n + 1) := by
  simp only [tensorRoosHom, HomologicalComplex.comp_f, Category.assoc]
  dsimp only [roosF, roosConeFunctor, Functor.comp_obj]
  rw [roosChi_snd, reassoc_of% (shiftMap_naturality (R := R)),
    coneMap_fst, reassoc_of% (shiftMap_naturality (R := R))]
  dsimp only [ι, shiftLeft]
  rw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc K
    (CochainComplex.mappingCone (roosU P)) (tensor R) (-1)
    p (i + 1) (n + 1) h i n (by omega) (by omega)]
  dsimp only [total, Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Linear.units_smul_comp]
  have hc := tensorCone_fst R K (roosP P) (roosP P) (roosU P) p i n (by omega)
  dsimp only [ι, total, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex] at hc
  rw [reassoc_of% hc]
  rw [roosChi_snd, Functor.map_comp]
  simp [Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]

end

/-- The raw finite Koszul/Roos comparison maps exist with their two coordinate formulas.
Source: Bhatt--Scholze, Lemma 3.5.5, comparison a.

Proof: in total degree `n+1` the source is the coproduct of the summands
`K^p ⊗ (R lim P)^(i+1)` with `p + (i+1) = n+1` (only `p ∈ {-1, 0}` are nonzero), and
`(R lim P)^(i+1) = ∏_j P_j^i ⊞ ∏_j P_j^(i+1)`; the target in degree `n+1` is
`∏_j (K ⊗ P_j)^n ⊞ ∏_j (K ⊗ P_j)^(n+1)`. Define `hom` on each summand by the displayed
formulas: tensor the Roos coordinate with `K^p`, include it as the summand of `K ⊗ P_j`, and
multiply the shifted component by `(-1)^p` (the total tensor sign moving the degree shift
past `K^p`). Checking the chain-map equation on each summand and coordinate is the sign
calculation of the total tensor differential against the Roos differential `1 - transition`:
the Koszul differential has degree `p` constant on the factor, the Roos differential commutes
with `K^p ⊗ -`, and the sign `(-1)^p` is exactly the one of the total differential on the
shifted factor. The two fields are then the defining formulas.
(blueprint: lem-sp-perfect-reduction-koszul-delta-raw-data) -/
theorem nonempty_koszulDeltaRawData
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) : Nonempty (KoszulDeltaRawData R t) := by
  -- Retain the original hypotheses and section-instance interface.
  have _ := ht
  have _ := c
  have _ := (inferInstance : HasDerivedCategory.{wR}
    (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R))
  have _ := (inferInstance : ∀ m, HasDerivedCategory.{wA}
    (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m)))
  have _ := (inferInstance : ∀ m, HasCountableProducts
    (RegularQuotientCone.Modules (powerRing R t m)))
  refine ⟨{ hom := fun m P ↦ tensorRoosHom R (principalKoszul R t m) P
            shifted := ?_, unshifted := ?_ }⟩
  · intro m P i p n h j
    rw [reassoc_of% tensorRoosHom_shifted]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [tensorProductComparison_π]
    congr 1
    rw [tensor_ι_map]
    simp [Functor.map_comp, Category.assoc]
  · intro m P i p n h j
    rw [reassoc_of% tensorRoosHom_unshifted]
    rw [tensorProductComparison_π]
    rw [tensor_ι_map]
    simp [Functor.map_comp, Category.assoc]
end CategoryTheory.PerfectReductionRoos
