/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.Algebra.Homology.ExactCouple.Convergence
public import WeilConjectures.Algebra.Homology.ExactCouple.HalfPlane
public import WeilConjectures.Algebra.Homology.ExactCouple.Hom

/-!
# Exact functors carry exact couples and their spectral sequences

Let `Φ : C ⥤ D` be an exact functor between abelian categories and `X = (D, E, α, f, g)` an
exact couple in `C`. Then:

* `X.mapExact Φ = (Φ D, Φ E, Φ α, Φ f, Φ g)` is an exact couple in `D`
  (`CategoryTheory.ExactCouple.mapExact`): an exact functor preserves exact sequences (blueprint
  `lem-sp-exact-functor-preserves-homology`, Mathlib's
  `CategoryTheory.Functor.preservesHomologyOfExact` and `CategoryTheory.ShortComplex.Exact.map`);
* applying `Φ` commutes with taking derived couples: there is a morphism of exact couples
  `Φ (X') ⟶ (Φ X)'` all of whose components are isomorphisms
  (`CategoryTheory.ExactCouple.mapExactDerivedHom`): on `D`-objects it is the comparison of the
  images `Φ (im α) ≅ im (Φ α)`, on `E`-objects the comparison `Φ (H(E, d)) ≅ H(Φ E, Φ d)`;
  iterating, morphisms `Φ (X_r) ⟶ (Φ X)_r` of all the iterated derived couples with invertible
  components (`CategoryTheory.ExactCouple.mapExactDerivedIterHom`), which are compatible with the
  inclusions of the `D`-objects into `Φ D` (`CategoryTheory.ExactCouple.mapExactDerivedIterHom_τD_ιIter`)
  and with all the differentials (being morphisms of exact couples);
* half-plane couples are carried to half-plane couples
  (`CategoryTheory.ExactCouple.IsHalfPlane.mapExact`), and convergence data of the spectral
  sequence of `X` to filtrations `F` of objects `A n` along maps `ι` are carried to convergence
  data of the spectral sequence of `Φ X` to the filtrations `Φ F` of `Φ A n` along `Φ ι`, the
  identifications `E_∞ ≅ gr` being the images under `Φ` of those of `X`
  (`CategoryTheory.ExactCouple.ConvergenceData.mapExact`).

This is blueprint `lem-sp-exact-functor-couple`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

namespace DecreasingFiltration

variable {A : C} (F : DecreasingFiltration A)

/-- The image `Fᵖ (Φ A) = Φ (Fᵖ A)` of a decreasing filtration under an exact functor. -/
noncomputable def mapExact : DecreasingFiltration (Φ.obj A) where
  F p := Subobject.mk (Φ.map (F.F p).arrow)
  F_succ_le p := Subobject.mk_le_mk_of_comm (Φ.map (Subobject.ofLE _ _ (F.F_succ_le p)))
    (by rw [← Φ.map_comp, Subobject.ofLE_arrow])

lemma mapExact_F (p : ℤ) : (F.mapExact Φ).F p = Subobject.mk (Φ.map (F.F p).arrow) := rfl

/-- The graded pieces of the image of a filtration under an exact functor are the images of the
graded pieces: `Φ (grᵖ A) ≅ grᵖ (Φ A)`. -/
noncomputable def mapExactGrIso (p : ℤ) : Φ.obj (F.gr p) ≅ (F.mapExact Φ).gr p :=
  (asIso (cokernelComparison (Subobject.ofLE _ _ (F.F_succ_le p)) Φ)).symm ≪≫
    cokernel.mapIso _ (Subobject.ofLE ((F.mapExact Φ).F (p + 1)) ((F.mapExact Φ).F p)
        ((F.mapExact Φ).F_succ_le p)) (Subobject.underlyingIso _).symm
      (Subobject.underlyingIso _).symm (by
        apply (cancel_mono (Subobject.mk (Φ.map (F.F p).arrow)).arrow).1
        rw [Iso.symm_hom, Iso.symm_hom, assoc, assoc, Subobject.underlyingIso_arrow]
        erw [Subobject.ofLE_arrow, Subobject.underlyingIso_arrow]
        rw [← Φ.map_comp, Subobject.ofLE_arrow])

@[reassoc]
lemma map_cokernelπ_mapExactGrIso_hom (p : ℤ) :
    Φ.map (cokernel.π _) ≫ (F.mapExactGrIso Φ p).hom =
      (Subobject.underlyingIso (Φ.map (F.F p).arrow)).inv ≫ cokernel.π _ := by
  simp [mapExactGrIso]

end DecreasingFiltration

namespace ExactCouple

variable {κ : Type*} [AddCommGroup κ] {a b c : κ}

namespace Hom

/-- The identity morphism of an exact couple. -/
@[simps]
def id (X : ExactCouple C a b c) : Hom X X where
  τD _ := 𝟙 _
  τE _ := 𝟙 _
  commα _ _ := by simp
  commf _ _ := by simp
  commg _ _ := by simp

/-- The composite of two morphisms of exact couples. -/
@[simps]
def comp {X Y Z : ExactCouple C a b c} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  τD i := φ.τD i ≫ ψ.τD i
  τE i := φ.τE i ≫ ψ.τE i
  commα i j := by rw [φ.commα_assoc, ψ.commα, assoc]
  commf i j := by rw [φ.commf_assoc, ψ.commf, assoc]
  commg i j := by rw [φ.commg_assoc, ψ.commg, assoc]

variable {X Y : ExactCouple C a b c} (φ : Hom X Y)

/-- If a morphism of exact couples is an isomorphism on the `D`-objects, so is the induced
morphism of the derived couples. -/
lemma isIso_τD' [∀ i, IsIso (φ.τD i)] (i : κ) : IsIso (φ.τD' i) := by
  have : Mono (φ.τD' i) := mono_of_mono_fac (φ.τD'_ιD i)
  have : Epi (φ.τD' i) := epi_of_epi_fac (φ.πD_τD' i)
  exact isIso_of_mono_of_epi _

/-- If a morphism of exact couples is an isomorphism on the `E`-objects, so is the induced
morphism of complexes `(E, d) ⟶ (E', d')`. -/
lemma isIso_dMap [∀ i, IsIso (φ.τE i)] : IsIso φ.dMap := by
  have : ∀ n, IsIso (φ.dMap.f n) := fun n ↦ by rw [dMap_f]; infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

instance isIso_derived_τD [∀ i, IsIso (φ.τD i)] (i : κ) : IsIso (φ.derived.τD i) :=
  φ.isIso_τD' i

instance isIso_derived_τE [∀ i, IsIso (φ.τE i)] (i : κ) : IsIso (φ.derived.τE i) := by
  have := φ.isIso_dMap
  exact inferInstanceAs (IsIso (HomologicalComplex.homologyMapIso (asIso φ.dMap) i).hom)

end Hom

/-! ### The image of an exact couple under an exact functor -/

/-- The image `Φ X = (Φ D, Φ E, Φ α, Φ f, Φ g)` of an exact couple under an exact functor, an
exact couple (blueprint `lem-sp-exact-functor-couple`, part 1). -/
@[simps]
noncomputable def mapExact (X : ExactCouple C a b c) : ExactCouple D a b c where
  D i := Φ.obj (X.D i)
  E i := Φ.obj (X.E i)
  α i j := Φ.map (X.α i j)
  f i j := Φ.map (X.f i j)
  g i j := Φ.map (X.g i j)
  shape_α i j h := by rw [X.shape_α i j h, Φ.map_zero]
  shape_f i j h := by rw [X.shape_f i j h, Φ.map_zero]
  shape_g i j h := by rw [X.shape_g i j h, Φ.map_zero]
  α_g i j k := by rw [← Φ.map_comp, X.α_g, Φ.map_zero]
  g_f i j k := by rw [← Φ.map_comp, X.g_f, Φ.map_zero]
  f_α i j k := by rw [← Φ.map_comp, X.f_α, Φ.map_zero]
  exact_α_g i j k hij hjk := (X.exact_α_g i j k hij hjk).map Φ
  exact_g_f i j k hij hjk := (X.exact_g_f i j k hij hjk).map Φ
  exact_f_α i j k hij hjk := (X.exact_f_α i j k hij hjk).map Φ

variable (X : ExactCouple C a b c)

lemma mapExact_d (i j : κ) : (X.mapExact Φ).d i j = Φ.map (X.d i j) := by
  simp [d]

/-- The short complexes of `(E, d)` of `Φ X` are the images under `Φ` of those of `X`. -/
noncomputable def mapExactScIso (i : κ) :
    (X.dComplex.sc i).map Φ ≅ (X.mapExact Φ).dComplex.sc i :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [mapExact_d]) (by simp [mapExact_d])

/-- The comparison of cycles `Φ (ker d) ⟶ ker (Φ d)`. -/
noncomputable def mapExactCycles (i : κ) : Φ.obj (X.cycles i) ⟶ (X.mapExact Φ).cycles i :=
  ((X.dComplex.sc i).mapCyclesIso Φ).inv ≫ ShortComplex.cyclesMap (X.mapExactScIso Φ i).hom

@[reassoc (attr := simp)]
lemma mapExactCycles_iCycles (i : κ) :
    X.mapExactCycles Φ i ≫ (X.mapExact Φ).dComplex.iCycles i =
      Φ.map (X.dComplex.iCycles i) := by
  have h := (X.dComplex.sc i).mapCyclesIso_hom_iCycles Φ
  rw [← Iso.eq_inv_comp] at h
  dsimp only [mapExactCycles, HomologicalComplex.iCycles]
  rw [assoc, ShortComplex.cyclesMap_i, h]
  simp [mapExactScIso]

/-- The comparison `Φ (H(E, d)) ≅ H(Φ E, Φ d)` of the `E`-objects of the derived couples. -/
noncomputable def mapExactE'Iso (i : κ) : Φ.obj (X.E' i) ≅ (X.mapExact Φ).E' i :=
  ((X.dComplex.sc i).mapHomologyIso Φ).symm ≪≫ ShortComplex.homologyMapIso (X.mapExactScIso Φ i)

@[reassoc]
lemma map_homologyπ_mapExactE'Iso_hom (i : κ) :
    Φ.map (X.dComplex.homologyπ i) ≫ (X.mapExactE'Iso Φ i).hom =
      X.mapExactCycles Φ i ≫ (X.mapExact Φ).dComplex.homologyπ i := by
  have h := ShortComplex.homologyπ_mapHomologyIso_hom Φ (X.dComplex.sc i)
  have h' : Φ.map (X.dComplex.sc i).homologyπ = ((X.dComplex.sc i).mapCyclesIso Φ).inv ≫
      (((X.dComplex.sc i).map Φ).homologyπ ≫ ((X.dComplex.sc i).mapHomologyIso Φ).hom) :=
    ((Iso.inv_comp_eq _).2 h).symm
  dsimp only [HomologicalComplex.homologyπ]
  rw [mapExactE'Iso, mapExactCycles, Iso.trans_hom, Iso.symm_hom,
    ShortComplex.homologyMapIso_hom, h', assoc, assoc, Iso.hom_inv_id_assoc, assoc,
    ShortComplex.homologyπ_naturality]

/-- The comparison `Φ (im α) ≅ im (Φ α)` of the `D`-objects of the derived couples. -/
noncomputable def mapExactD'Iso (i : κ) : Φ.obj (X.D' i) ≅ (X.mapExact Φ).D' i :=
  haveI : Epi (Φ.map (X.πD i)) := Φ.map_epi _
  haveI : StrongEpi (Φ.map (X.πD i)) := strongEpi_of_epi _
  haveI : Mono (Φ.map (X.ιD i)) := Φ.map_mono _
  image.isoStrongEpiMono (Φ.map (X.πD i)) (Φ.map (X.ιD i))
    (by rw [← Φ.map_comp, X.πD_ιD]; rfl)

@[reassoc (attr := simp)]
lemma mapExactD'Iso_hom_ιD (i : κ) :
    (X.mapExactD'Iso Φ i).hom ≫ (X.mapExact Φ).ιD i = Φ.map (X.ιD i) :=
  haveI : Epi (Φ.map (X.πD i)) := Φ.map_epi _
  haveI : StrongEpi (Φ.map (X.πD i)) := strongEpi_of_epi _
  haveI : Mono (Φ.map (X.ιD i)) := Φ.map_mono _
  image.isoStrongEpiMono_hom_comp_ι (Φ.map (X.πD i)) (Φ.map (X.ιD i)) _

@[reassoc (attr := simp)]
lemma map_πD_mapExactD'Iso_hom (i : κ) :
    Φ.map (X.πD i) ≫ (X.mapExactD'Iso Φ i).hom = (X.mapExact Φ).πD i := by
  rw [← cancel_mono ((X.mapExact Φ).ιD i), assoc, mapExactD'Iso_hom_ιD, ← Φ.map_comp,
    πD_ιD, πD_ιD]
  rfl

@[reassoc (attr := simp)]
lemma map_gCycles_mapExactCycles (l k : κ) :
    Φ.map (X.gCycles l k) ≫ X.mapExactCycles Φ k = (X.mapExact Φ).gCycles l k := by
  rw [← cancel_mono ((X.mapExact Φ).dComplex.iCycles k), assoc, mapExactCycles_iCycles,
    ← Φ.map_comp, gCycles_i, gCycles_i]
  rfl

/-- The comparison morphism `Φ (X') ⟶ (Φ X)'` of exact couples, with invertible components:
the comparison of images `Φ (im α) ≅ im (Φ α)` on `D`-objects and the comparison of homology
`Φ (H(E, d)) ≅ H(Φ E, Φ d)` on `E`-objects (blueprint `lem-sp-exact-functor-couple`, part 2). -/
@[simps]
noncomputable def mapExactDerivedHom : Hom (X.derived.mapExact Φ) (X.mapExact Φ).derived where
  τD i := (X.mapExactD'Iso Φ i).hom
  τE i := (X.mapExactE'Iso Φ i).hom
  commα i j := by
    change Φ.map (X.α' i j) ≫ _ = _ ≫ (X.mapExact Φ).α' i j
    rw [← cancel_mono ((X.mapExact Φ).ιD j), assoc, assoc, mapExactD'Iso_hom_ιD, α'_ιD,
      mapExactD'Iso_hom_ιD_assoc, ← Φ.map_comp, α'_ιD, Φ.map_comp]
    rfl
  commf i j := by
    change Φ.map (X.f' i j) ≫ _ = _ ≫ (X.mapExact Φ).f' i j
    rw [← cancel_mono ((X.mapExact Φ).ιD j), ← cancel_epi (Φ.map (X.dComplex.homologyπ i))]
    simp only [assoc]
    rw [mapExactD'Iso_hom_ιD, ← Φ.map_comp, ← Φ.map_comp, homologyπ_f'_assoc, fCycles_ιD,
      map_homologyπ_mapExactE'Iso_hom_assoc, homologyπ_f'_assoc, fCycles_ιD,
      mapExactCycles_iCycles_assoc, Φ.map_comp]
    rfl
  commg i j := by
    change Φ.map (X.g' i j) ≫ _ = _ ≫ (X.mapExact Φ).g' i j
    rw [← cancel_epi (Φ.map (X.πD i)), map_πD_mapExactD'Iso_hom_assoc, πD_g', ← Φ.map_comp_assoc,
      πD_g', Φ.map_comp_assoc, map_homologyπ_mapExactE'Iso_hom, map_gCycles_mapExactCycles_assoc]

instance (i : κ) : IsIso ((X.mapExactDerivedHom Φ).τD i) := by
  rw [mapExactDerivedHom_τD]
  infer_instance

instance (i : κ) : IsIso ((X.mapExactDerivedHom Φ).τE i) := by
  rw [mapExactDerivedHom_τE]
  infer_instance

/-- The comparison morphisms `Φ (X_n) ⟶ (Φ X)_n` of the iterated derived couples, with
invertible components (blueprint `lem-sp-exact-functor-couple`, part 2): the composites of the
comparisons `Φ (X') ⟶ (Φ X)'` of `CategoryTheory.ExactCouple.mapExactDerivedHom` and of the
morphisms of derived couples induced by the previous comparison. -/
noncomputable def mapExactDerivedIterHom :
    (n : ℕ) → Hom ((X.derivedIter n).mapExact Φ) ((X.mapExact Φ).derivedIter n)
  | 0 => Hom.id _
  | n + 1 => ((X.derivedIter n).mapExactDerivedHom Φ).comp (mapExactDerivedIterHom n).derived

lemma mapExactDerivedIterHom_succ (n : ℕ) :
    X.mapExactDerivedIterHom Φ (n + 1) =
      ((X.derivedIter n).mapExactDerivedHom Φ).comp (X.mapExactDerivedIterHom Φ n).derived :=
  rfl

instance isIso_mapExactDerivedIterHom_τD (n : ℕ) (i : κ) :
    IsIso ((X.mapExactDerivedIterHom Φ n).τD i) := by
  induction n generalizing i with
  | zero => rw [show X.mapExactDerivedIterHom Φ 0 = Hom.id _ from rfl, Hom.id_τD]; infer_instance
  | succ n ih => rw [mapExactDerivedIterHom_succ, Hom.comp_τD]; infer_instance

instance isIso_mapExactDerivedIterHom_τE (n : ℕ) (i : κ) :
    IsIso ((X.mapExactDerivedIterHom Φ n).τE i) := by
  induction n generalizing i with
  | zero => rw [show X.mapExactDerivedIterHom Φ 0 = Hom.id _ from rfl, Hom.id_τE]; infer_instance
  | succ n ih => rw [mapExactDerivedIterHom_succ, Hom.comp_τE]; infer_instance

/-- The comparison `Φ (X_n) ⟶ (Φ X)_n` is compatible with the inclusions of the `D`-objects into
`Φ D`: the `D`-objects of `(Φ X)_n` and the images under `Φ` of those of `X_n` are the same
subobjects of `Φ D` (blueprint `lem-sp-exact-functor-couple`, part 2). -/
@[reassoc]
lemma mapExactDerivedIterHom_τD_ιIter (n : ℕ) (i : κ) :
    (X.mapExactDerivedIterHom Φ n).τD i ≫ (X.mapExact Φ).ιIter n i = Φ.map (X.ιIter n i) := by
  induction n with
  | zero =>
    change 𝟙 _ ≫ 𝟙 _ = Φ.map (𝟙 _)
    rw [Φ.map_id, Category.comp_id]
    rfl
  | succ n ih =>
    rw [mapExactDerivedIterHom_succ, Hom.comp_τD]
    change (_ ≫ (X.mapExactDerivedIterHom Φ n).τD' i) ≫
      ((X.mapExact Φ).derivedIter n).ιD i ≫ (X.mapExact Φ).ιIter n i = _
    rw [assoc, Hom.τD'_ιD_assoc, ih, mapExactDerivedHom_τD, mapExactD'Iso_hom_ιD_assoc,
      ← Φ.map_comp]
    rfl

/-- The differentials of the iterated derived couples of `Φ X` are the images under `Φ` of those
of `X`, through the comparison isomorphisms (blueprint `lem-sp-exact-functor-couple`, part 2). -/
@[reassoc]
lemma map_d_mapExactDerivedIterHom_τE (n : ℕ) (i j : κ) :
    Φ.map ((X.derivedIter n).d i j) ≫ (X.mapExactDerivedIterHom Φ n).τE j =
      (X.mapExactDerivedIterHom Φ n).τE i ≫ ((X.mapExact Φ).derivedIter n).d i j := by
  rw [← mapExact_d]
  exact ((X.mapExactDerivedIterHom Φ n).dMap.comm i j).symm

/-! ### Half-plane couples and convergence -/

section Convergence

variable {b : ℤ × ℤ} {X : ExactCouple C ((-1, 0) : ℤ × ℤ) b 0}

/-- The image of a half-plane couple under an exact functor is a half-plane couple (blueprint
`lem-sp-exact-functor-couple`, part 3). -/
lemma IsHalfPlane.mapExact {a : ℤ} (h : X.IsHalfPlane a) : (X.mapExact Φ).IsHalfPlane a where
  isZero_D p n hpn := Φ.map_isZero (h.isZero_D p n hpn)
  isZero_E p n hpn := Φ.map_isZero (h.isZero_E p n hpn)

variable {A : ℤ → C} {ι : ∀ p n : ℤ, X.D (p, n) ⟶ A n} {F : ∀ n, DecreasingFiltration (A n)}

/-- **Exact functors carry convergence.** If the spectral sequence of `X` converges to the
filtrations `F n` of `A n` along `ι`, then the spectral sequence of `Φ X` converges to the
filtrations `Φ (F n)` of `Φ (A n)` along `Φ ι`, with the same stable pages; the identification
`E_∞^{p, n}(Φ X) ≅ grᵖ (Φ Aⁿ)` is the image under `Φ` of the identification
`E_∞^{p, n}(X) ≅ grᵖ Aⁿ`, through the comparisons `Φ (X_N) ≅ (Φ X)_N` and
`Φ (grᵖ Aⁿ) ≅ grᵖ (Φ Aⁿ)` (blueprint `lem-sp-exact-functor-couple`, part 3). -/
noncomputable def ConvergenceData.mapExact (cd : X.ConvergenceData ι F) :
    (X.mapExact Φ).ConvergenceData (fun p n ↦ Φ.map (ι p n)) (fun n ↦ (F n).mapExact Φ) where
  stage := cd.stage
  d_out p n N hN j := by
    rw [← cancel_epi ((X.mapExactDerivedIterHom Φ N).τE (p, n)), comp_zero,
      ← map_d_mapExactDerivedIterHom_τE, cd.d_out p n N hN, Φ.map_zero, zero_comp]
  d_in p n N hN j := by
    rw [← cancel_epi ((X.mapExactDerivedIterHom Φ N).τE j), comp_zero,
      ← map_d_mapExactDerivedIterHom_τE, cd.d_in p n N hN, Φ.map_zero, zero_comp]
  iso p n N hN := (asIso ((X.mapExactDerivedIterHom Φ N).τE (p, n))).symm ≪≫
    Φ.mapIso (cd.iso p n N hN) ≪≫ (F n).mapExactGrIso Φ p
  comm p n N hN := by
    obtain ⟨φ, hφ₁, hφ₂⟩ := cd.comm p n N hN
    refine ⟨inv ((X.mapExactDerivedIterHom Φ N).τD (p - N, n)) ≫ Φ.map φ ≫
      (Subobject.underlyingIso (Φ.map ((F n).F p).arrow)).inv, ?_, ?_⟩
    · rw [DecreasingFiltration.mapExact_F, assoc, assoc, Subobject.underlyingIso_arrow,
        ← Φ.map_comp, hφ₁, Φ.map_comp, IsIso.inv_comp_eq,
        mapExactDerivedIterHom_τD_ιIter_assoc]
    · have h₁ := (X.mapExactDerivedIterHom Φ N).commg (p - N, n) (p, n)
      simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom]
      rw [← IsIso.eq_inv_comp, ← assoc, ← assoc, IsIso.eq_comp_inv] at h₁
      rw [reassoc_of% h₁, ← Φ.map_comp_assoc, hφ₂, Φ.map_comp_assoc,
        DecreasingFiltration.map_cokernelπ_mapExactGrIso_hom, assoc, assoc]

/-- **Exact functors carry convergence** (blueprint `lem-sp-exact-functor-couple`, part 3). -/
lemma ConvergesTo.mapExact (h : X.ConvergesTo ι F) :
    (X.mapExact Φ).ConvergesTo (fun p n ↦ Φ.map (ι p n)) (fun n ↦ (F n).mapExact Φ) :=
  ⟨h.some.mapExact Φ⟩

end Convergence

end ExactCouple

end CategoryTheory
