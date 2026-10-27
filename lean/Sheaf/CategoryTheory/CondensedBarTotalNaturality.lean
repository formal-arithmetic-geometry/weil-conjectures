/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q33 and E1
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Signed homotopies and naturality of the internal condensed bar total

Source: main-20261015, six-functors direct-images proof, paragraph (3), formal
internal-bar expansion, old step 7 (blueprint: lem-sfb-condensed-bar-total-naturality).

The cochains, double complex, totalization, invariants and augmentations are the
recorded compatible bar data. The conclusions concern the actual normalized
augmentation morphism, without assuming that it is a quasi-isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CondensedBar

variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {F : InternalFunctions A} (B : BarDiagram (G := G) F)
  (V : Invariants A G) (a : Augmentation V B) (t : TotalAugmentation V B a)

/-- The total chain map is postcomposition on each bar summand and commutes with
the invariant augmentation. Identities and composition are retained by the functor
`totalCochains B` itself.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality).

Proof: step 1 of the node. The bar cochains are already an additive functor.
Apply Mathlib's summand formula for the induced total map. The augmentation
square is the naturality equation of the specified total augmentation.
-/
theorem total_chainMap_naturality
    {I J : CochainComplex (Equivariant A G) ℕ} (f : I ⟶ J) :
    (∀ (p q n : ℕ) (h : p + q = n),
      (doubleComplex B I).ιTotal (.up ℕ) p q n h ≫ ((totalCochains B).map f).f n =
        ((cochains B).map (f.f q)).f p ≫ (doubleComplex B J).ιTotal (.up ℕ) p q n h) ∧
    t.map.app I ≫ (totalCochains B).map f =
      (V.functor.mapHomologicalComplex (.up ℕ)).map f ≫ t.map.app J := by
  constructor
  · intro p q n h
    exact HomologicalComplex₂.ιTotal_map _ _
      ((HomologicalComplex₂.flipFunctor _ _ _).map
        (((cochains B).mapHomologicalComplex (.up ℕ)).map f)) (.up ℕ) p q n h
  · exact (t.map.naturality f).symm

private def barComplex :
    CochainComplex (Equivariant A G ⥤+ Modules A) ℕ where
  X p := AdditiveFunctor.of (cochains B ⋙ HomologicalComplex.eval _ _ p)
  d p q := ObjectProperty.homMk
    { app := fun N ↦ ((cochains B).obj N).d p q
      naturality := fun N M f ↦ ((cochains B).map f).comm p q }
  shape p q hpq := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext N
    exact ((cochains B).obj N).shape p q hpq
  d_comp_d' p q r _ _ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext N
    exact ((cochains B).obj N).d_comp_d p q r

private instance barEvaluation_additive :
    ∀ X : Equivariant A G ⥤+ Modules A,
      ((AdditiveFunctor.forget _ _).obj X).Additive := fun X ↦ X.property

private instance barEvaluation_zero :
    ∀ X : Equivariant A G ⥤+ Modules A,
      ((AdditiveFunctor.forget _ _).obj X).PreservesZeroMorphisms := fun X ↦ by
  change X.obj.PreservesZeroMorphisms
  infer_instance

private theorem bar_mapBifunctorMap
    {I J : CochainComplex (Equivariant A G) ℕ} (f : I ⟶ J) :
    HomologicalComplex.mapBifunctorMap (𝟙 (barComplex B)) f
      (AdditiveFunctor.forget _ _) (.up ℕ) = (totalCochains B).map f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp [HomologicalComplex.ι_mapBifunctorMap, totalCochains,
    HomologicalComplex₂.ιTotal_map, barComplex]
  rfl

private theorem bar_ι
    (I : CochainComplex (Equivariant A G) ℕ) (p q n : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor (barComplex B) I
      (AdditiveFunctor.forget _ _) (.up ℕ) p q n hpq =
        (doubleComplex B I).ιTotal (.up ℕ) p q n hpq := by
  rfl

private theorem bar_ι_zero
    (I : CochainComplex (Equivariant A G) ℕ) (p q n : ℕ) :
    HomologicalComplex.ιMapBifunctorOrZero (barComplex B) I
      (AdditiveFunctor.forget _ _) (.up ℕ) p q n =
        (doubleComplex B I).ιTotalOrZero (.up ℕ) p q n := by
  rfl

private def barHomotopy
    {I J : CochainComplex (Equivariant A G) ℕ} {f g : I ⟶ J} (h : Homotopy f g) :
    Homotopy ((totalCochains B).map f) ((totalCochains B).map g) := by
  have H := HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 (barComplex B)) h
    (AdditiveFunctor.forget _ _) (.up ℕ)
  rw [bar_mapBifunctorMap, bar_mapBifunctorMap] at H
  exact H

private theorem barHomotopy_ι
    {I J : CochainComplex (Equivariant A G) ℕ} {f g : I ⟶ J} (h : Homotopy f g)
    (p q n m : ℕ) (hpq : p + q = n) :
    (doubleComplex B I).ιTotal (.up ℕ) p q n hpq ≫ (barHomotopy B h).hom n m =
      (-1 : ℤ) ^ p • (((cochains B).map (h.hom q (q - 1))).f p ≫
        (doubleComplex B J).ιTotalOrZero (.up ℕ) p (q - 1) m) := by
  have hh := HomologicalComplex.mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
    (𝟙 (barComplex B)) h (AdditiveFunctor.forget _ _) (.up ℕ)
    p (q - 1) q n m hpq (by cases q <;> simp)
  rw [bar_ι, bar_ι_zero] at hh
  simpa [barHomotopy, HomologicalComplex.mapBifunctorMapHomotopy₂, barComplex,
    Units.smul_def, Preadditive.zsmul_comp] using hh

private theorem barHomotopy_formula
    {I J : CochainComplex (Equivariant A G) ℕ} {f g : I ⟶ J} (h : Homotopy f g)
    (p q n m : ℕ) (hpq : p + q = n) :
    (doubleComplex B I).ιTotal (.up ℕ) p q n hpq ≫ (barHomotopy B h).hom n m =
      (-1 : ℤ) ^ p • (((cochains B).map (h.hom q (m - p))).f p ≫
        (doubleComplex B J).ιTotalOrZero (.up ℕ) p (m - p) m) := by
  rw [barHomotopy_ι]
  by_cases hm : p + (q - 1) = m
  · have he : m - p = q - 1 := by omega
    rw [he]
  · rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ hm, comp_zero, smul_zero]
    by_cases hmp : p ≤ m
    · rw [h.zero q (m - p) (by change ¬ (m - p + 1 = q); omega),
        Functor.map_zero, HomologicalComplex.zero_f_apply, zero_comp, smul_zero]
    · rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
        change p + (m - p) ≠ m
        omega), comp_zero, smul_zero]

/-- Totalizing a coefficient homotopy multiplies it in bar degree p by (-1)^p.
The use of `ιTotalOrZero` includes the q=0 boundary without a negative term.
Its restriction along the augmentation is precisely the invariant homotopy.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality).

Proof: step 2. Package C^p as a complex of additive functors and apply
Mathlib's bifunctor homotopy theorem to evaluation. Its component is
k^{p,q}=C^p(h^q); naturality gives d_bar k = k d_bar.
The horizontal components of dH+Hd cancel because
their signs are (-1)^p and (-1)^(p+1). The vertical components have two
factors (-1)^p, leaving C^p(d_J h+h d_I)=C^p(f-g). At q=0 the nonexistent
negative-degree component is zero. At p=0 the sign is one and h preserves
fixed sections, giving the displayed compatibility with the augmentation.
-/
theorem total_signedHomotopy
    {I J : CochainComplex (Equivariant A G) ℕ} {f g : I ⟶ J} (h : Homotopy f g) :
    ∃ H : Homotopy ((totalCochains B).map f) ((totalCochains B).map g),
      (∀ (p q n m : ℕ) (hpq : p + q = n),
        (doubleComplex B I).ιTotal (.up ℕ) p q n hpq ≫ H.hom n m =
          (-1 : ℤ) ^ p • (((cochains B).map (h.hom q (m - p))).f p ≫
            (doubleComplex B J).ιTotalOrZero (.up ℕ) p (m - p) m)) ∧
      (∀ n m : ℕ, (t.map.app I).f n ≫ H.hom n m =
        V.functor.map (h.hom n m) ≫ (t.map.app J).f m) := by
  refine ⟨barHomotopy B h, barHomotopy_formula B h, ?_⟩
  intro n m
  rw [t.components, Category.assoc, barHomotopy_formula B h 0 n n m (by simp)]
  simp only [pow_zero, one_smul, Nat.sub_zero]
  rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by simp),
    ← Category.assoc]
  have ha := HomologicalComplex.congr_hom (a.map.naturality (h.hom n m)) 0
  simpa [t.components, Category.assoc] using
    congrArg (fun k ↦ k ≫ (doubleComplex B J).ιTotal (.up ℕ) 0 m m (by simp)) ha.symm

section Localization

variable [HasDerivedCategory.{u + 2} (Modules A)]

/-- The actual bar total followed by extension by zero and ordinary localization.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality). -/
def totalLocalization :
    CochainComplex (Equivariant A G) ℕ ⥤ DerivedCategory.{u + 2} (Modules A) :=
  totalCochains B ⋙ ComplexShape.embeddingUpNat.extendFunctor (Modules A) ⋙
    DerivedCategory.Q.{u + 2}

variable [ActionAbelian A G]

/-- Every module map lifts between specified resolutions; all lifts give the same
localized total map. No total augmentation quasi-isomorphism is used.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality).

Proof: step 3. Mathlib's injective-resolution descent supplies f.
Its nonnegative descent-homotopy theorem compares any two lifts. Apply the
signed total homotopy construction above and extend by zero.
Localization factors through the homotopy category, so the two maps agree.
-/
theorem total_resolution_lifts {N M : Equivariant A G} (u : N ⟶ M)
    (I : InjectiveResolution N) (J : InjectiveResolution M) :
    (∃ f : I.cocomplex ⟶ J.cocomplex,
      I.ι ≫ f = (CochainComplex.single₀ _).map u ≫ J.ι) ∧
    (∀ (f g : I.cocomplex ⟶ J.cocomplex),
      I.ι ≫ f = (CochainComplex.single₀ _).map u ≫ J.ι →
      I.ι ≫ g = (CochainComplex.single₀ _).map u ≫ J.ι →
      (totalLocalization B).map f = (totalLocalization B).map g) := by
  constructor
  · exact ⟨InjectiveResolution.desc u J I, InjectiveResolution.desc_commutes u J I⟩
  · intro f g hf hg
    let H := barHomotopy B (InjectiveResolution.descHomotopy u f g hf hg)
    exact DerivedCategory.Q_map_eq_of_homotopy _
      (H.extend ComplexShape.embeddingUpNat)

/-- Identity lifts between two resolutions give inverse isomorphisms of bar totals.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality).

Proof: step 4. Compose the two identity lifts. Their composites lift the identity,
so lift uniqueness makes them homotopic to the identity chain maps. Their signed
total homotopies become equalities after localization. The displayed inverse
relations identify these actual localized maps as mutually inverse isomorphisms.
-/
theorem total_resolution_change {N : Equivariant A G}
    (I J : InjectiveResolution N) (f : I.cocomplex ⟶ J.cocomplex)
    (g : J.cocomplex ⟶ I.cocomplex) (hf : I.ι ≫ f = J.ι) (hg : J.ι ≫ g = I.ι) :
    IsIso ((totalLocalization B).map f) ∧
    (totalLocalization B).map f ≫ (totalLocalization B).map g = 𝟙 _ ∧
    (totalLocalization B).map g ≫ (totalLocalization B).map f = 𝟙 _ := by
  have hfg : (totalLocalization B).map f ≫ (totalLocalization B).map g = 𝟙 _ := by
    rw [← Functor.map_comp, ← (totalLocalization B).map_id]
    apply (total_resolution_lifts B (𝟙 N) I I).2
    · simp [← Category.assoc, hf, hg]
    · simp
  have hgf : (totalLocalization B).map g ≫ (totalLocalization B).map f = 𝟙 _ := by
    rw [← Functor.map_comp, ← (totalLocalization B).map_id]
    apply (total_resolution_lifts B (𝟙 N) J J).2
    · simp [← Category.assoc, hg, hf]
    · simp
  exact ⟨(⟨_, _, hfg, hgf⟩ :
    (totalLocalization B).obj I.cocomplex ≅
      (totalLocalization B).obj J.cocomplex).isIso_hom, hfg, hgf⟩

/-- The canonical localized maps preserve identities and composition, even when the
chosen lift of a composite differs from the composite of the chosen lifts.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality).

Proof: step 4. An endomorphism lifting the identity is homotopic to the identity.
The composite of lifts of u and v lifts u followed by v. Compare it with any
other lift of that composite using uniqueness and the signed total homotopy.
The functoriality of totalization and localization gives the asserted equations.
-/
theorem total_resolution_functorial :
    (∀ (N : Equivariant A G) (I : InjectiveResolution N)
      (f : I.cocomplex ⟶ I.cocomplex), I.ι ≫ f = I.ι →
        (totalLocalization B).map f = 𝟙 _) ∧
    (∀ (N M L : Equivariant A G) (u : N ⟶ M) (v : M ⟶ L)
      (I : InjectiveResolution N) (J : InjectiveResolution M) (K : InjectiveResolution L)
      (f : I.cocomplex ⟶ J.cocomplex) (g : J.cocomplex ⟶ K.cocomplex)
      (k : I.cocomplex ⟶ K.cocomplex),
      I.ι ≫ f = (CochainComplex.single₀ _).map u ≫ J.ι →
      J.ι ≫ g = (CochainComplex.single₀ _).map v ≫ K.ι →
      I.ι ≫ k = (CochainComplex.single₀ _).map (u ≫ v) ≫ K.ι →
      (totalLocalization B).map k =
        (totalLocalization B).map f ≫ (totalLocalization B).map g) := by
  constructor
  · intro N I f hf
    rw [← (totalLocalization B).map_id]
    apply (total_resolution_lifts B (𝟙 N) I I).2
    · simpa using hf
    · simp
  · intro N M L u v I J K f g k hf hg hk
    rw [← Functor.map_comp]
    apply (total_resolution_lifts B (u ≫ v) I K).2 _ _ hk
    rw [← Category.assoc, hf, Category.assoc, hg, ← Functor.map_comp_assoc]

end Localization

section Derived

variable [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- The specified-resolution augmentation comparison is the canonical invariant
derived-unit comparison followed by the localized actual total augmentation.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality). -/
def augmentationComparison {N : Equivariant A G} (I : InjectiveResolution N) :
    V.functor.rightDerivedFunctor.{u + 2, u + 2}.obj
        ((DerivedCategory.singleFunctor.{u + 2} _ 0).obj N) ⟶
      (totalLocalization B).obj I.cocomplex :=
  (resolutionComparison V I).hom ≫
    DerivedCategory.Q.{u + 2}.map
      (HomologicalComplex.extendMap (t.map.app I.cocomplex) ComplexShape.embeddingUpNat)

variable [hUlim : PreservesFiniteLimits (forgetAction (A := A) (G := G))]
  [hUcolim : PreservesFiniteColimits (forgetAction (A := A) (G := G))]
  [hUinj : (forgetAction (A := A) (G := G)).PreservesInjectiveObjects]

include hUlim hUcolim hUinj

-- Retain the ambient action-category hypotheses of the original public statement.
set_option linter.unusedSectionVars false in
/-- Every bar column has its canonical derived internal-Hom comparison on every
specified resolution. The normalization is RF(Q Uι) followed by the inverse
derived unit, so the comparisons are determined, rather than arbitrary isomorphisms.
Under these comparisons the column map is exactly RF of the underlying module map.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality).

Proof: step 5. The given Grothendieck categories have K-injective
resolutions, which supplies the standing hypothesis of the
ordinary total right derived functor. Exactness of U makes Uι a quasi-isomorphism;
preservation of injectives makes UI a bounded-below injective complex, hence
K-injective. The derived unit is consequently invertible there. Map Uι by RF
and compose with the inverse unit to obtain c. Naturality of the unit and the
augmentation-preserving lift square yield the displayed naturality equation.
The identification of F_p with internal Hom from A[G^p] is part of the recorded
InternalFunctions datum, so this is the prescribed derived internal-Hom map.
-/
theorem total_column_derived_naturality :
    ∃ c : ∀ (p : ℕ) (N : Equivariant A G) (I : InjectiveResolution N),
      (F.functor (power G p)).rightDerivedFunctor.{u + 2, u + 2}.obj
          (DerivedCategory.Q.{u + 2}.obj
            (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
              ((HomologicalComplex.single _ (.up ℤ) 0).obj N))) ≅
        DerivedCategory.Q.{u + 2}.obj
          (((F.functor (power G p)).mapHomologicalComplex (.up ℤ)).obj
            (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
              I.cochainComplex)),
      (∀ (p : ℕ) (N : Equivariant A G) (I : InjectiveResolution N),
        IsIso ((F.functor (power G p)).rightDerivedFunctorUnitQ.{u + 2, u + 2}
          (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
            I.cochainComplex)) ∧
        (c p N I).hom ≫
          (F.functor (power G p)).rightDerivedFunctorUnitQ.{u + 2, u + 2}
            (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
              I.cochainComplex) =
          (F.functor (power G p)).rightDerivedFunctor.{u + 2, u + 2}.map
            (DerivedCategory.Q.{u + 2}.map
              (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).map
                I.ι'))) ∧
      (∀ (p : ℕ) (N M : Equivariant A G) (u : N ⟶ M)
        (I : InjectiveResolution N) (J : InjectiveResolution M)
        (f : I.cocomplex ⟶ J.cocomplex),
        I.ι ≫ f = (CochainComplex.single₀ _).map u ≫ J.ι →
        (F.functor (power G p)).rightDerivedFunctor.{u + 2, u + 2}.map
            (DerivedCategory.Q.{u + 2}.map
              (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).map
                ((HomologicalComplex.single _ (.up ℤ) 0).map u))) ≫ (c p M J).hom =
          (c p N I).hom ≫ DerivedCategory.Q.{u + 2}.map
            (((F.functor (power G p)).mapHomologicalComplex (.up ℤ)).map
              (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).map
                (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)))) := by
  let U := forgetAction (A := A) (G := G)
  let (N : Equivariant A G) (I : InjectiveResolution N) :
      CochainComplex.IsKInjective
        ((U.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) := by
    have : ∀ n : ℤ, Injective
        (((U.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).X n) :=
      fun n ↦ U.injective_obj (I.cochainComplex.X n)
    exact CochainComplex.isKInjective_of_injective _ 0
  let c := fun (p : ℕ) (N : Equivariant A G) (I : InjectiveResolution N) ↦
    (F.functor (power G p)).rightDerivedFunctor.{u + 2, u + 2}.mapIso
      (asIso (DerivedCategory.Q.{u + 2}.map
        ((U.mapHomologicalComplex (.up ℤ)).map I.ι'))) ≪≫
      (F.functor (power G p)).rightDerivedFunctorObjQIso.{u + 2, u + 2}
        ((U.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
  refine ⟨c, ?_, ?_⟩
  · intro p N I
    constructor
    · rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    · simp [c, U, Functor.rightDerivedFunctorUnitQ_eq]
  · intro p N M u I J f hf
    let φ : InjectiveResolution.Hom I J u :=
      ⟨f, HomologicalComplex.congr_hom hf 0⟩
    have hφ := congrArg ((U.mapHomologicalComplex (.up ℤ)).map) φ.ι'_comp_hom'
    simp only [Functor.map_comp, U] at hφ
    dsimp only [c, U, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp]
    erw [← hφ]
    rw [Functor.map_comp, Functor.map_comp, Category.assoc,
      Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_hom]
    exact (Category.assoc _ _ _).symm

-- Keep the original public hypotheses although this proof uses the weaker invariant API.
set_option linter.unusedSectionVars false in
/-- The invariant-source map is precisely RΓ of the module map, and the normalized
augmentation comparison is natural for every chain lift on any two resolutions.
Taking the module map to be the identity gives resolution independence through
the canonical bar-total isomorphisms; arbitrary lifts give the same square.
Source: formal internal-bar expansion, paragraph (3), old step 7
(blueprint: lem-sfb-condensed-bar-total-naturality).

Proof: step 6. Apply the canonical inverse-unit computation of invariants
to the specified equivariant injective resolutions. The derived-unit naturality
square and the lift's augmentation square give the first identity. Localize
the strict total-augmentation square of step 1 and substitute that identity.
The resulting second identity is the naturality square for β_I=Q(b_I)c_I.
Step 3 removes dependence on the lift. Step 4 makes identity lifts between
resolutions inverse isomorphisms, and gives identity and composition coherence.
For u=1 the same equation identifies β on different resolutions; for general u
it is naturality. No invertibility of b_I or β_I is used in this argument.
-/
theorem augmentation_resolution_naturality {N M : Equivariant A G} (u : N ⟶ M)
    (I : InjectiveResolution N) (J : InjectiveResolution M)
    (f : I.cocomplex ⟶ J.cocomplex)
    (hf : I.ι ≫ f = (CochainComplex.single₀ _).map u ≫ J.ι) :
    (V.functor.rightDerivedFunctor.{u + 2, u + 2}.map
        ((DerivedCategory.singleFunctor.{u + 2} _ 0).map u) ≫
      (resolutionComparison V J).hom =
        (resolutionComparison V I).hom ≫
          DerivedCategory.Q.{u + 2}.map
            (HomologicalComplex.extendMap
              ((V.functor.mapHomologicalComplex (.up ℕ)).map f)
              ComplexShape.embeddingUpNat)) ∧
    (V.functor.rightDerivedFunctor.{u + 2, u + 2}.map
        ((DerivedCategory.singleFunctor.{u + 2} _ 0).map u) ≫
      augmentationComparison B V a t J =
        augmentationComparison B V a t I ≫ (totalLocalization B).map f) := by
  let φ : InjectiveResolution.Hom I J u :=
      ⟨f, HomologicalComplex.congr_hom hf 0⟩
  have hφ := φ.ι'_comp_hom'
  have hc : V.functor.rightDerivedFunctor.{u + 2, u + 2}.map
        ((DerivedCategory.singleFunctor.{u + 2} _ 0).map u) ≫
      (resolutionComparison V J).hom =
        (resolutionComparison V I).hom ≫
          DerivedCategory.Q.{u + 2}.map
            (HomologicalComplex.extendMap
              ((V.functor.mapHomologicalComplex (.up ℕ)).map f)
              ComplexShape.embeddingUpNat) := by
    dsimp only [resolutionComparison, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    change V.functor.rightDerivedFunctor.map
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map u)) ≫ _ = _
    rw [← Functor.map_comp_assoc, ← Functor.map_comp, ← hφ,
      Functor.map_comp, Functor.map_comp]
    rw [Category.assoc, Category.assoc,
      V.functor.rightDerivedFunctor_map_Q_map_comp_objQIso_hom_assoc]
    simp only [Category.assoc]
    congr 2
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply HomologicalComplex.hom_ext
    intro n
    exact HomologicalComplex.mapExtensIso_hom_f_naturality _ _ _ _
  refine ⟨hc, ?_⟩
  dsimp only [augmentationComparison, totalLocalization, Functor.comp_map,
    ComplexShape.Embedding.extendFunctor]
  rw [← Category.assoc, hc, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  exact congrArg (fun k ↦ DerivedCategory.Q.map
    (HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)) (t.map.naturality f)

end Derived

end CategoryTheory.CondensedBar
