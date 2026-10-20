/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalageTower
public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
import Sheaf.CategoryTheory.CartanEilenbergDecalageSpectralObjectIso
import Sheaf.CategoryTheory.SpectralObjectBottomIsoCriterion

/-! # The Cartan--Eilenberg decalage spectral object

Source: Stacks Project, Tags 015X and 015K.
(blueprint: lem-sp-ce-decalage-spectral-object).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Normalized truncated augmentations commute with every specified cutoff inclusion.
Source: Stacks Project, Tag 015X, Remark 13.26.15
(blueprint: lem-sp-ce-decalage-spectral-object).

Proof. Compose with the monic inclusion of the larger truncation. Both sides then
become the original augmentation after the smaller inclusion. Cancel the mono. -/
theorem cartanEilenberg_truncatedAugmentation_square
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {F : A ⥤ B} [F.Additive] (P : CartanEilenbergPresentation F) (q r : ℤ)
    (u : CochainComplex.truncLE
        ((F.mapHomologicalComplex (.up ℤ)).obj
          (P.J.cocomplex.extend ComplexShape.embeddingUpNat)) q ⟶
      CochainComplex.truncLE
        ((F.mapHomologicalComplex (.up ℤ)).obj
          (P.J.cocomplex.extend ComplexShape.embeddingUpNat)) r)
    (v : CochainComplex.truncLE P.I q ⟶ CochainComplex.truncLE P.I r)
    (hu : u ≫ CochainComplex.ιTruncLE _ r = CochainComplex.ιTruncLE _ q)
    (hv : v ≫ CochainComplex.ιTruncLE P.I r = CochainComplex.ιTruncLE P.I q)
    (a : ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.truncLE
          ((F.mapHomologicalComplex (.up ℤ)).obj
            (P.J.cocomplex.extend ComplexShape.embeddingUpNat)) q) ⟶
      CochainComplex.truncLE P.I q)
    (b : ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.truncLE
          ((F.mapHomologicalComplex (.up ℤ)).obj
            (P.J.cocomplex.extend ComplexShape.embeddingUpNat)) r) ⟶
      CochainComplex.truncLE P.I r)
    (ha : a ≫ CochainComplex.ιTruncLE P.I q =
      ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.ιTruncLE _ q) ≫ P.e)
    (hb : b ≫ CochainComplex.ιTruncLE P.I r =
      ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.ιTruncLE _ r) ≫ P.e) :
    a ≫ v = ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map u ≫ b := by
  have : Mono (CochainComplex.ιTruncLE P.I r) :=
    inferInstanceAs (Mono (HomologicalComplex.ιTruncLE P.I
      (ComplexShape.embeddingUpIntLE r)))
  apply (cancel_mono (CochainComplex.ιTruncLE P.I r)).1
  rw [Category.assoc, hv, ha, Category.assoc, hb, ← Category.assoc,
    ← Functor.map_comp, hu]

/-- The coordinate normalization makes total augmentations natural in every
commuting square of horizontally indexed complexes, including cutoff inclusions.
Source: Stacks Project, Tag 015X, Remark 13.26.15
(blueprint: lem-sp-ce-decalage-spectral-object).

Proof. In degree n the source augmentation lands in the summand (n,0).
Naturality of this total summand inclusion and of extension by zero reduces the
square to the degree-(n,0) component of the given augmentation square. -/
theorem cartanEilenberg_totalAugmentation_square
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {K L : CochainComplex B ℤ}
    {I J : HomologicalComplex₂ B (.up ℤ) (.up ℕ)}
    (a : ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).obj K ⟶ I)
    (b : ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).obj L ⟶ J)
    (u : K ⟶ L) (v : I ⟶ J)
    (h : a ≫ v = ((CochainComplex.single₀ B).mapHomologicalComplex (.up ℤ)).map u ≫ b)
    (augK : K ⟶ ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).total (.up ℤ))
    (augL : L ⟶ ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj J).total (.up ℤ))
    (hK : ∀ n : ℤ, augK.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 B).mapHomologicalComplex (.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj I).ιTotal
        (.up ℤ) n 0 n (add_zero n))
    (hL : ∀ n : ℤ, augL.f n = (b.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 B).mapHomologicalComplex (.up ℕ)).obj (J.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).obj J).ιTotal
        (.up ℤ) n 0 n (add_zero n)) :
    augK ≫ HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor (𝟭 B)).map v) (.up ℤ) =
      u ≫ augL := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, hK, hL]
  rw [Category.assoc, Category.assoc, HomologicalComplex₂.ιTotal_map]
  change (a.f n).f 0 ≫ _ ≫
    (HomologicalComplex.extendMap (v.f n) ComplexShape.embeddingUpNat).f 0 ≫ _ = _
  rw [HomologicalComplex.extendMap_f (v.f n)
    ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hh := congrArg (fun z ↦ (z.f n).f 0) h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀_map_f_zero] at hh
  rw [← Category.assoc ((a.f n).f 0), hh, Category.assoc]

/-- Mapping cones of the decalage tower of a mapped CE total compute the derived
truncation intervals, including their connecting morphisms and comparison maps.
Source: Stacks Project, Tag 015X, Remark 13.26.15, and Tag 015K, Remark 13.21.4.
(blueprint: lem-sp-ce-decalage-spectral-object).

Proof. Before applying G, identify Dec(V)^(-q) with the total of the horizontal smart truncation
at q. On each diagonal all summands with horizontal degree below q remain, the degree-q summand
is replaced by its horizontal cycles, and higher summands vanish. The proved
totalTruncLEToDecalage_isIso identifies this step, and totalTruncLEToDecalage_naturality handles
presentation comparisons. The unique truncated CE augmentation is a quasi-isomorphism into this
bounded-below injective total. The same argument applies to every interval: horizontal cycles
and boundaries are injective, so the step inclusions split in each degree. Apply G, using
preservation of cycles and the finite-diagonal total comparison. The derived-functor unit at
these injective totals identifies the tower with RG of the upper smart truncations of F(J). The
proved rightDerivedFunctorPlusResolutionIso_naturality fixes these comparisons already in the
bounded-below derived category and makes their augmentation squares commute. The proved
cartanEilenberg_truncatedAugmentation_square gives compatibility with cutoff inclusions. The
proved cartanEilenberg_totalAugmentation_square transports these normalized squares to totals,
as it does for presentation comparisons. The proved rightDerivedFunctorPlusResolutionNatIso
computes the entire diagram of specified injective resolutions simultaneously. The proved
cochainTruncLEQIso_naturality and cochainTruncLEQIso_of_le identify these coherently with the
canonical derived truncations. In particular, the tower at integer q is RG of the cochain
truncation at q-1, hence RG of the canonical derived truncation strictly below q, as required by
the Grothendieck spectral object. For each pair of cutoffs take the functorial mapping cone of
their inclusion and the cone map of their augmentation square. The proved
mappingConeMap_quasiIso and mappingCone_injective show that it is a quasi-isomorphism into a
bounded-below complex of injectives. The proved rightDerivedFunctorPlusConeResolutionNatIso
computes all these interval cone resolutions naturally. Apply the additive-functor mapping-cone
comparison to identify their mapped cones with the cones of the mapped tower. In the source
derived category, the cone of tau_<a X -> tau_<b X is identified with tau_>=a tau_<b X by
comparing its triangle with the truncation triangle of tau_<b X at a. Use the identity on
tau_<b X and the normalized identification tau_<a tau_<b X = tau_<a X on the first term.
The resulting third map is unique: its possible differences factor through a map from
(tau_<a X)[1] to tau_>=a tau_<b X, which vanishes by t-structure orthogonality. Hence
commuting cutoff squares induce the canonical interval maps. For three cutoffs use the
mapping-cone octahedral triangles and the corresponding truncation triangles; uniqueness
makes their interval squares commute. Their last arrows are the triangle connecting arrows,
so these squares fix the signs as well. Apply the triangulated right derived functor only
after these comparisons, preserving the triangle squares and their connecting arrows. At minus
infinity both towers are zero. At plus infinity use the untruncated CE total augmentation,
which is a bounded-below injective resolution of F(J). Its normalization gives the same inclusion
and comparison squares
as at finite cutoffs. Finally identify F(J) in the derived category with RF(X) via the
injective-resolution comparison for the specified injective resolution J of X. Apply cohomology
to get the spectral object isomorphism. The augmentation squares give its naturality; arbitrary
filtered lifts with the stated total map agree by their monic step inclusions. -/
theorem cartanEilenberg_decalage_spectralObject
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
    (hL : ∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
      (L P).complexStep p n =
        ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) :
    ∃ e : ∀ P : CartanEilenbergPresentation F,
      (filteredComplexDecalageSpectralObjectFunctor C).obj
          (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ≅
        F.grothendieckSpectralObject G P.X,
      ∀ (P Q : CartanEilenbergPresentation F) (d : P.Comparison Q)
        (t : (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
          (⟨Q.total G, L Q⟩ : FilteredObject (CochainComplex C ℤ))),
        t.hom = HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ) →
        (filteredComplexDecalageSpectralObjectFunctor C).map t ≫ (e Q).hom =
          (e P).hom ≫ (F.grothendieckSpectralObjectFunctor G).map d.f := by
  obtain ⟨f, hf, hnat⟩ := cartanEilenberg_decalage_spectralObject_iso_exists F G L hL
  have (P : CartanEilenbergPresentation F) : IsIso (f P) :=
    Abelian.SpectralObject.isIso_of_bottom_intervals (f P) (hf P)
  refine ⟨fun P ↦ asIso (f P), ?_⟩
  intro P Q d t ht
  exact hnat P Q d t ht

end CategoryTheory
