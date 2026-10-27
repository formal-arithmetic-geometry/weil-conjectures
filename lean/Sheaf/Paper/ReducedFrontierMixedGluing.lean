/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.ExtensionByZeroPunctual
public import Sheaf.Paper.SfCommonStageDirectImage
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.ZlImmersionFilteredReductionTransport
import Sheaf.Paper.ZlWeilHeartLocalizationExact
import Sheaf.Paper.ClopenPrescribedWeilFiltration
import Sheaf.Paper.ZlWeilPullCompositorEquivariance
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCompIso
import Sheaf.Paper.WeilMixedUpperBounds
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Mixed Weil filtrations along a reduced closed frontier

Source: main-20261015, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, final three paragraphs
(blueprint: lem-zl-reduced-frontier-mixed-gluing).

The structures below only package the hypotheses and clauses of this lemma. Closed
image is tied to the recorded derived direct image and its actual adjunction unit.
Open image and every restriction are the existing canonical Weil-heart functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The given reduced frontier, with all maps over the fixed finite field. The
first term is the reduction, identified over X, and the last has empty underlying
space. Finite component sets may be empty. Finite type and separatedness of these
subschemes are inherited from X; bundling them records these inherited structures.
Source: source paragraphs 6--9 (blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
structure ZlReducedFrontier (D : FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k₀))) where
  length : ℕ
  closed : Fin (length + 1) → Over (Spec (.of D.k₀))
  [closed_ft : ∀ a, LocallyOfFiniteType (closed a).hom]
  [closed_qc : ∀ a, QuasiCompact (closed a).hom]
  [closed_sep : ∀ a, IsSeparated (closed a).hom]
  reduced : ∀ a, IsReduced (closed a).left
  ambient : ∀ a, closed a ⟶ X
  [ambient_closed : ∀ a, IsClosedImmersion (ambient a).left]
  reduction : (closed 0).left ≅ X.left.nilradical.subscheme
  reduction_over : reduction.hom ≫ X.left.nilradical.subschemeι = (ambient 0).left
  finish : IsEmpty (closed (Fin.last length)).left
  inclusion : ∀ a : Fin length, closed a.succ ⟶ closed a.castSucc
  [inclusion_closed : ∀ a, IsClosedImmersion (inclusion a).left]
  ambient_next : ∀ a : Fin length, inclusion a ≫ ambient a.castSucc = ambient a.succ
  difference : Fin length → Over (Spec (.of D.k₀))
  [difference_ft : ∀ a, LocallyOfFiniteType (difference a).hom]
  [difference_qc : ∀ a, QuasiCompact (difference a).hom]
  [difference_sep : ∀ a, IsSeparated (difference a).hom]
  openInclusion : ∀ a : Fin length, difference a ⟶ closed a.castSucc
  [open_inclusion : ∀ a, IsOpenImmersion (openInclusion a).left]
  complement : ∀ a, Set.range (openInclusion a).left = (Set.range (inclusion a).left)ᶜ
  count : Fin length → ℕ
  piece : ∀ a : Fin length, Fin (count a) → Over (Spec (.of D.k₀))
  [piece_ft : ∀ a b, LocallyOfFiniteType (piece a b).hom]
  [piece_qc : ∀ a b, QuasiCompact (piece a b).hom]
  [piece_sep : ∀ a b, IsSeparated (piece a b).hom]
  pieceInclusion : ∀ (a : Fin length) (b : Fin (count a)), piece a b ⟶ difference a
  [piece_open : ∀ a b, IsOpenImmersion (pieceInclusion a b).left]
  [piece_closed : ∀ a b, IsClosedImmersion (pieceInclusion a b).left]
  cover : ∀ a, ⋃ b, Set.range (pieceInclusion a b).left = Set.univ
  disjoint : ∀ a b c, b ≠ c →
    Disjoint (Set.range (pieceInclusion a b).left) (Set.range (pieceInclusion a c).left)

attribute [instance] ZlReducedFrontier.closed_ft ZlReducedFrontier.closed_qc
  ZlReducedFrontier.closed_sep ZlReducedFrontier.ambient_closed
  ZlReducedFrontier.inclusion_closed ZlReducedFrontier.difference_ft
  ZlReducedFrontier.difference_qc ZlReducedFrontier.difference_sep
  ZlReducedFrontier.open_inclusion ZlReducedFrontier.piece_ft ZlReducedFrontier.piece_qc
  ZlReducedFrontier.piece_sep ZlReducedFrontier.piece_open ZlReducedFrontier.piece_closed

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Exact preservation of an individual finite filtration, with precisely its
assigned pure quotient weights, as well as preservation of a mixed upper bound.
No strictness is imposed on the inclusions, and length zero is permitted.
Source: source final paragraph (blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
structure ZlFrontierFiltrationPreservation
    {Y X : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (iota : Ω ≃+* ℂ)
    (T : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω) : Prop where
  additive : T.Additive
  finiteLimits : PreservesFiniteLimits T
  finiteColimits : PreservesFiniteColimits T
  filtration : ∀ (m : ℕ) (G : Fin (m + 1) → sfCommonStageWeilSheaf D l hl Y Ω)
    (φ : ∀ s : Fin m, G s.castSucc ⟶ G s.succ) (weights : Fin m → ℝ),
    IsZero (G 0) → (∀ s, Mono (φ s)) →
    (∀ s, SfIsPunctuallyPureOfWeight D l hl Ω Y iota (cokernel (φ s)) (weights s)) →
      IsZero (T.obj (G 0)) ∧ (∀ s, Mono (T.map (φ s))) ∧
      ∀ s, SfIsPunctuallyPureOfWeight D l hl Ω X iota
        (cokernel (T.map (φ s))) (weights s)
  mixed : ∀ (G : sfCommonStageWeilSheaf D l hl Y Ω) (w : ℝ),
    SfIsMixedOfWeightsAtMost D l hl Ω Y iota G w →
      SfIsMixedOfWeightsAtMost D l hl Ω X iota (T.obj G) w

variable {Y X : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Closed direct image in the constructible Weil heart, specified by its recorded
derived carrier and adjunction unit. This is a presentation of the actual direct
image, not an arbitrary functor or an arbitrary isomorphism of objects.
Source: source final paragraph (blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
structure ZlFrontierClosedImage (iota : Ω ≃+* ℂ) (i : Y ⟶ X)
    [IsClosedImmersion i.left] where
  functor : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω
  carrier : functor ⋙ ObjectProperty.ι _ =
    ObjectProperty.ι _ ⋙ sfModelWeilDerivedPush D l hl Ω i
  adjunction : zlWeilPull D l hl Ω i ⊣ functor
  unit_normalization : ∀ F : sfCommonStageWeilSheaf D l hl X Ω,
    HEq ((ObjectProperty.ι _).map (adjunction.unit.app F))
      ((sfModelWeilDerivedAdjunction D l hl Ω i).unit.app F.obj)
  preservation : ZlFrontierFiltrationPreservation D l hl Ω iota functor

/-- The canonical open adjunction already used to define zlOpenWeilShriek.
Source: source final paragraph (blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
def zlFrontierOpenAdjunction (j : Y ⟶ X) [IsOpenImmersion j.left] :
    zlOpenWeilShriek D l hl Ω j ⊣ zlWeilPull D l hl Ω j :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (zlWeilPull D l hl Ω j)
    (zlOpenWeilPull_isRightAdjoint D l hl Ω j)

/-- The localization sequence uses the actual open counit and closed unit.
The last restriction is i*F; inverse-image composition identifies this with the
restriction to the next member of the frontier.
Source: displayed sequence in source final paragraph
(blueprint: lem-zl-reduced-frontier-mixed-gluing). -/
def ZlFrontierLocalization (iota : Ω ≃+* ℂ) {Z : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (j : Y ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]
    (P : ZlFrontierClosedImage D l hl Ω iota i)
    (F : sfCommonStageWeilSheaf D l hl X Ω) : Prop :=
  ∃ h : (zlFrontierOpenAdjunction D l hl Ω j).counit.app F ≫
      P.adjunction.unit.app F = 0,
    (ShortComplex.mk ((zlFrontierOpenAdjunction D l hl Ω j).counit.app F)
      (P.adjunction.unit.app F) h).ShortExact

omit [IsSeparated X.hom] in
private theorem frontierPureIso (iota : Ω ≃+* ℂ) (w : ℝ)
    {A B : sfCommonStageWeilSheaf D l hl X Ω} (e : A ≅ B)
    (h : SfIsPunctuallyPureOfWeight D l hl Ω X iota A w) :
    SfIsPunctuallyPureOfWeight D l hl Ω X iota B w := by
  intro y α hα
  obtain ⟨L, K, ⟨a⟩, rest⟩ := hα
  exact h y α ⟨L, K, ⟨(ObjectProperty.ι _).mapIso e ≪≫ a⟩, rest⟩

omit [IsSeparated X.hom] in
private theorem frontierMixedIso (iota : Ω ≃+* ℂ) (w : ℝ)
    {A B : sfCommonStageWeilSheaf D l hl X Ω} (e : A ≅ B)
    (h : SfIsMixedOfWeightsAtMost D l hl Ω X iota A w) :
    SfIsMixedOfWeightsAtMost D l hl Ω X iota B w := by
  obtain ⟨n, G, φ, h0, ⟨last⟩, hm, hp⟩ := h
  exact ⟨n, G, φ, h0, ⟨last ≪≫ e⟩, hm, hp⟩

omit [IsSeparated X.hom] [IsSeparated Y.hom] in
private theorem frontierPreservation (iota : Ω ≃+* ℂ)
    (T : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω)
    (h : ZlImmersionImageFiltration D l hl Ω iota T) :
    ZlFrontierFiltrationPreservation D l hl Ω iota T := by
  let := h.1
  let := h.2.1
  have ha : T.Additive := Functor.additive_of_preserves_binary_products T
  refine ⟨ha, h.1, h.2.1, ?_, h.2.2.2.2⟩
  intro n G φ weights h0 hm hp
  refine ⟨T.map_isZero h0, ?_, ?_⟩
  · intro s
    let := hm s
    infer_instance
  · intro s
    exact frontierPureIso D l hl Ω iota (weights s) (PreservesCokernel.iso T (φ s))
      (h.2.2.1 _ _ (hp s))

omit [IsSeparated X.hom] [IsSeparated Y.hom] in
private theorem frontierPreservationIso (iota : Ω ≃+* ℂ)
    {T U : sfCommonStageWeilSheaf D l hl Y Ω ⥤ sfCommonStageWeilSheaf D l hl X Ω}
    (e : T ≅ U) (h : ZlImmersionImageFiltration D l hl Ω iota T) :
    ZlFrontierFiltrationPreservation D l hl Ω iota U := by
  let := h.1
  let := h.2.1
  have : PreservesFiniteLimits U := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits U := preservesFiniteColimits_of_natIso e
  have ha : U.Additive := Functor.additive_of_preserves_binary_products U
  refine ⟨ha, inferInstance, inferInstance, ?_, ?_⟩
  · intro n G φ weights h0 hm hp
    refine ⟨U.map_isZero h0, ?_, ?_⟩
    · intro s
      let := hm s
      infer_instance
    · intro s
      apply frontierPureIso D l hl Ω iota (weights s) (PreservesCokernel.iso U (φ s))
      exact frontierPureIso D l hl Ω iota (weights s) (e.app _)
        (h.2.2.1 _ _ (hp s))
  · intro G w hm
    exact frontierMixedIso D l hl Ω iota w (e.app _) (h.2.2.2.2 G w hm)

private theorem frontierClosedImage (iota : Ω ≃+* ℂ)
    (i : Y ⟶ X) [IsClosedImmersion i.left] :
    ∃ P : ZlFrontierClosedImage D l hl Ω iota i,
      Surjective i.left → ∀ H, IsIso (P.adjunction.unit.app H) := by
  obtain ⟨J, adjJ, I, adj, hc, hn, _, hi, hs⟩ :=
    zlImmersionFilteredReductionTransport D l hl Ω iota (𝟙 X) i
  exact ⟨⟨I, hc, adj, hn, frontierPreservation D l hl Ω iota I hi⟩,
    fun h H ↦ (hs h H).1⟩

private theorem frontierOpenPreservation (iota : Ω ≃+* ℂ)
    (j : Y ⟶ X) [IsOpenImmersion j.left] :
    ZlFrontierFiltrationPreservation D l hl Ω iota (zlOpenWeilShriek D l hl Ω j) := by
  obtain ⟨J, adjJ, I, adj, _, _, hj, _, _⟩ :=
    zlImmersionFilteredReductionTransport D l hl Ω iota j (𝟙 X)
  exact frontierPreservationIso D l hl Ω iota
    (adjJ.leftAdjointUniq (zlFrontierOpenAdjunction D l hl Ω j)) hj

private theorem frontierLocalization (iota : Ω ≃+* ℂ)
    {Z : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (j : Y ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X) [IsClosedImmersion i.left]
    (hc : Set.range j.left = (Set.range i.left)ᶜ)
    (P : ZlFrontierClosedImage D l hl Ω iota i)
    (F : sfCommonStageWeilSheaf D l hl X Ω) :
    ZlFrontierLocalization D l hl Ω iota j i P F := by
  obtain ⟨L⟩ := (zlWeilHeartLocalizationExact D l hl Ω iota
    (X₀ := X) (U₀ := Y) (Z₀ := Z)).2.2.1 j i hc
  let e := L.open_adjunction.leftAdjointUniq (zlFrontierOpenAdjunction D l hl Ω j)
  let d := L.closed_adjunction.rightAdjointUniq P.adjunction
  have he := Adjunction.leftAdjointUniq_hom_app_counit L.open_adjunction
    (zlFrontierOpenAdjunction D l hl Ω j) F
  have hd := Adjunction.unit_rightAdjointUniq_hom_app L.closed_adjunction P.adjunction F
  obtain ⟨h, hs⟩ := L.localization F
  have h' : (zlFrontierOpenAdjunction D l hl Ω j).counit.app F ≫
      P.adjunction.unit.app F = 0 := by
    apply (cancel_epi (e.hom.app ((zlWeilPull D l hl Ω j).obj F))).1
    change e.hom.app _ ≫ _ = e.hom.app _ ≫ 0
    rw [← Category.assoc, he, ← hd, ← Category.assoc, h, zero_comp, comp_zero]
  refine ⟨h', ShortComplex.shortExact_of_iso ?_ hs⟩
  exact ShortComplex.isoMk (e.app _) (Iso.refl F) (d.app _)
    (by
      change e.hom.app _ ≫ _ = _ ≫ 𝟙 F
      simpa only [Category.comp_id] using he)
    (by
      change 𝟙 F ≫ _ = _ ≫ d.hom.app _
      simpa only [Category.id_comp] using hd.symm)

omit [IsSeparated X.hom] in
private theorem frontierMixedZero (iota : Ω ≃+* ℂ) (w : ℝ)
    (F : sfCommonStageWeilSheaf D l hl X Ω) (h : IsZero F) :
    SfIsMixedOfWeightsAtMost D l hl Ω X iota F w := by
  refine ⟨0, fun _ ↦ F, fun s ↦ s.elim0, h, ⟨Iso.refl _⟩, ?_, ?_⟩
  · intro s
    exact s.elim0
  · intro s
    exact s.elim0

omit [IsSeparated X.hom] in
private theorem frontierMixedMono (iota : Ω ≃+* ℂ) {w w' : ℝ} (hw : w ≤ w')
    {F : sfCommonStageWeilSheaf D l hl X Ω}
    (h : SfIsMixedOfWeightsAtMost D l hl Ω X iota F w) :
    SfIsMixedOfWeightsAtMost D l hl Ω X iota F w' := by
  obtain ⟨n, G, φ, h0, last, hm, hp⟩ := h
  exact ⟨n, G, φ, h0, last, hm, fun s ↦
    let ⟨v, hv, hp⟩ := hp s
    ⟨v, hv.trans hw, hp⟩⟩

omit [IsSeparated X.hom] in
private theorem frontierMixedExtension (iota : Ω ≃+* ℂ) (w : ℝ)
    (S : ShortComplex (sfCommonStageWeilSheaf D l hl X Ω)) (hs : S.ShortExact)
    (hA : SfIsMixedOfWeightsAtMost D l hl Ω X iota S.X₁ w)
    (hC : SfIsMixedOfWeightsAtMost D l hl Ω X iota S.X₃ w) :
    SfIsMixedOfWeightsAtMost D l hl Ω X iota S.X₂ w := by
  let := hs.mono_f
  apply SfIsMixedOfWeightsAtMost.of_mono_cokernel D l hl Ω X iota w S.f hA
  exact frontierMixedIso D l hl Ω iota w
    (IsColimit.coconePointUniqueUpToIso hs.gIsCokernel (colimit.isColimit _)) hC

private theorem frontierClopenMixed (iota : Ω ≃+* ℂ)
    (N : ℕ) (V : Fin N → Over (Spec (.of D.k₀)))
    [∀ b, LocallyOfFiniteType (V b).hom] [∀ b, QuasiCompact (V b).hom]
    [∀ b, IsSeparated (V b).hom]
    (j : ∀ b, V b ⟶ X)
    [∀ b, IsOpenImmersion (j b).left] [∀ b, IsClosedImmersion (j b).left]
    (cover : ⋃ b, Set.range (j b).left = Set.univ)
    (disjoint : ∀ b c, b ≠ c → Disjoint (Set.range (j b).left) (Set.range (j c).left))
    (F : sfCommonStageWeilSheaf D l hl X Ω) (w : ℝ)
    (h : ∀ b, SfIsMixedOfWeightsAtMost D l hl Ω (V b) iota
      ((zlWeilPull D l hl Ω (j b)).obj F) w) :
    SfIsMixedOfWeightsAtMost D l hl Ω X iota F w := by
  classical
  choose n G φ h0 last hm hp using h
  choose weights hw hq using hp
  obtain ⟨J, adj, A, ψ, position, _, _, _, _, _, mixed, _⟩ :=
    clopen_prescribed_weil_filtration D l hl Ω iota X N V j cover disjoint F
      n G φ weights h0 last hm hq
  exact mixed w hw

private theorem frontierLiftComposition
    {A B C : Type*} [Category A] [Category B] [Category C]
    (P : ObjectProperty A) (Q : ObjectProperty B) (R : ObjectProperty C)
    (f : A ⥤ B) (g : B ⥤ C) (h : A ⥤ C)
    (hf : ∀ K : P.FullSubcategory, Q (f.obj K.obj))
    (hg : ∀ K : Q.FullSubcategory, R (g.obj K.obj))
    (hh : ∀ K : P.FullSubcategory, R (h.obj K.obj)) (e : h ≅ f ⋙ g) :
    Nonempty (R.lift (P.ι ⋙ h) hh ≅
      Q.lift (P.ι ⋙ f) hf ⋙ R.lift (Q.ι ⋙ g) hg) := by
  exact ⟨Functor.fullyFaithfulCancelRight R.ι (Functor.isoWhiskerLeft P.ι e)⟩

set_option allowUnsafeReducibility true in
attribute [local irreducible] Scheme.residueField integralDerivedPullback
  constructibleIntegralPullback sfRationalConstructibleCategory
  sfRationalConstructibleLocalization commonStageDerivedPullback zlPullComp
  rationalDerivedPullback sfModelPullComposition zlFrobeniusSquare
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompIsoOfIso

private theorem frontierPullComposition
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Nonempty (zlWeilPull D l hl Ω (f ≫ g) ≅
      zlWeilPull D l hl Ω g ⋙ zlWeilPull D l hl Ω f) := by
  let e := (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompIsoOfIso
    (e₁ := zlFrobeniusSquare D l hl Ω g)
    (e₂ := zlFrobeniusSquare D l hl Ω f)
    (e₃ := zlFrobeniusSquare D l hl Ω (f ≫ g))
    (sfModelPullComposition D l hl Ω f g)
    (zlWeilPullCompositorEquivariance D l hl Ω f g)).symm
  exact frontierLiftComposition _ _ _
    (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω g))
    (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f))
    (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω (f ≫ g)))
    (zlWeilPull_mem D l hl Ω g) (zlWeilPull_mem D l hl Ω f)
    (zlWeilPull_mem D l hl Ω (f ≫ g)) e


omit [IsSeparated X.hom] [IsSeparated Y.hom] in
private theorem frontierMixedRestriction (iota : Ω ≃+* ℂ)
    {Z : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : Z ⟶ Y) (g : Y ⟶ X) (F : sfCommonStageWeilSheaf D l hl X Ω) (w : ℝ)
    (h : SfIsMixedOfWeightsAtMost D l hl Ω Z iota
      ((zlWeilPull D l hl Ω (f ≫ g)).obj F) w) :
    SfIsMixedOfWeightsAtMost D l hl Ω Z iota
      ((zlWeilPull D l hl Ω f).obj ((zlWeilPull D l hl Ω g).obj F)) w := by
  obtain ⟨e⟩ := frontierPullComposition D l hl Ω f g
  exact frontierMixedIso D l hl Ω iota w (e.app F) h

/-- Gluing along the given finite reduced frontier, including extension of each
component filtration, the canonical short exact sequences and the reduction unit.
No reality hypothesis occurs. Every bound shared by the component filtrations is
retained by the resulting finite filtration.

Source: main-20261015, thm-zl-real-mixed-by-curves.proof.md, paragraphs 6--9
(blueprint: lem-zl-reduced-frontier-mixed-gluing).

Proof: choose the normalized closed images supplied by immersion filtration
transport. Their actual adjunctions give the desired units; uniqueness of left
and right adjoints identifies their localization sequences with the existing
Weil-heart localization theorem. Exact image functors preserve the filtration
quotients by the cokernel comparison isomorphism. Prescribed clopen reconstruction
assembles the component filtrations on each open difference, including an empty
component family. The normalized pullback compositor is Frobenius-equivariant,
so it lifts to an isomorphism of the actual Weil inverse images and identifies
all iterated restrictions. Induct backwards from the empty final closed term.
At each step, apply extension closure of bounded mixedness to the localization
short exact sequence. The reduction is surjective by its identification over X
with the nilradical subscheme, so the normalized reduction unit is an isomorphism.
Transport the resulting mixed filtration through its inverse. Finally take an
upper bound of the finite family of component bounds; the empty family is also
bounded above. Every preassigned common upper bound is preserved by the same
induction.
-/
theorem zlReducedFrontierMixedGluing (iota : Ω ≃+* ℂ)
    (C : ZlReducedFrontier D X) (F : sfCommonStageWeilSheaf D l hl X Ω)
    (mixed : ∀ (a : Fin C.length) (b : Fin (C.count a)),
      ∃ w : ℝ, SfIsMixedOfWeightsAtMost D l hl Ω (C.piece a b) iota
        ((zlWeilPull D l hl Ω
          (C.pieceInclusion a b ≫ C.openInclusion a ≫ C.ambient a.castSucc)).obj F) w) :
    ∃ (images : ∀ a : Fin C.length,
        ZlFrontierClosedImage D l hl Ω iota (C.inclusion a))
      (reduction : ZlFrontierClosedImage D l hl Ω iota (C.ambient 0)),
      (∃ w : ℝ, SfIsMixedOfWeightsAtMost D l hl Ω X iota F w) ∧
      (∀ w : ℝ, (∀ (a : Fin C.length) (b : Fin (C.count a)),
        SfIsMixedOfWeightsAtMost D l hl Ω (C.piece a b) iota
          ((zlWeilPull D l hl Ω
            (C.pieceInclusion a b ≫ C.openInclusion a ≫ C.ambient a.castSucc)).obj F) w) →
        SfIsMixedOfWeightsAtMost D l hl Ω X iota F w) ∧
      (∀ (a : Fin C.length) (b : Fin (C.count a)),
        ZlFrontierFiltrationPreservation D l hl Ω iota
          (zlOpenWeilShriek D l hl Ω (C.pieceInclusion a b))) ∧
      (∀ a : Fin C.length,
        ZlFrontierFiltrationPreservation D l hl Ω iota
          (zlOpenWeilShriek D l hl Ω (C.openInclusion a)) ∧
        ZlFrontierLocalization D l hl Ω iota (C.openInclusion a) (C.inclusion a)
          (images a) ((zlWeilPull D l hl Ω (C.ambient a.castSucc)).obj F)) ∧
      IsIso (reduction.adjunction.unit.app F) := by
  classical
  choose images image_surj using fun a : Fin C.length ↦
    frontierClosedImage D l hl Ω iota (C.inclusion a)
  obtain ⟨reduction, reduction_surj⟩ :=
    frontierClosedImage D l hl Ω iota (C.ambient 0)
  have open_preservation (a : Fin C.length) :=
    frontierOpenPreservation D l hl Ω iota (C.openInclusion a)
  have loc (a : Fin C.length) := frontierLocalization D l hl Ω iota
    (C.openInclusion a) (C.inclusion a) (C.complement a) (images a)
      ((zlWeilPull D l hl Ω (C.ambient a.castSucc)).obj F)
  have surj : Surjective (C.ambient 0).left := by
    have h := (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism
      X.left).2.2.1
    let := h
    rw [← C.reduction_over]
    infer_instance
  have unit_iso : IsIso (reduction.adjunction.unit.app F) := reduction_surj surj F
  have bounded (w : ℝ)
      (hm : ∀ (a : Fin C.length) (b : Fin (C.count a)),
        SfIsMixedOfWeightsAtMost D l hl Ω (C.piece a b) iota
          ((zlWeilPull D l hl Ω
            (C.pieceInclusion a b ≫ C.openInclusion a ≫ C.ambient a.castSucc)).obj F) w) :
      SfIsMixedOfWeightsAtMost D l hl Ω X iota F w := by
    have closed_mixed (a : Fin (C.length + 1)) :
        SfIsMixedOfWeightsAtMost D l hl Ω (C.closed a) iota
          ((zlWeilPull D l hl Ω (C.ambient a)).obj F) w := by
      induction a using Fin.reverseInduction with
      | last =>
          apply frontierMixedZero D l hl Ω iota w
          exact (zlWeilHeartLocalizationExact D l hl Ω iota
            (X₀ := C.closed (Fin.last C.length))
            (U₀ := C.closed (Fin.last C.length))
            (Z₀ := C.closed (Fin.last C.length))).2.2.2 C.finish _
      | @cast a ih =>
          have open_mixed : SfIsMixedOfWeightsAtMost D l hl Ω (C.difference a) iota
              ((zlWeilPull D l hl Ω (C.openInclusion a)).obj
                ((zlWeilPull D l hl Ω (C.ambient a.castSucc)).obj F)) w := by
            apply frontierClopenMixed D l hl Ω iota (C.count a) (C.piece a)
              (C.pieceInclusion a) (C.cover a) (C.disjoint a)
            intro b
            have hb := frontierMixedRestriction D l hl Ω iota (C.pieceInclusion a b)
              (C.openInclusion a ≫ C.ambient a.castSucc) F w (hm a b)
            obtain ⟨e⟩ := frontierPullComposition D l hl Ω
              (C.openInclusion a) (C.ambient a.castSucc)
            exact frontierMixedIso D l hl Ω iota w
              ((zlWeilPull D l hl Ω (C.pieceInclusion a b)).mapIso (e.app F)) hb
          have next_mixed : SfIsMixedOfWeightsAtMost D l hl Ω (C.closed a.succ) iota
              ((zlWeilPull D l hl Ω (C.inclusion a)).obj
                ((zlWeilPull D l hl Ω (C.ambient a.castSucc)).obj F)) w := by
            apply frontierMixedRestriction D l hl Ω iota (C.inclusion a)
              (C.ambient a.castSucc) F w
            simpa only [C.ambient_next a] using ih
          obtain ⟨h, hs⟩ := loc a
          exact frontierMixedExtension D l hl Ω iota w _ hs
            ((open_preservation a).mixed _ w open_mixed)
            ((images a).preservation.mixed _ w next_mixed)
    have hm := reduction.preservation.mixed _ w (closed_mixed 0)
    exact frontierMixedIso D l hl Ω iota w (asIso (reduction.adjunction.unit.app F)).symm hm
  choose weights hweights using mixed
  have finite_bounds : BddAbove (Set.range (fun i : Sigma (fun a : Fin C.length ↦
      Fin (C.count a)) ↦ weights i.1 i.2)) := Set.Finite.bddAbove (Set.finite_range _)
  obtain ⟨w, hw⟩ := finite_bounds
  refine ⟨images, reduction, ⟨w, bounded w ?_⟩, bounded, ?_, ?_, unit_iso⟩
  · intro a b
    exact frontierMixedMono D l hl Ω iota (hw ⟨⟨a, b⟩, rfl⟩) (hweights a b)
  · intro a b
    exact frontierOpenPreservation D l hl Ω iota (C.pieceInclusion a b)
  · intro a
    exact ⟨open_preservation a, loc a⟩

end WeilConjectures
