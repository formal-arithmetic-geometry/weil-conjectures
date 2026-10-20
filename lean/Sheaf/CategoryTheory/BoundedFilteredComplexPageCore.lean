/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.BoundedFilteredPageConstruction
import Sheaf.CategoryTheory.BoundedFilteredCoupleAbutment

/-!
# Canonical bounded filtered pages and their finite abutment

Source: Stacks Project, Homology, Section 12.24, Lemmas 12.24.2--12.24.4 and 12.24.11;
blueprint thm-sp-spectral-object-yields, steps 1--5
(blueprint: lem-sp-bounded-filtered-page-core).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem pageCore_subobjects_stabilize
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (hF : F.IsFinite)
    (p n : ℤ) :
    ∃ (R : ℤ) (_hR : 1 ≤ R), ∀ r : ℤ, R ≤ r →
      F.complexCycles p n r = F.complexCycles p n R ∧
      F.complexBoundaries p n r = F.complexBoundaries p n R := by
  obtain ⟨a, b, ha, hb⟩ := hF
  have hbot (i : ℤ) (hi : b ≤ i) : F.step i = ⊥ := by
    apply le_antisymm _ bot_le
    simpa only [hb] using F.antitone_step hi
  have htop (i : ℤ) (hi : i ≤ a) : F.step i = ⊤ := by
    apply le_antisymm le_top
    simpa only [ha] using F.antitone_step hi
  let R := max 1 (max (b - p) (p + 1 - a))
  have hR : 1 ≤ R := le_max_left _ _
  have hRb : b - p ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRa : p + 1 - a ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R, hR, ?_⟩
  intro r hr
  have hhi : F.step (p + r) = F.step (p + R) := by
    rw [hbot (p + r) (by omega), hbot (p + R) (by omega)]
  have hlo : F.step (p - r + 1) = F.step (p - R + 1) := by
    rw [htop (p - r + 1) (by omega), htop (p - R + 1) (by omega)]
  have hhi' : F.complexStep (p + r) (n + 1) = F.complexStep (p + R) (n + 1) :=
    congrArg (fun T : Subobject K ↦ imageSubobject (T.arrow.f (n + 1))) hhi
  have hlo' : F.complexStep (p - r + 1) (n - 1) =
      F.complexStep (p - R + 1) (n - 1) :=
    congrArg (fun T : Subobject K ↦ imageSubobject (T.arrow.f (n - 1))) hlo
  constructor
  · simp only [DecreasingFiltration.complexCycles, hhi']
  · simp only [DecreasingFiltration.complexBoundaries, hlo']

private theorem pageCore_quotient_iso
    {C : Type u} [Category.{v} C] [Abelian C] {A : C}
    {B Z B' Z' : Subobject A} (h : B ≤ Z) (h' : B' ≤ Z')
    (hB : B = B') (hZ : Z = Z') :
    Nonempty (cokernel (Subobject.ofLE B Z h) ≅ cokernel (Subobject.ofLE B' Z' h')) := by
  subst B'
  subst Z'
  exact ⟨Iso.refl _⟩

private theorem pageCore_graded_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (p n : ℤ)
    (h : F.step (p + 1) = F.step p) : IsZero ((F.gradedPiece p).X n) := by
  have hz : IsZero (F.gradedPiece p) := by
    dsimp [DecreasingFiltration.gradedPiece]
    let e := Subobject.isoOfEq (F.step (p + 1)) (F.step p) h
    change IsZero (cokernel e.hom)
    exact isZero_cokernel_of_epi _
  exact (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_isZero hz

private theorem pageCore_differentials_stabilize
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (E : CohomologicalSpectralSequence C 1)
    (hpages : ∀ (p q r : ℤ) (hr : 1 ≤ r),
      ∃ hBZ : U.obj.filtration.complexBoundaries p (p + q) r ≤
          U.obj.filtration.complexCycles p (p + q) r,
        Nonempty ((E.page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ)))
    (p q : ℤ) :
    ∃ (R : ℤ) (_hR : 1 ≤ R), ∀ (r : ℤ) (_hr : R ≤ r),
      (E.page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
      (E.page r (by omega)).d (p - r, q + r - 1) (p, q) = 0 := by
  obtain ⟨a, b, ha, hb⟩ := U.property
  have hbot (i : ℤ) (hi : b ≤ i) : U.obj.filtration.step i = ⊥ := by
    apply le_antisymm _ bot_le
    simpa only [hb] using U.obj.filtration.antitone_step hi
  have htop (i : ℤ) (hi : i ≤ a) : U.obj.filtration.step i = ⊤ := by
    apply le_antisymm le_top
    simpa only [ha] using U.obj.filtration.antitone_step hi
  have hzero (k l r : ℤ) (hr : 1 ≤ r) (hk : k < a ∨ b ≤ k) :
      IsZero ((E.page r hr).X (k, l)) := by
    have heq : U.obj.filtration.step (k + 1) = U.obj.filtration.step k := by
      rcases hk with hk | hk
      · rw [htop (k + 1) (by omega), htop k (by omega)]
      · rw [hbot (k + 1) (by omega), hbot k hk]
    have hz := pageCore_graded_zero U.obj.filtration k (k + l) heq
    obtain ⟨hBZ, ⟨e⟩⟩ := hpages k l r hr
    have hZ : IsZero (U.obj.filtration.complexCycles k (k + l) r : C) :=
      IsZero.of_mono (U.obj.filtration.complexCycles k (k + l) r).arrow hz
    have hquot := IsZero.of_epi (cokernel.π (Subobject.ofLE _ _ hBZ)) hZ
    exact hquot.of_iso e
  let R := max 1 (max (b - p) (p - a + 1))
  have hR : 1 ≤ R := le_max_left _ _
  have hRb : b - p ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRa : p - a + 1 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R, hR, ?_⟩
  intro r hr
  exact ⟨(hzero (p + r) (q - r + 1) r (by omega) (Or.inr (by omega))).eq_zero_of_tgt _,
    (hzero (p - r) (q + r - 1) r (by omega) (Or.inl (by omega))).eq_zero_of_src _⟩

/-- Canonical page construction and finite convergence, without first-quadrant support.
Source: Stacks Project, Homology, Section 12.24, Lemmas 12.24.2--12.24.4 and 12.24.11;
blueprint thm-sp-spectral-object-yields, steps 1--5
(blueprint: lem-sp-bounded-filtered-page-core).

Proof: Form the long exact sequences of the filtration-step short exact sequences.
Reindex their exact couple by (P,Q)=(2p+q,-p). Deriving this couple gives page s+1,
and the three successive filtration steps give the displayed first differential.
Restrict filtered morphisms to filtration steps, then descend them through the
cokernels; uniqueness of cokernel descent gives the quotient squares, identities,
and composition. The induced couple morphisms give the spectral-sequence functor.
A representative in F^p with differential in F^(p+r) is a cycle modulo F^(p+r).
Its image class vanishes exactly when it is dy+f with y in F^(p-r+1) and f in
F^(p+1). Thus its kernel consists of the displayed boundaries. Descending this
representative map gives eI and eZ with the stated representative equation.
The supplied transition agrees with cokernel descent since hφ fixes its composite
with the epimorphic projection. At r=1 it is the identity, giving the first-page
image equation. All these operations commute with filtered maps.
Set G^p H^n=image(H^n(F^p K)→H^n(K)). The finite bottom and top filtration steps
give a finite separated filtration G. The alpha system is constant at H^n(K)
in its bottom tail, so this object with its inclusion cocone gives A and aH.
The couple maps are the filtration inclusions and quotient projections, giving
all three displayed compatibility equations. The stationary cycles are ker d
intersect F^p, and the stationary boundaries are im d intersect F^p, modulo
F^(p+1). Their quotient identifies with gr^p G, giving L and convergence.
For each bidegree choose a common bound for both filtration tails and the adjacent
bidegrees. Derived-couple representatives then have zero incoming and outgoing
differentials, and page homology identifies all subsequent pages with that bound.
This statement makes no first-quadrant assumption or uniform quadrant bound. -/
theorem boundedFilteredComplex_pageCore
    (C : Type u) [Category.{v} C] [Abelian C]
    (φ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
        U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
    (hφ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p r : ℤ) (hr : 1 ≤ r),
        U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ φ U p r hr =
          Subobject.ofLE (U.obj.filtration.step p)
            (U.obj.filtration.step (p - r + 1))
            (U.obj.filtration.antitone_step (by omega)) ≫
              U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega)) :
    ∃ (S : ObjectProperty.FullSubcategory
          (fun U : FilteredObject (CochainComplex C ℤ) ↦ U.filtration.IsFinite) ⥤
        CohomologicalSpectralSequence C 1)
      (e₁ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        ((S.obj U).page 1).X (p, q) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
      (eI : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅
          image (HomologicalComplex.homologyMap (φ U p r hr) (p + q))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        (eI U p q 1 (by omega)).hom ≫
            image.ι (HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) =
          (e₁ U p q).hom ≫
            HomologicalComplex.homologyMap (φ U p 1 (by omega)) (p + q)) ∧
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
        ∃ (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
            (V.obj.filtration.step a : CochainComplex C ℤ))
          (a : U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
            V.obj.filtration.complexQuotient p (p + r) (by omega))
          (b : U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
            V.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
          (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p),
          (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom) ∧
          U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + r) (by omega) ∧
          U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
            s (p - r + 1) ≫
              V.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          ((S.map t).hom 1).f (p, q) ≫ (e₁ V p q).hom =
            (e₁ U p q).hom ≫ HomologicalComplex.homologyMap g (p + q) ∧
          ((S.map t).hom r hr).f (p, q) ≫ (eI V p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ V p r hr) (p + q)) =
            (eI U p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ≫
                HomologicalComplex.homologyMap b (p + q)) ∧
      ∀ U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite),
        (∀ p q : ℤ,
          ∃ (i : U.obj.filtration.gradedPiece (p + 1) ⟶
              U.obj.filtration.complexQuotient p (p + 2) (by omega))
            (j : U.obj.filtration.complexQuotient p (p + 2) (by omega) ⟶
              U.obj.filtration.gradedPiece p)
            (hij : i ≫ j = 0) (hS : (ShortComplex.mk i j hij).ShortExact),
            U.obj.filtration.complexQuotientπ (p + 1) (p + 1 + 1) (by omega) ≫ i =
              Subobject.ofLE (U.obj.filtration.step (p + 1))
                (U.obj.filtration.step p) (U.obj.filtration.antitone_step (by omega)) ≫
                  U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ∧
            U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ≫ j =
              U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
            ((S.obj U).page 1).d (p, q) (p + 1, q) ≫ (e₁ U (p + 1) q).hom =
              (e₁ U p q).hom ≫
                hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega)) ∧
        (∀ (p q r : ℤ) (hr : 1 ≤ r),
          ∃ (hBZ : U.obj.filtration.complexBoundaries p (p + q) r ≤
              U.obj.filtration.complexCycles p (p + q) r)
            (eZ : ((S.obj U).page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ))
            (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (U.obj.filtration.complexCycles p (p + q) r : C))
            (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (U.obj.filtration.complexQuotient p (p + r) (by omega)).cycles (p + q)),
            z ≫ (U.obj.filtration.complexCycles p (p + q) r).arrow =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
            g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q) =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ∧
            z ≫ cokernel.π (Subobject.ofLE _ _ hBZ) ≫ eZ.inv ≫
                (eI U p q r hr).hom ≫
                image.ι (HomologicalComplex.homologyMap (φ U p r hr) (p + q)) =
              g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).homologyπ
                (p + q) ≫ HomologicalComplex.homologyMap (φ U p r hr) (p + q)) ∧
        (∃ (G : ∀ n : ℤ, DecreasingFiltration (U.obj.obj.homology n))
          (X : BigradedExactCouple C 0) (L : X.LimitSubobjects)
          (A : ∀ n : ℤ, X.AlphaColimit n)
          (aH : ∀ n : ℤ, (A n).obj ≅ U.obj.obj.homology n)
          (eD : ∀ P Q : ℤ, X.D P Q ≅
            (U.obj.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q))
          (eC : ∀ (s : ℕ) (p q : ℤ),
            (X.pageCouple s).E (2 * p + q) (-p) ≅
              ((S.obj U).page (s + 1) (by omega)).X (p, q)),
          (∀ n p : ℤ, (G n).step p =
            imageSubobject (HomologicalComplex.homologyMap
              (U.obj.filtration.step p).arrow n)) ∧
          (∀ n : ℤ, (G n).IsFinite ∧ (G n).IsSeparated) ∧
          (∀ n P : ℤ,
            (A n).ι P ≫ (aH n).hom =
              (eD P (n - P)).hom ≫ eqToHom (by
                rw [show -(n - P) = P - n by omega, show P + (n - P) = n by omega]) ≫
                HomologicalComplex.homologyMap
                  (U.obj.filtration.step (P - n)).arrow n) ∧
          (∀ P Q : ℤ,
            X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (Subobject.ofLE (U.obj.filtration.step (-Q))
                  (U.obj.filtration.step (-(Q + 1)))
                  (U.obj.filtration.antitone_step (by omega))) (P + Q) ≫
                eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
          (∀ P Q : ℤ,
            X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
                (eC 0 (-Q) (P + 2 * Q)).hom ≫ (e₁ U (-Q) (P + 2 * Q)).hom ≫
                eqToHom (by
                  rw [show -Q + (P + 2 * Q) = P + Q by omega]
                  rfl) =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (U.obj.filtration.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) ∧
          (∀ (s : ℕ) (p q : ℤ),
            (eC s p q).hom ≫
                ((S.obj U).page (s + 1) (by omega)).d (p, q)
                  (p + (s + 1), q - (s + 1) + 1) =
              (X.pageCouple s).d (2 * p + q) (-p) ≫
                eqToHom (by congr 1 <;> omega) ≫
                  (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom) ∧
          X.ConvergesTo L A ∧
          (∀ p q : ℤ, Nonempty
            (X.pageInfinity L (2 * p + q) (-p) ≅ (G (p + q)).gradedPiece p))) ∧
        (∀ p q : ℤ, ∃ (R : ℤ) (hR : 1 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
          U.obj.filtration.complexCycles p (p + q) r =
            U.obj.filtration.complexCycles p (p + q) R ∧
          U.obj.filtration.complexBoundaries p (p + q) r =
            U.obj.filtration.complexBoundaries p (p + q) R ∧
          ((S.obj U).page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
          ((S.obj U).page r (by omega)).d (p - r, q + r - 1) (p, q) = 0 ∧
          Nonempty (((S.obj U).page r (by omega)).X (p, q) ≅
            ((S.obj U).page R hR).X (p, q))) := by
  obtain ⟨S, e₁, eI, hfirst, hnat, hobj⟩ :=
    boundedFilteredComplex_pageConstruction C φ hφ
  refine ⟨S, e₁, eI, hfirst, hnat, ?_⟩
  intro U
  obtain ⟨hd₁, hrep, X, eD, eC, hα, hγ, hd⟩ := hobj U
  obtain ⟨G, L, A, aH, hG, hfinite, hcocone, hconv, hinf⟩ :=
    boundedFilteredComplex_coupleAbutment C S e₁ U X eD eC hα hγ
  refine ⟨hd₁, hrep, ⟨G, X, L, A, aH, eD, eC, hG, hfinite, hcocone,
    hα, hγ, hd, hconv, hinf⟩, ?_⟩
  have hpages (p q r : ℤ) (hr : 1 ≤ r) :
      ∃ hBZ : U.obj.filtration.complexBoundaries p (p + q) r ≤
          U.obj.filtration.complexCycles p (p + q) r,
        Nonempty (((S.obj U).page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ)) := by
    obtain ⟨hBZ, eZ, _⟩ := hrep p q r hr
    exact ⟨hBZ, ⟨eZ⟩⟩
  intro p q
  obtain ⟨R₀, hR₀, hsub⟩ :=
    pageCore_subobjects_stabilize U.obj.filtration U.property p (p + q)
  obtain ⟨R₁, hR₁, hdiff⟩ := pageCore_differentials_stabilize U (S.obj U) hpages p q
  let R := max R₀ R₁
  have hR : 1 ≤ R := hR₀.trans (le_max_left _ _)
  have hR₀R : R₀ ≤ R := le_max_left _ _
  have hR₁R : R₁ ≤ R := le_max_right _ _
  refine ⟨R, hR, ?_⟩
  intro r hr
  obtain ⟨hZr, hBr⟩ := hsub r (hR₀R.trans hr)
  obtain ⟨hZR, hBR⟩ := hsub R hR₀R
  have hZ := hZr.trans hZR.symm
  have hB := hBr.trans hBR.symm
  obtain ⟨hout, hin⟩ := hdiff r (hR₁R.trans hr)
  obtain ⟨hBZr, ⟨er⟩⟩ := hpages p q r (hR.trans hr)
  obtain ⟨hBZR, ⟨eR⟩⟩ := hpages p q R hR
  obtain ⟨equot⟩ := pageCore_quotient_iso hBZr hBZR hB hZ
  exact ⟨hZ, hB, hout, hin, ⟨er ≪≫ equot ≪≫ eR.symm⟩⟩


end CategoryTheory
