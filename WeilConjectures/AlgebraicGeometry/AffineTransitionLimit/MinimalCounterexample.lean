/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Minimal counterexamples over a quasi-compact quasi-separated base

A qcqs-local property (`AlgebraicGeometry.Scheme.IsQcqsLocalProperty`) of schemes over a
quasi-compact quasi-separated base `T` holds for the spectrum of a field over `T` as soon as it
holds for `T` itself (`AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section MinimalCounterexample

/-- A property `P` of quasi-compact quasi-separated schemes over a quasi-compact
quasi-separated base `T`, that is, a predicate on morphisms `T' ⟶ T` with `T'` qcqs, is
*qcqs-local* when it satisfies the three stability conditions of Stacks `0F06` and fails for
the empty scheme. -/
structure Scheme.IsQcqsLocalProperty (T : Scheme.{u})
    (P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop) : Prop where
  /-- `P` is invariant under thickenings: if `i : T₁ ⟶ T₂` is a closed immersion which is
  surjective on points and `f₂ : T₂ ⟶ T`, then `P (i ≫ f₂)` holds if and only if `P f₂`
  does. -/
  invariant_under_thickening : ∀ {T₁ T₂ : Scheme.{u}} [CompactSpace T₂]
    [QuasiSeparatedSpace T₂] (i : T₁ ⟶ T₂) [IsClosedImmersion i], Function.Surjective i.base →
    ∀ f₂ : T₂ ⟶ T, P (i ≫ f₂) ↔ P f₂
  /-- `P` is compatible with cofiltered limits with affine transition morphisms: if
  `D : I ⥤ Over T` is a cofiltered diagram of qcqs schemes over `T` whose transition
  morphisms are affine and `c` is a cone on `D` whose underlying cone of schemes is a limit
  cone, then `P` for every stage implies `P` for the limit. -/
  compatible_with_cofilteredLimit : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over T) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Limits.Cone D), Limits.IsLimit ((Over.forget T).mapCone c) →
    (∀ i, P (D.obj i).hom) → P c.pt.hom
  /-- `P` propagates to an open or to its closed complement: if `V` is a quasi-compact open
  of a qcqs scheme `T'` over `T` and `i : Z ⟶ T'` is a closed immersion onto the complement
  of `V`, then `P` for `T' ⟶ T` implies `P` for `V ⟶ T` or for `Z ⟶ T`. -/
  of_opens_or_closedComplement : ∀ {T' Z : Scheme.{u}} [CompactSpace T']
    [QuasiSeparatedSpace T'] (f : T' ⟶ T) (V : T'.Opens), IsCompact (V : Set T') →
    ∀ (i : Z ⟶ T') [IsClosedImmersion i], Set.range i.base = (V : Set T')ᶜ →
    P f → P (V.ι ≫ f) ∨ P (i ≫ f)
  /-- `P` fails for the empty scheme. -/
  not_of_isEmpty : ∀ {T' : Scheme.{u}} (f : T' ⟶ T), IsEmpty T' → ¬ P f

namespace Scheme.IsQcqsLocalProperty

variable {T : Scheme.{u}} {P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop}

/-- A qcqs-local property is invariant under isomorphisms of qcqs schemes over the base. -/
lemma comp_iff_of_isIso (hP : T.IsQcqsLocalProperty P) {T₁ T₂ : Scheme.{u}} [CompactSpace T₂]
    [QuasiSeparatedSpace T₂] (e : T₁ ⟶ T₂) [IsIso e] (f : T₂ ⟶ T) : P (e ≫ f) ↔ P f :=
  hP.invariant_under_thickening e (fun x ↦ ⟨(inv e).base x, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩) f

set_option backward.isDefEq.respectTransparency false in
/-- A qcqs-local property holding for the closed subschemes cut out by the members of a nonempty
chain of ideal sheaves holds for the closed subscheme cut out by their supremum, which is the
cofiltered limit of these closed subschemes. This gives the lower bounds of chains in the Zorn
argument of `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`. -/
lemma subschemeι_sSup [CompactSpace T] [QuasiSeparatedSpace T] (hP : T.IsQcqsLocalProperty P)
    {c : Set T.IdealSheafData} (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (h : ∀ I ∈ c, P I.subschemeι) : P (sSup c).subschemeι := by
  obtain ⟨I₀, hI₀⟩ := hne
  have : Nonempty c := ⟨⟨I₀, hI₀⟩⟩
  have : IsDirectedOrder c := ⟨fun a b ↦ by
    rcases hc.total a.2 b.2 with hab | hab
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hab⟩⟩
  let F : cᵒᵖ ⥤ Scheme.{u} :=
    { obj I := I.unop.1.subscheme
      map f := IdealSheafData.inclusion (leOfHom f.unop)
      map_id _ := IdealSheafData.inclusion_id _
      map_comp _ _ := (IdealSheafData.inclusion_comp _ _).symm }
  let D : cᵒᵖ ⥤ Over T := F.toOver T (fun I ↦ I.unop.1.subschemeι)
    (fun _ ↦ IdealSheafData.inclusion_subschemeι _)
  let c' : Cone D :=
    { pt := Over.mk (sSup c).subschemeι
      π :=
      { app I := Over.homMk (IdealSheafData.inclusion (le_sSup I.unop.2))
          (IdealSheafData.inclusion_subschemeι _)
        naturality I J f := by
          ext1
          change IdealSheafData.inclusion _ =
            IdealSheafData.inclusion _ ≫ IdealSheafData.inclusion _
          exact (IdealSheafData.inclusion_comp _ _).symm } }
  have hπ (s : Cone (D ⋙ Over.forget T)) {I J : c} (hIJ : I ≤ J) :
      s.π.app (.op I) ≫ I.1.subschemeι = s.π.app (.op J) ≫ J.1.subschemeι := by
    rw [← s.w (homOfLE hIJ).op]
    exact (Category.assoc _ _ _).trans
      (congrArg (s.π.app (.op J) ≫ ·) (IdealSheafData.inclusion_subschemeι _))
  have hπ₀ (s : Cone (D ⋙ Over.forget T)) (I : c) :
      s.π.app (.op I) ≫ I.1.subschemeι = s.π.app (.op ⟨I₀, hI₀⟩) ≫ I₀.subschemeι := by
    rcases hc.total I.2 hI₀ with hle | hle
    · exact hπ s (I := I) (J := ⟨I₀, hI₀⟩) hle
    · exact (hπ s (I := ⟨I₀, hI₀⟩) (J := I) hle).symm
  have hker (s : Cone (D ⋙ Over.forget T)) :
      (sSup c).subschemeι.ker ≤ (s.π.app (.op ⟨I₀, hI₀⟩) ≫ I₀.subschemeι).ker := by
    rw [IdealSheafData.ker_subschemeι]
    refine sSup_le fun I hI ↦ ?_
    rw [← hπ₀ s ⟨I, hI⟩]
    have := Scheme.Hom.le_ker_comp (s.π.app (.op ⟨I, hI⟩)) I.subschemeι
    rwa [IdealSheafData.ker_subschemeι] at this
  have hlim : IsLimit ((Over.forget T).mapCone c') :=
    { lift s := (IsClosedImmersion.lift (sSup c).subschemeι _ (hker s) :
        s.pt ⟶ (sSup c).subscheme)
      fac s I := by
        change (IsClosedImmersion.lift (sSup c).subschemeι _ (hker s) :
          s.pt ⟶ (sSup c).subscheme) ≫ IdealSheafData.inclusion (le_sSup I.unop.2) = s.π.app I
        rw [← cancel_mono I.unop.1.subschemeι, Category.assoc,
          IdealSheafData.inclusion_subschemeι, IsClosedImmersion.lift_fac]
        exact (hπ₀ s I.unop).symm
      uniq s m hm := by
        rw [← cancel_mono (sSup c).subschemeι, IsClosedImmersion.lift_fac, ← hm (.op ⟨I₀, hI₀⟩)]
        change _ = (m ≫ IdealSheafData.inclusion _) ≫ _
        rw [Category.assoc, IdealSheafData.inclusion_subschemeι] }
  have (I : cᵒᵖ) : CompactSpace (D.obj I).left :=
    inferInstanceAs (CompactSpace I.unop.1.subscheme)
  have (I : cᵒᵖ) : QuasiSeparatedSpace (D.obj I).left :=
    inferInstanceAs (QuasiSeparatedSpace I.unop.1.subscheme)
  have {I J : cᵒᵖ} (f : I ⟶ J) : IsAffineHom (D.map f).left := by
    have hf : (D.map f).left = IdealSheafData.inclusion (leOfHom f.unop) := rfl
    have h : IdealSheafData.inclusion (leOfHom f.unop) ≫ J.unop.1.subschemeι =
        I.unop.1.subschemeι := IdealSheafData.inclusion_subschemeι _
    have : IsClosedImmersion
        (IdealSheafData.inclusion (leOfHom f.unop) ≫ J.unop.1.subschemeι) := by
      rw [h]; infer_instance
    have : IsClosedImmersion (IdealSheafData.inclusion (leOfHom f.unop)) :=
      IsClosedImmersion.of_comp_isClosedImmersion _ J.unop.1.subschemeι
    rw [hf]
    infer_instance
  exact hP.compatible_with_cofilteredLimit D c' hlim fun I ↦ h I.unop.1 I.unop.2

end Scheme.IsQcqsLocalProperty

open CommRingCat in
set_option backward.isDefEq.respectTransparency false in
/-- **Minimal counterexamples occur over a point.** A qcqs-local property `P` of
quasi-compact quasi-separated schemes over a quasi-compact quasi-separated base `T` which
holds for `T` itself holds for some morphism `Spec K ⟶ T` with `K` a field.

By Zorn's lemma there is a minimal closed subscheme `T'` of `T` with `P`. Every nonempty
quasi-compact open of `T'` has `P`, as otherwise its closed complement would be a smaller closed
subscheme with `P`. Take a nonempty affine open `Spec A` of `T'` and a minimal prime `p` of `A`;
then `Spec A_p` is the cofiltered limit of the nonempty basic opens `Spec A[1/f]`, `f ∉ p`, so
it has `P`, and it is a thickening of the spectrum of its residue field, as `A_p` has a single
prime ideal. (Blueprint: `sk-lem-minimal`, `sbc-lem-bc-minimal-counterexample`.) -/
@[stacks 0F06]
theorem exists_spec_field_of_isQcqsLocalProperty (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T]
    (P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop) (hP' : T.IsQcqsLocalProperty P)
    (hP : P (𝟙 T)) :
    ∃ (K : Type u) (_ : Field K) (g : Spec (CommRingCat.of K) ⟶ T), P g := by
  classical
  -- Zorn's lemma gives a maximal ideal sheaf `J` (a minimal closed subscheme) with `P`
  obtain ⟨J, -, hJ⟩ := zorn_le_nonempty₀ {I : T.IdealSheafData | P I.subschemeι}
    (fun c hcs hc y hy ↦ ⟨sSup c, hP'.subschemeι_sSup hc ⟨y, hy⟩ fun I hI ↦ hcs hI,
      fun _ hz ↦ le_sSup hz⟩) ⊥ (by
      have hsurj : Function.Surjective (⊥ : T.IdealSheafData).subschemeι.base := by
        rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.support_bot]
        rfl
      have := (hP'.invariant_under_thickening _ hsurj (𝟙 T)).mpr hP
      rwa [Category.comp_id] at this)
  have hJP : P J.subschemeι := hJ.prop
  -- a closed subscheme of `V(J)` with `P` is all of `V(J)`
  have hsurj {Z : Scheme.{u}} (g : Z ⟶ J.subscheme) [IsClosedImmersion g]
      (hg : P (g ≫ J.subschemeι)) : Function.Surjective g.base := by
    have hker : P (g ≫ J.subschemeι).ker.subschemeι := by
      have := (hP'.comp_iff_of_isIso (g ≫ J.subschemeι).toImage (g ≫ J.subschemeι).imageι).mp
        (by rwa [Scheme.Hom.toImage_imageι])
      exact this
    have hJk : J ≤ (g ≫ J.subschemeι).ker := by
      have := Scheme.Hom.le_ker_comp g J.subschemeι
      rwa [Scheme.IdealSheafData.ker_subschemeι] at this
    have heq : (g ≫ J.subschemeι).ker = J := le_antisymm (hJ.2 hker hJk) hJk
    have hrange : Set.range (g ≫ J.subschemeι).base = Set.range J.subschemeι.base := by
      rw [← (g ≫ J.subschemeι).isClosedEmbedding.isClosed_range.closure_eq,
        ← Scheme.Hom.support_ker, heq, Scheme.IdealSheafData.range_subschemeι]
    intro z
    obtain ⟨w, hw⟩ : J.subschemeι.base z ∈ Set.range (g ≫ J.subschemeι).base :=
      hrange ▸ ⟨z, rfl⟩
    exact ⟨w, J.subschemeι.isClosedEmbedding.injective (by simpa using hw)⟩
  -- a nonempty quasi-compact open subscheme of `V(J)` has `P`
  have hopen {W : Scheme.{u}} (o : W ⟶ J.subscheme) [IsOpenImmersion o] [CompactSpace W]
      [Nonempty W] : P (o ≫ J.subschemeι) := by
    have hV : IsCompact (o.opensRange : Set J.subscheme) := by
      simpa using isCompact_range o.continuous
    let Z : TopologicalSpace.Closeds J.subscheme :=
      ⟨(o.opensRange : Set J.subscheme)ᶜ, o.opensRange.isOpen.isClosed_compl⟩
    have hZ : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base =
        (o.opensRange : Set J.subscheme)ᶜ := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    rcases hP'.of_opens_or_closedComplement J.subschemeι o.opensRange hV _ hZ hJP with h | h
    · have : CompactSpace o.opensRange := isCompact_iff_compactSpace.mp hV
      have : QuasiSeparatedSpace o.opensRange :=
        quasiSeparatedSpace_of_quasiSeparated o.opensRange.ι
      rw [← o.isoOpensRange_hom_ι, Category.assoc, hP'.comp_iff_of_isIso]
      exact h
    · obtain ⟨w⟩ := ‹Nonempty W›
      obtain ⟨z, hz⟩ := hsurj _ h (o.base w)
      have : o.base w ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base :=
        ⟨z, hz⟩
      rw [hZ] at this
      exact (this ⟨w, rfl⟩).elim
  -- `V(J)` is nonempty, choose a nonempty affine open and a minimal prime of its sections
  obtain ⟨x⟩ : Nonempty J.subscheme := by
    by_contra hne
    exact hP'.not_of_isEmpty _ (not_nonempty_iff.mp hne) hJP
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    J.subscheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV : IsAffineOpen V := hV
  obtain ⟨y, -⟩ : x ∈ Set.range hV.fromSpec.base := by rwa [hV.range_fromSpec]
  have : Nontrivial Γ(J.subscheme, V) := ⟨⟨0, 1, fun h ↦ y.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ zero_mem _))⟩⟩
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal Γ(J.subscheme, V))) bot_ne_top
  have : p.IsPrime := hp.1.1
  -- `Spec A_p` is the limit of the nonempty basic opens `Spec A[1/f]`, `f ∉ p`, of `V`
  let q : Spec Γ(J.subscheme, V) ⟶ T := hV.fromSpec ≫ J.subschemeι
  have hstage (s : Finset p.primeCompl) :
      P (Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (AwayProd p s))) ≫ q) := by
    have : Nontrivial (AwayProd p s) := (awayProdToAtPrime p s).toRingHom.domain_nontrivial
    have : Nonempty (Spec (.of (AwayProd p s))) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    have : IsOpenImmersion (Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (AwayProd p s)))) :=
      IsOpenImmersion.of_isLocalization (∏ x ∈ s, (x : Γ(J.subscheme, V)))
    have := hopen (Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (AwayProd p s))) ≫ hV.fromSpec)
    rwa [Category.assoc] at this
  let F : (Finset p.primeCompl)ᵒᵖ ⥤ Scheme.{u} := (awayProdDiagram p).op ⋙ Scheme.Spec
  let D : (Finset p.primeCompl)ᵒᵖ ⥤ Over T := F.toOver T
    (fun s ↦ Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (AwayProd p s.unop))) ≫ q)
    (fun {s t} f ↦ by
      change Spec.map ((awayProdDiagram p).map f.unop) ≫ _ = _
      rw [← Spec.map_comp_assoc, ofHom_algebraMap_comp_awayProdDiagram_map])
  let c' : Cone D :=
    { pt := Over.mk (Spec.map (ofHom (algebraMap Γ(J.subscheme, V) (Localization.AtPrime p))) ≫ q)
      π :=
      { app s := Over.homMk (Spec.map ((awayProdCocone p).ι.app s.unop)) (by
          change _ ≫ Spec.map _ ≫ q = _
          rw [← Spec.map_comp_assoc, ofHom_algebraMap_comp_awayProdCocone_ι_app]
          rfl)
        naturality s t f := by
          ext1
          change Spec.map ((awayProdCocone p).ι.app t.unop) =
            Spec.map ((awayProdCocone p).ι.app s.unop) ≫ Spec.map ((awayProdDiagram p).map f.unop)
          rw [← Spec.map_comp, (awayProdCocone p).w] } }
  have hlim : IsLimit ((Over.forget T).mapCone c') :=
    isLimitOfPreserves Scheme.Spec (isColimitAwayProdCocone p).op
  have (s : (Finset p.primeCompl)ᵒᵖ) : IsAffine (D.obj s).left :=
    inferInstanceAs (IsAffine (Spec _))
  have {s t : (Finset p.primeCompl)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f).left :=
    isAffineHom_of_isAffine _
  have hlimP : P c'.pt.hom :=
    hP'.compatible_with_cofilteredLimit D c' hlim fun s ↦ hstage s.unop
  -- `Spec A_p` has a single point, so the residue field is a thickening of it
  have hunique (z : PrimeSpectrum (Localization.AtPrime p)) :
      z.asIdeal = IsLocalRing.maximalIdeal _ := by
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      (A := Localization.AtPrime p) p ⊥ hp
    rw [Ideal.map_bot, IsLocalization.AtPrime.map_eq_maximalIdeal p] at hrad
    refine le_antisymm (IsLocalRing.le_maximalIdeal z.isPrime.ne_top) ?_
    rw [← hrad]
    exact z.isPrime.radical_le_iff.mpr bot_le
  have : Subsingleton (Spec (.of (Localization.AtPrime p))) :=
    ⟨fun a b ↦ PrimeSpectrum.ext ((hunique a).trans (hunique b).symm)⟩
  let K := IsLocalRing.ResidueField (Localization.AtPrime p)
  let i : Spec (.of K) ⟶ Spec (.of (Localization.AtPrime p)) :=
    Spec.map (ofHom (IsLocalRing.residue _))
  have : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have : Nonempty (Spec (.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  exact ⟨K, inferInstance, i ≫ c'.pt.hom, (hP'.invariant_under_thickening i
    (fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩) _).mpr hlimP⟩

end MinimalCounterexample

end AlgebraicGeometry
