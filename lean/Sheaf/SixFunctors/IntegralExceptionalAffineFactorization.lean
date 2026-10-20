/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.SixFunctors.IntegralBrownAdjoint
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.SixFunctors.CompactificationOverBase
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.MateOpenRestriction

/-!
# Geometric and adjoint factorization on one affine chart

Source: blueprint main-20261015, sk-thm-int-restriction, General f paragraph,
and sk-thm-int-restriction-glue.proof.md, paragraph (2).
(blueprint: lem-sfb-integral-exceptional-affine-factorization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable {X Y : Scheme.{u}}

private theorem affine_presentation {T Z : Scheme.{u}} [IsAffine T] [IsAffine Z]
    (q : Z ⟶ T) [LocallyOfFiniteType q] :
    ∃ (d : ℕ) (i : Z ⟶ AffineSpace (ULift.{u} (Fin d)) T),
      IsClosedImmersion i ∧ i ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = q := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_closure_range_appTop_union_eq_top q
  let v : ULift.{u} (Fin s.card) → Γ(Z, ⊤) := fun a ↦ (s.equivFin.symm a.down).val
  have hv : Set.range v = (s : Set Γ(Z, ⊤)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (s.equivFin.symm a.down).property
    · intro hx
      exact ⟨⟨s.equivFin ⟨x, hx⟩⟩, by simp [v]⟩
  exact ⟨s.card, AffineSpace.homOfVector q v,
    AffineSpace.isClosedImmersion_homOfVector q v (by rw [hv]; exact hs),
    AffineSpace.homOfVector_over q v⟩

private noncomputable def liftAdjunction
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty C) (Q : ObjectProperty D)
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hF : ∀ A : P.FullSubcategory, Q (F.obj A.obj))
    (hG : ∀ B : Q.FullSubcategory, P (G.obj B.obj)) :
    Q.lift (P.ι ⋙ F) hF ⊣ P.lift (Q.ι ⋙ G) hG :=
  adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι (Iso.refl _) (Iso.refl _)

private noncomputable def liftIso
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    {F G : C ⥤ P.FullSubcategory} (e : F ⋙ P.ι ≅ G ⋙ P.ι) : F ≅ G :=
  NatIso.ofComponents (fun A ↦ P.isoMk (e.app A)) (by
    intro A B m
    apply ObjectProperty.hom_ext
    exact e.hom.naturality m)

private noncomputable def space (k : Type u) [Field k] (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] : Spaces k :=
  ⟨Over.mk (T ↘ Spec (.of k)),
    ⟨inferInstanceAs (IsSeparated (T ↘ Spec (.of k))),
      inferInstanceAs (LocallyOfFiniteType (T ↘ Spec (.of k))),
      inferInstanceAs (QuasiCompact (T ↘ Spec (.of k)))⟩⟩

set_option maxHeartbeats 800000 in
-- The affine presentation and five full-subcategory lifts elaborate in one proof.
/-- Affine presentation and the corresponding comparison of right adjoints.

Source: blueprint main-20261015, sk-thm-int-restriction.proof.md, General f,
and sk-thm-int-restriction-glue.proof.md, paragraph (2).
(blueprint: lem-sfb-integral-exceptional-affine-factorization).

Proof: The finite-type affine morphism U -> V has a finite polynomial presentation,
giving a closed immersion i into A^d_V and the displayed equation of scheme morphisms.
All chart schemes are separated of finite type over k: they are affine opens in
Noetherian schemes, and affine space is separated and of finite type over V.
Choose boundary compactifications of p and i, and obtain their right adjoints from
the integral Brown theorem. Open restriction preserves the localizing category.
Composition of compact support, together with open extension/restriction adjunctions,
identifies the left adjoint of u* G with the left adjoint of v* Gp Gi.
The natural Hom bijections, or uniqueness of right adjoints, give the displayed
object isomorphism for every K in the localizing category. No bounded constructibility
hypothesis is needed here. Empty charts and d=0 are included in the polynomial
presentation and identity adjunction cases. The statement makes no preservation claim.
-/
theorem integralExceptionalAffineFactorization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory)
    (_adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G)
    (U : X.Opens) (V : Y.Opens) (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (_hUV : U ≤ f ⁻¹ᵁ V) :
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    ∃ (d : ℕ) (i : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme)
      (_hi : IsClosedImmersion i) (_hio : i.IsOver (Spec (.of k)))
      (cp : Compactification.BoundaryCompactification
        (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme))
      (hp : ∀ K, localizing Λ (AffineSpace (ULift.{u} (Fin d)) V.toScheme) K →
        localizing Λ V.toScheme ((image Λ cp.obj.obj).obj K))
      (Gp : (localizing Λ V.toScheme).FullSubcategory ⥤
        (localizing Λ (AffineSpace (ULift.{u} (Fin d)) V.toScheme)).FullSubcategory)
      (_adjp : lowerShriek Λ cp.obj.obj hp ⊣ Gp)
      (ci : Compactification.BoundaryCompactification i)
      (hi' : ∀ K, localizing Λ U.toScheme K →
        localizing Λ (AffineSpace (ULift.{u} (Fin d)) V.toScheme)
          ((image Λ ci.obj.obj).obj K))
      (Gi : (localizing Λ (AffineSpace (ULift.{u} (Fin d)) V.toScheme)).FullSubcategory ⥤
        (localizing Λ U.toScheme).FullSubcategory)
      (_adji : lowerShriek Λ ci.obj.obj hi' ⊣ Gi),
      i ≫ (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) ≫ V.ι = U.ι ≫ f ∧
      ∀ K : (localizing Λ Y).FullSubcategory,
        ∃ hK : localizing Λ V.toScheme ((pull Λ V.ι).obj K.obj),
          Nonempty ((pull Λ U.ι).obj (G.obj K).obj ≅
            (Gi.obj (Gp.obj ⟨(pull Λ V.ι).obj K.obj, hK⟩)).obj) := by
  classical
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let : IsAffine U.toScheme := _hU
  let : IsAffine V.toScheme := _hV
  let : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  let : QuasiCompact U.ι := inferInstance
  let : QuasiCompact V.ι := inferInstance
  let : LocallyOfFiniteType (U.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of k)))
  let : QuasiCompact (U.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (U.ι ≫ X ↘ Spec (.of k)))
  let : IsSeparated (U.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (U.ι ≫ X ↘ Spec (.of k)))
  let : LocallyOfFiniteType (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ Y ↘ Spec (.of k)))
  let : QuasiCompact (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (V.ι ≫ Y ↘ Spec (.of k)))
  let : IsSeparated (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (V.ι ≫ Y ↘ Spec (.of k)))
  let q := f.resLE V U _hUV
  obtain ⟨d, i, hi, hqi⟩ := affine_presentation q
  let := hi
  let A := AffineSpace (ULift.{u} (Fin d)) V.toScheme
  let p : A ⟶ V.toScheme := A ↘ V.toScheme
  have hq : q ≫ V.ι = U.ι ≫ f := by simp [q]
  have hio : i.IsOver (Spec (.of k)) := by
    constructor
    change i ≫ p ≫ (V.toScheme ↘ Spec (.of k)) = U.toScheme ↘ Spec (.of k)
    rw [← Category.assoc, hqi]
    change q ≫ V.ι ≫ (Y ↘ Spec (.of k)) = U.ι ≫ (X ↘ Spec (.of k))
    rw [← Category.assoc, hq, Category.assoc, comp_over f]
  let := hio
  let : LocallyOfFiniteType (A ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ V.toScheme ↘ Spec (.of k)))
  let : QuasiCompact (A ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (p ≫ V.toScheme ↘ Spec (.of k)))
  let : IsSeparated (A ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (p ≫ V.toScheme ↘ Spec (.of k)))
  obtain ⟨cp⟩ := compactification_over_base (S := Spec (.of k)) p
  let ci : Compactification.BoundaryCompactification i :=
    ⟨⟨Compactification.ofIsProper i,
      inferInstanceAs (QuasiCompact (𝟙 U.toScheme))⟩⟩
  obtain ⟨_, _, hp, hPA, hPV, Gp, sP, _, adjp, _, _⟩ :=
    exists_integralBrownAdjoint ℓ E k p cp
  obtain ⟨_, _, hi', hIU, hIA, Gi, sI, _, adji, _, _⟩ :=
    exists_integralBrownAdjoint ℓ E k i ci
  refine ⟨d, i, hi, hio, cp, hp, Gp, adjp, ci, hi', Gi, adji, ?_, ?_⟩
  · rw [← Category.assoc, hqi, hq]
  · let US := space k U.toScheme
    let VS := space k V.toScheme
    let AS := space k A
    let XS := space k X
    let YS := space k Y
    let us : US ⟶ XS := ObjectProperty.homMk (U.ι.asOver (Spec (.of k)))
    let vs : VS ⟶ YS := ObjectProperty.homMk (V.ι.asOver (Spec (.of k)))
    let fs : XS ⟶ YS := ObjectProperty.homMk (f.asOver (Spec (.of k)))
    let ps : AS ⟶ VS := ObjectProperty.homMk (p.asOver (Spec (.of k)))
    let is : US ⟶ AS := ObjectProperty.homMk (i.asOver (Spec (.of k)))
    let cu : Compactification.BoundaryCompactification U.ι :=
      ⟨⟨Compactification.ofIsOpenImmersion U.ι,
        inferInstanceAs (QuasiCompact U.ι)⟩⟩
    let cv : Compactification.BoundaryCompactification V.ι :=
      ⟨⟨Compactification.ofIsOpenImmersion V.ι,
        inferInstanceAs (QuasiCompact V.ι)⟩⟩
    obtain ⟨pres, φ, μ, coh⟩ := integralLocalizingCompactSupport ℓ E k
    let hu : ∀ M, localizing Λ U.toScheme M →
        localizing Λ X ((image Λ cu.obj.obj).obj M) :=
      fun M hM ↦ pres.maps_localizing (f := us) cu.obj M hM
    let hv : ∀ M, localizing Λ V.toScheme M →
        localizing Λ Y ((image Λ cv.obj.obj).obj M) :=
      fun M hM ↦ pres.maps_localizing (f := vs) cv.obj M hM
    let hPu : ∀ N : (localizing Λ X).FullSubcategory,
        localizing Λ U.toScheme ((pull Λ U.ι).obj N.obj) :=
      fun N ↦ coh.localizing_pull us N.obj N.property
    let hPv : ∀ N : (localizing Λ Y).FullSubcategory,
        localizing Λ V.toScheme ((pull Λ V.ι).obj N.obj) :=
      fun N ↦ coh.localizing_pull vs N.obj N.property
    let Pu := (localizing Λ U.toScheme).lift ((localizing Λ X).ι ⋙ pull Λ U.ι) hPu
    let Pv := (localizing Λ V.toScheme).lift ((localizing Λ Y).ι ⋙ pull Λ V.ι) hPv
    let Lu := lowerShriek Λ cu.obj.obj hu
    let Lv := lowerShriek Λ cv.obj.obj hv
    let au : Lu ⊣ Pu :=
      liftAdjunction (localizing Λ U.toScheme) (localizing Λ X)
        ((openAdjunction Λ U.ι).ofNatIsoLeft (mateOpenTrivialLowerShriek Λ U.ι).symm)
        (fun M ↦ hu M.obj M.property) hPu
    let av : Lv ⊣ Pv :=
      liftAdjunction (localizing Λ V.toScheme) (localizing Λ Y)
        ((openAdjunction Λ V.ι).ofNatIsoLeft (mateOpenTrivialLowerShriek Λ V.ι).symm)
        (fun M ↦ hv M.obj M.property) hPv
    obtain ⟨cip⟩ := compactification_over_base (S := Spec (.of k)) (i ≫ p)
    obtain ⟨ce⟩ := compactification_over_base (S := Spec (.of k)) (U.ι ≫ f)
    have heq : i ≫ p ≫ V.ι = U.ι ≫ f := by rw [← Category.assoc, hqi, hq]
    let ces : Compactifications k ((is ≫ ps) ≫ vs) :=
      ⟨ce.obj.obj.copy (by
        change (i ≫ p) ≫ V.ι = U.ι ≫ f
        simpa only [Category.assoc] using heq), ce.obj.property⟩
    let hip : ∀ M, localizing Λ U.toScheme M →
        localizing Λ V.toScheme ((image Λ cip.obj.obj).obj M) :=
      fun M hM ↦ pres.maps_localizing (f := is ≫ ps) cip.obj M hM
    let he : ∀ M, localizing Λ U.toScheme M →
        localizing Λ Y ((image Λ ce.obj.obj).obj M) :=
      fun M hM ↦ pres.maps_localizing (f := us ≫ fs) ce.obj M hM
    let Lf := lowerShriek Λ c.obj.obj h
    let Li := lowerShriek Λ ci.obj.obj hi'
    let Lp := lowerShriek Λ cp.obj.obj hp
    let Lip := lowerShriek Λ cip.obj.obj hip
    let Le := lowerShriek Λ ce.obj.obj he
    let euf : Lu ⋙ Lf ≅ Le :=
      liftIso (F := Lu ⋙ Lf) (G := Le) (localizing Λ Y) (μ us fs cu.obj c.obj ce.obj)
    let eip : Li ⋙ Lp ≅ Lip :=
      liftIso (F := Li ⋙ Lp) (G := Lip) (localizing Λ V.toScheme) (μ is ps ci.obj cp.obj cip.obj)
    let eipv : Lip ⋙ Lv ≅ Le :=
      liftIso (F := Lip ⋙ Lv) (G := Le) (localizing Λ Y) (μ (is ≫ ps) vs cip.obj cv.obj ces)
    let eleft : Lu ⋙ Lf ≅ (Li ⋙ Lp) ⋙ Lv :=
      euf ≪≫ eipv.symm ≪≫ (Functor.isoWhiskerRight eip Lv).symm
    let adjA : Lu ⋙ Lf ⊣ G ⋙ Pu := au.comp _adj
    let adjB : (Li ⋙ Lp) ⋙ Lv ⊣ Pv ⋙ (Gp ⋙ Gi) := (adji.comp adjp).comp av
    let eright := Adjunction.rightAdjointUniq adjA (adjB.ofNatIsoLeft eleft.symm)
    intro K
    refine ⟨hPv K, ⟨?_⟩⟩
    exact ((localizing Λ U.toScheme).ι).mapIso (eright.app K)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
