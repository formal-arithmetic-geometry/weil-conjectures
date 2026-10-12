/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Algebra.Module.DegreeZeroFractions
import Sheaf.AlgebraicGeometry.ProjStandardOpenProperties
import Sheaf.Topology.SheafOfModulesFromBasis
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.RingTheory.Localization.Module

/-!
# Comparing Proj module sheaves from fraction charts

Source: Stacks Project, Constructions, Lemma 01M7; Sheaves on Spaces, Tags 009N and 009U.
(blueprint: lem-sc-proj-graded-chart-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem iso_of_basis (X : TopCat.{u}) (R : TopCat.Sheaf RingCat.{u} X)
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (hrefine : ∀ (U : B) (C : Set B),
      (∀ V ∈ C, V.val ≤ U.val) → (⨆ V ∈ C, V.val) = U.val →
      ∃ (n : ℕ) (W : Fin n → B), (⨆ i, (W i).val) = U.val ∧
        ∀ i, ∃ V ∈ C, (W i).val ≤ V.val)
    (F G : SheafOfModules.{u} R)
    (l : ∀ U : B, F.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)]
      G.val.obj (op U.val))
    (hl : ∀ (U V : B) (h : V.val ≤ U.val) (s : F.val.obj (op U.val)),
      l V (F.val.map (homOfLE h).op s) = G.val.map (homOfLE h).op (l U s)) :
    Nonempty (F ≅ G) := by
  let r (U V : B) (h : V.val ≤ U.val) : F.val.obj (op U.val) →+
      F.val.obj (op V.val) := (F.val.presheaf.map (homOfLE h).op).hom
  have hid (U : B) (s : F.val.obj (op U.val)) : r U U le_rfl s = s := by
    simp [r]
  have hcomp (U V W : B) (hVU : V.val ≤ U.val) (hWV : W.val ≤ V.val)
      (s : F.val.obj (op U.val)) :
      r V W hWV (r U V hVU s) = r U W (hWV.trans hVU) s := by
    change F.val.presheaf.map _ (F.val.presheaf.map _ s) = F.val.presheaf.map _ s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hscalar (U V : B) (h : V.val ≤ U.val) (a : R.obj.obj (op U.val))
      (s : F.val.obj (op U.val)) :
      r U V h (a • s) = R.obj.map (homOfLE h).op a • r U V h s :=
    F.val.map_smul _ _ _
  have hglue (U : B) (n : ℕ) (V : Fin n → B) (hV : ∀ i, (V i).val ≤ U.val)
      (hcover : (⨆ i, (V i).val) = U.val) (s : ∀ i, F.val.obj (op (V i).val))
      (hs : ∀ i j,
        r (V i) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_left (s i) =
        r (V j) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_right (s j)) :
      ∃! t : F.val.obj (op U.val), ∀ i, r U (V i) (hV i) t = s i := by
    let F' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.val.presheaf, F.isSheaf⟩
    exact F'.existsUnique_gluing' (fun i ↦ (V i).val) U.val
      (fun i ↦ homOfLE (hV i)) hcover.ge s (by
        intro i j
        exact hs i j)
  obtain ⟨_, _, _, _, huniq, _⟩ := Opens.exists_sheafOfModules_from_basis X B hB hcap
    hrefine R (fun U ↦ F.val.obj (op U.val)) r hid hcomp hscalar hglue
  obtain ⟨eF, _, _⟩ := huniq F (fun U ↦ LinearEquiv.refl _ _) (by
    intro U V h s
    rfl)
  obtain ⟨eG, _, _⟩ := huniq G (fun U ↦ (l U).symm) (by
    intro U V h s
    apply (l V).injective
    simp only [LinearEquiv.apply_symm_apply]
    calc
      G.val.map (homOfLE h).op s =
          l V (F.val.map (homOfLE h).op ((l U).symm s)) := by
        simpa only [LinearEquiv.apply_symm_apply] using (hl U V h ((l U).symm s)).symm
      _ = l V (r U V h ((l U).symm s)) := by
        congr 1)
  exact ⟨eF.symm ≪≫ eG⟩

set_option maxHeartbeats 800000 in
-- Localized equivalences and dependent chart transports require more elaboration heartbeats.
/-- A linear equivalence preserving numerator degrees compares sheaves given by charts.
Source: Stacks Project, Constructions, Lemma 01M7; Sheaves on Spaces, Tags 009N and 009U;
steps 2 and 3 of lem-sc-p1-homogeneous-basis-proj-coproduct.
(blueprint: lem-sc-proj-graded-chart-comparison)

Proof: Localize e and e.symm at powers of each positive homogeneous f. On a fraction,
these maps send y/h to e(y)/h and e.symm(y)/h. The degree hypothesis identifies the
prescribed degree-zero subsets in both directions, since the denominator is unchanged.
The injective chart maps with the stated images therefore give additive equivalences
of the section groups. The scalar formulas make them linear over the chart ring, which
is isomorphic to the ring of sections via awayToSection. For an inclusion D(g) <= D(f),
standardOpenProperties supplies e'>0 and homogeneous a with g^e'=a*f. Choose a fraction
representative y/f^m for a section. The two restriction formulas agree after applying
the localized equivalence, because e(a^m • y)=a^m • e(y). Thus the linear equivalences
and their inverses commute with every restriction. Positive homogeneous standard opens
form a basis closed under intersections and admitting finite refinements. Restrict F
and G to this basis. The uniqueness clause of exists_sheafOfModules_from_basis glues
the compatible equivalences to a sheaf isomorphism. Alternatively, extend both maps
from the basis and check their inverse identities there. Empty opens cause no exception:
the section modules and the relevant localized degree-zero subsets are zero. No stalk
comparison or internal-grading hypothesis is required once these charts are provided. -/
theorem graded_chart_comparison (k : Type u) [Field k]
    (M N : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℕ → Set M) (𝓝 : ℕ → Set N)
    (e : M ≃ₗ[MvPolynomial (Fin 2) k] N)
    (hdegree : ∀ (n : ℕ) (y : M), y ∈ 𝓜 n ↔ e y ∈ 𝓝 n)
    (F G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ 𝓜 n) (Submonoid.powers f))
    (hscalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s)
    (hres : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (beta : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f N)
    (hbeta : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (beta f d hd hf) ∧
        Set.range (beta f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ 𝓝 n) (Submonoid.powers f))
    (hbetaScalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        beta f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • beta f d hd hf s)
    (hbetaRes : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : N)
          (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          beta f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          beta g b hb hg (G.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    : Nonempty (F ≅ G) := by
  classical
  let S := MvPolynomial (Fin 2) k
  let 𝒜 := homogeneousSubmodule (Fin 2) k
  let I := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
  let D (f : I) := basicOpen 𝒜 f.val.1
  let L (f : I) : LocalizedModule.Away f.val.1 M ≃ₗ[Localization.Away f.val.1]
      LocalizedModule.Away f.val.1 N :=
    IsLocalizedModule.mapEquiv (Submonoid.powers f.val.1)
      (mkLinearMap _ M) (mkLinearMap _ N) (Localization.Away f.val.1) e
  have hL (f : I) (y : M) (h : Submonoid.powers f.val.1) :
      L f (mk y h) = mk (e y) h := by
    change LocalizedModule.map (Submonoid.powers f.val.1) e.toLinearMap (mk y h) = _
    exact LocalizedModule.map_mk _ _ _ _
  let A (f : I) := alpha f.val.1 f.val.2 f.property.1 f.property.2
  let B (f : I) := beta f.val.1 f.val.2 f.property.1 f.property.2
  have hrange (f : I) (x : LocalizedModule.Away f.val.1 M) :
      x ∈ (A f).range ↔ L f x ∈ (B f).range := by
    change x ∈ Set.range (A f) ↔ L f x ∈ Set.range (B f)
    rw [(halpha f.val.1 f.val.2 f.property.1 f.property.2).2,
      (hbeta f.val.1 f.val.2 f.property.1 f.property.2).2]
    constructor
    · rintro ⟨n, y, h, hy, hh, rfl⟩
      exact ⟨n, e y, h, (hdegree n y).mp hy, hh, (hL f y h).symm⟩
    · rintro ⟨n, y, h, hy, hh, heq⟩
      refine ⟨n, e.symm y, h, ?_, hh, ?_⟩
      · exact (hdegree n (e.symm y)).mpr (by simpa using hy)
      · apply (L f).injective
        simpa only [hL, LinearEquiv.apply_symm_apply] using heq
  let toB (f : I) : F.val.obj (op (D f)) →+ (B f).range :=
    { toFun := fun s ↦ ⟨L f (A f s), (hrange f _).mp ⟨s, rfl⟩⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun s t ↦ Subtype.ext (by simp) }
  let phi (f : I) : F.val.obj (op (D f)) →+ G.val.obj (op (D f)) :=
    (AddMonoidHom.ofInjective
      (hbeta f.val.1 f.val.2 f.property.1 f.property.2).1).symm.toAddMonoidHom.comp (toB f)
  have hphi (f : I) (s : F.val.obj (op (D f))) : B f (phi f s) = L f (A f s) :=
    AddMonoidHom.apply_ofInjective_symm
      (hbeta f.val.1 f.val.2 f.property.1 f.property.2).1 _
  have hbij (f : I) : Function.Bijective (phi f) := by
    constructor
    · intro s t hst
      apply (halpha f.val.1 f.val.2 f.property.1 f.property.2).1
      apply (L f).injective
      rw [← hphi, ← hphi, hst]
    · intro t
      have ht : (L f).symm (B f t) ∈ (A f).range := by
        apply (hrange f _).mpr
        rw [LinearEquiv.apply_symm_apply]
        exact ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := ht
      refine ⟨s, (hbeta f.val.1 f.val.2 f.property.1 f.property.2).1 ?_⟩
      rw [hphi, hs, LinearEquiv.apply_symm_apply]
  have hphiScalar (f : I) (q : (Proj 𝒜).presheaf.obj (op (D f)))
      (s : F.val.obj (op (D f))) : phi f (q • s) = q • phi f s := by
    let Riso := basicOpenIsoAway 𝒜 f.val.1 f.property.2 f.property.1
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso Riso.hom).2 q
    apply (hbeta f.val.1 f.val.2 f.property.1 f.property.2).1
    rw [hphi]
    change L f (A f (awayToSection 𝒜 f.val.1 r • s)) =
      B f (awayToSection 𝒜 f.val.1 r • phi f s)
    rw [hscalar, hbetaScalar, hphi, map_smul]
  let lin (f : I) : F.val.obj (op (D f)) ≃ₗ[(Proj 𝒜).presheaf.obj (op (D f))]
      G.val.obj (op (D f)) :=
    { AddEquiv.ofBijective (phi f) (hbij f) with map_smul' := hphiScalar f }
  have hlin (f g : I) (inc : D g ≤ D f) (s : F.val.obj (op (D f))) :
      lin g (F.val.map (homOfLE inc).op s) =
        G.val.map (homOfLE inc).op (lin f s) := by
    obtain ⟨e', c, a, he', ha, hrel⟩ :=
      ((standardOpenProperties.{u, u, u} 𝒜).2.2.1 f.val.1 g.val.1 f.val.2 g.val.2
        f.property.1 g.property.1 f.property.2 g.property.2).1.mp inc
    have hx : A f s ∈ degreeZeroFractions (fun n ↦ (𝒜 n : Set S)) 𝓜
        (Submonoid.powers f.val.1) := by
      rw [← (halpha f.val.1 f.val.2 f.property.1 f.property.2).2]
      exact ⟨s, rfl⟩
    obtain ⟨n, y, h, _, _, hy⟩ := hx
    obtain ⟨m, hm⟩ := h.property
    have hh : h = (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) :=
      Subtype.ext hm.symm
    have hs : A f s = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) := by
      rw [← hy, hh]
    have ht : B f (lin f s) =
        mk (e y) (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) := by
      change B f (phi f s) = _
      rw [hphi, hs, hL]
    apply (hbeta g.val.1 g.val.2 g.property.1 g.property.2).1
    change B g (phi g (F.val.map (homOfLE inc).op s)) =
      B g (G.val.map (homOfLE inc).op (lin f s))
    rw [hphi]
    rw [hres f.val.1 g.val.1 f.val.2 g.val.2 f.property.1 g.property.1
      f.property.2 g.property.2 inc e' c a he' ha hrel m y s hs]
    rw [hbetaRes f.val.1 g.val.1 f.val.2 g.val.2 f.property.1 g.property.1
      f.property.2 g.property.2 inc e' c a he' ha hrel m (e y) (lin f s) ht]
    rw [hL, map_smul]
  let basis := Set.range D
  have hBasis : Opens.IsBasis basis := by
    convert (standardOpenProperties.{u, u, u} 𝒜).1 using 1
    ext U
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f.val.1, f.val.2, f.property.1, f.property.2, rfl⟩
    · rintro ⟨f, n, hn, hf, rfl⟩
      exact ⟨⟨⟨f, n⟩, hn, hf⟩, rfl⟩
  have hcap (U V : basis) : U.val ⊓ V.val ∈ basis := by
    obtain ⟨f, hf⟩ := U.property
    obtain ⟨g, hg⟩ := V.property
    refine ⟨⟨⟨f.val.1 * g.val.1, f.val.2 + g.val.2⟩,
      by omega, SetLike.mul_mem_graded f.property.2 g.property.2⟩, ?_⟩
    rw [← hf, ← hg]
    exact ((standardOpenProperties.{u, u, u} 𝒜).2.1 f.val.1 g.val.1 f.val.2 g.val.2
      f.property.1 g.property.1 f.property.2 g.property.2).symm
  have hrefine (U : basis) (C : Set basis) (_hC : ∀ V ∈ C, V.val ≤ U.val)
      (hcover : (⨆ V ∈ C, V.val) = U.val) :
      ∃ (n : ℕ) (W : Fin n → basis), (⨆ i, (W i).val) = U.val ∧
        ∀ i, ∃ V ∈ C, (W i).val ≤ V.val := by
    obtain ⟨f, hf⟩ := U.property
    have hcover' : (⨆ V : C, V.val.val) = D f := by
      simpa only [iSup_subtype, hf] using hcover
    obtain ⟨n, g, t, ht, hgt, hsub⟩ := (standardOpenProperties.{u, u, u} 𝒜).2.2.2.1
      f.val.1 f.val.2 f.property.1 f.property.2 C (fun V ↦ V.val.val) hcover'
    let W (i : Fin n) : basis :=
      ⟨basicOpen 𝒜 (g i), ⟨⟨⟨g i, t i⟩, ht i⟩, rfl⟩⟩
    refine ⟨n, W, ?_, ?_⟩
    · exact hgt.symm.trans hf
    · intro i
      obtain ⟨V, hV⟩ := hsub i
      exact ⟨V.val, V.property, hV⟩
  let idx (U : basis) : I := U.property.choose
  have hidx (U : basis) : D (idx U) = U.val := U.property.choose_spec
  let l (U : basis) : F.val.obj (op U.val) ≃ₗ[(Proj 𝒜).presheaf.obj (op U.val)]
      G.val.obj (op U.val) := (hidx U) ▸ lin (idx U)
  have hlin' (f g : I) (U V : (Proj 𝒜).Opens) (hf : D f = U) (hg : D g = V)
      (inc : V ≤ U) (s : F.val.obj (op U)) :
      (hg ▸ lin g) (F.val.map (homOfLE inc).op s) =
        G.val.map (homOfLE inc).op ((hf ▸ lin f) s) := by
    subst U
    subst V
    exact hlin f g inc s
  apply iso_of_basis (Proj 𝒜).toTopCat (Proj 𝒜).ringCatSheaf
    basis hBasis hcap hrefine F G l
  intro U V h s
  exact hlin' (idx U) (idx V) U.val V.val (hidx U) (hidx V) h s

end AlgebraicGeometry.Proj
