/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

public import Mathlib.RingTheory.AdjoinRoot

import Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison
import Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts

/-!
# Standard tame charts for normalization over a local trait

Source: Stacks Project, Tags 0EYJ, 0EYG and 0EYH.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The concrete local normalization admits jointly surjective affine etale charts on which
it is a finite product of standard tame monic extensions.

Source: Stacks Project, Tags 0EYJ (trait paragraph), 0EYG and 0EYH.
(blueprint: lem-sbc-stalk-normalization-trait-charts)

Proof: Write A = O_{S,s}. The points of Spec A map to the generalizations of s.
Minimality outside U identifies its inverse image with the punctured spectrum, which,
for the DVR A, is Spec Frac A. The generic-fibre pullback squares identify the given
finite etale model there with the base change of Z. Smoothness over A makes the closed
fibre a regular effective Cartier divisor, cut out by a uniformizer: flatness makes
that uniformizer a nonzerodivisor and smoothness over the residue field makes the
fibre regular. At the codimension-one points of this divisor, each connected component
of the generic cover is Galois with stabilizer a subgroup of G. Its ramification indices
and residue degrees divide the invertible order of the stabilizer (Tag 09EB), so the
ramification indices are prime to the residue characteristic. In positive residue characteristic
the inseparable residue degree is a power of that characteristic and divides the
residue degree, so it is one. Thus the residue extensions are separable and the cover
is tame in codimension one. Apply 0EYG and 0EYH to obtain, around each point of the local
total space, an affine etale neighbourhood Spec R and a finite disjoint union of standard
covers Spec R[T]/(T^e-f), with e positive and invertible in R. Relative normalization
commutes with localization on the base (Stacks Tag 0307); hence the normalization on
the local total space is the concrete pullback n. Its formation also commutes with
etale base change (Tags 03GE and 03GV), so the comparison is an isomorphism over Spec R, not just
an abstract isomorphism of schemes. Finite disjoint unions of these affine spectra
are the spectrum of their product. Choose one neighbourhood for each point and index
its finitely many components by Fin m. The neighbourhoods are jointly surjective.
Off the divisor the finite etale cover is etale locally split; use e = 1 and f = 1.
An empty cover is represented by m = 0, whose product is the zero ring. This construction
uses no section and no rational point. -/
theorem GaloisCover.stalk_normalization_trait_charts {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n →
      ∃ (I : Type u) (R : I → CommRingCat.{u})
        (φ : ∀ i, Spec (R i) ⟶ pullback c a),
        (∀ i, Etale (φ i)) ∧
        (∀ x : ↥(pullback c a), ∃ (i : I) (y : Spec (R i)), φ i y = x) ∧
        ∀ i, ∃ (m : ℕ) (f : R i) (e : Fin m → ℕ),
          (∀ k, 0 < e k ∧ IsUnit (e k : R i)) ∧
          ∃ α : pullback n (φ i) ≅
            Spec (CommRingCat.of (∀ k : Fin m,
              AdjoinRoot ((Polynomial.X : Polynomial (R i)) ^ e k - Polynomial.C f))),
            α.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap (R i) (∀ k : Fin m,
                AdjoinRoot ((Polynomial.X : Polynomial (R i)) ^ e k - Polynomial.C f)))) =
              pullback.snd n (φ i) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  let : IsDiscreteValuationRing (S.presheaf.stalk s) := hdvr
  dsimp only
  intro hn
  let a := S.fromSpecStalk s
  let d := pullback.snd c a
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
  let : IsFinite n := hn
  obtain ⟨W, β, hβ⟩ := GaloisCover.stalk_normalization_generic_comparison
    hS c G q j hCη Z U hηU jU PA ψ hjU hψ s hs hmin hdvr
  let : IsFinite W.π := W.isFinite
  let b := Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) S.functionField))
  let p := W.π ≫ pullback.fst d b
  have hβ' : β.hom ≫ p.fromNormalization = n := hβ
  have hp : IsFinite p.fromNormalization := by
    have h : β.inv ≫ n = p.fromNormalization := by
      rw [← hβ', Iso.inv_hom_id_assoc]
    rw [← h]
    infer_instance
  have hGA : IsUnit (Nat.card G : S.presheaf.stalk s) := by
    simpa using hG.map (S.presheaf.Γgerm s).hom
  have hlocal :=
    GaloisCover.trait_generic_normalization_chart (S.presheaf.stalk s) S.functionField
      d G hGA W hp
  choose R φ y hφ hy hcharts using hlocal
  refine ⟨↥(pullback c a), R, φ, hφ, ?_, ?_⟩
  · intro x
    exact ⟨x, y x, hy x⟩
  intro i
  obtain ⟨m, f, e, he, α, hα⟩ := hcharts i
  let δ : pullback n (φ i) ≅ pullback p.fromNormalization (φ i) :=
    asIso (pullback.map n (φ i) p.fromNormalization (φ i) β.hom (𝟙 _) (𝟙 _)
      (by simpa using hβ'.symm) (by simp))
  refine ⟨m, f, e, he, δ ≪≫ α, ?_⟩
  simp only [Iso.trans_hom, Category.assoc, hα]
  change δ.hom ≫ pullback.snd p.fromNormalization (φ i) = pullback.snd n (φ i)
  simp [δ, pullback.map]


end AlgebraicGeometry.Scheme
