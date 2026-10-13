/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

public import Sheaf.RingTheory.Depth

public import Mathlib.RingTheory.MvPowerSeries.Basic

import Mathlib.RingTheory.IntegralClosure.GoingDown
import Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense
import Sheaf.RingTheory.FlatLocalDepthFormula
import Sheaf.RingTheory.NormalLocalDepthTwo

/-! # Formal test: BoundaryDepths -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 0EYJ; Tags 0EY6, 0EY9, 0337 and 031S.
(blueprint: lem-sbc-stalk-normalization-formal-boundary-depths)

Proof: Minimality identifies the local base open with the punctured spectrum
of A. The localized normalization is normal and its open preimage is dense.
Smooth flat local maps make boundary target points have height at least two,
using the depth hypothesis on A and the flat local depth formula. Going down
for the finite integral extension of normal domains gives height at least two
at its boundary source points. Normal Serre S2 then gives source depth at least
two. Flat base change by t induces flat local maps on source stalks, so the
flat local depth formula preserves this bound. Each stalk of the split finite
coproduct is a stalk of one copy of T. The Noetherian power-series ring is flat
over A, and the base equation makes the complement of V lie over the closed
point of A. The flat local depth formula therefore gives depth at least two
for these stalks as well. The argument includes d = 0; a trivial group has
one summand. These bounds do not identify either cover on V. -/
theorem GaloisCover.stalk_normalization_formal_boundary_depths {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (G : Type (u + 1)) [Finite G]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ (d : ℕ)
      (t : Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s))) ⟶ pullback c a),
      Flat t →
      t ≫ pullback.snd c a =
        Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin d))) →
      let T := Spec (.of (MvPowerSeries (Fin d) (S.presheaf.stalk s)))
      let F : Scheme.{u} := pullback n t
      let E : Scheme.{u} := ∐ (fun _ : G ↦ T)
      let V := (t ≫ pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U)
      let r : F ⟶ T := pullback.snd n t
      let p : E ⟶ T := Sigma.desc (fun _ : G ↦ 𝟙 T)
      (∀ x : F, r x ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk x) (F.presheaf.stalk x)) ∧
      (∀ x : E, p x ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk x) (E.presheaf.stalk x)) := by sorry

end AlgebraicGeometry.Scheme
