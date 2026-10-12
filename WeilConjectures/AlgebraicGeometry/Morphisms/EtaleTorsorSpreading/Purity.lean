/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Datum
public import WeilConjectures.AlgebraicGeometry.Morphisms.PuritySmooth
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# From the section to the whole fibre: purity

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`)
over a Noetherian base, let `s` be a point of `S` other than the generic point. If the
normalization `N ⟶ C` of `C` in the Galois cover is étale over all strict generizations of `s`
and over `σ(s)`, it is étale over all of the fibre `C_s`
(`AlgebraicGeometry.Scheme.SpreadingDatum.etaleOver_of_etaleOverSection`).

Indeed the fibre `C_s` is irreducible (smooth with geometrically connected fibres), so its
generic point `ξ_s` specializes to `σ(s)`; as `N ⟶ C` is integral, the set of points of `C`
over which it is étale is stable under generization, so `N` is étale over `ξ_s`, hence over a
dense subset of `C_s`. Purity
(`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`, [Stacks 0EYE] and
[Stacks 0EYB]) then gives étaleness over all of `C_s`; it applies since `N` is the normalization
of `C` in the regular (smooth over `κ(η)`) scheme `Z.P`, which lies over the generic point of `S`.

This is the common final step of the trait case and of the case of depth at least two in the
proof of [Stacks 0EYJ].
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

lemma etaleOver_iff (s : D.S) : D.EtaleOver s ↔ ∀ x : D.ν.normalization,
    D.c (D.ν.fromNormalization x) = s → x ∈ D.ν.fromNormalization.etaleLocus := by
  simp only [EtaleOver, Scheme.Hom.mem_etaleLocus]

lemma etaleOverSection_iff (s : D.S) : D.EtaleOverSection s ↔ ∀ x : D.ν.normalization,
    D.ν.fromNormalization x = D.σ s → x ∈ D.ν.fromNormalization.etaleLocus := by
  simp only [EtaleOverSection, Scheme.Hom.mem_etaleLocus]

instance : GeometricallyIrreducible D.c := .of_smooth_of_geometricallyConnected D.c

/-- The generic point of the fibre `C_s`, which is irreducible. -/
noncomputable def fibreGenericPoint (s : D.S) : D.C :=
  D.c.fiberι s (genericPoint (D.c.fiber s))

lemma c_fibreGenericPoint (s : D.S) : D.c (D.fibreGenericPoint s) = s := by
  have : D.fibreGenericPoint s ∈ Set.range (D.c.fiberι s) := ⟨_, rfl⟩
  rwa [Scheme.Hom.range_fiberι] at this

lemma fibreGenericPoint_specializes {s : D.S} {x : D.C} (hx : D.c x = s) :
    D.fibreGenericPoint s ⤳ x := by
  have : x ∈ Set.range (D.c.fiberι s) := by rw [Scheme.Hom.range_fiberι]; exact hx
  obtain ⟨x, rfl⟩ := this
  exact (genericPoint_specializes x).map (D.c.fiberι s).continuous

/-- If the normalization is étale over `σ(s)`, it is étale over the generic point of `C_s`. -/
lemma mem_etaleLocus_of_fibreGenericPoint {s : D.S} (hsec : D.EtaleOverSection s)
    (x : D.ν.normalization) (hx : D.ν.fromNormalization x = D.fibreGenericPoint s) :
    x ∈ D.ν.fromNormalization.etaleLocus :=
  Scheme.Hom.mem_etaleLocus_of_specializes
    (D.fibreGenericPoint_specializes (by rw [← Scheme.Hom.comp_apply, D.σ_c]; rfl))
    ((D.etaleOverSection_iff s).1 hsec) x hx

instance : Smooth D.q := MorphismProperty.of_isPullback D.isPullback.flip inferInstance

instance : IsRegular D.Z.P := IsRegular.of_smooth (D.Z.π ≫ D.q)

instance : IsLocallyNoetherian D.Z.P :=
  LocallyOfFiniteType.isLocallyNoetherian (D.Z.π ≫ D.q)

/-- The local rings of the Galois cover are integrally closed domains (it is regular). -/
lemma isDomain_isIntegrallyClosed_stalk (z : D.Z.P) :
    IsDomain (D.Z.P.presheaf.stalk z) ∧ IsIntegrallyClosed (D.Z.P.presheaf.stalk z) := by
  have := IsRegular.uniqueFactorizationMonoid_stalk z
  exact ⟨inferInstance, UniqueFactorizationMonoid.instIsIntegrallyClosed⟩

/-- The Galois cover lies over the generic point of `S`. -/
lemma c_ν (z : D.Z.P) : D.c (D.ν z) = genericPoint D.S := by
  rw [← Scheme.Hom.comp_apply, Category.assoc, ← D.isPullback.w, ← Category.assoc,
    Scheme.Hom.comp_apply]
  exact (congrArg _ (Subsingleton.elim _ (IsLocalRing.closedPoint _))).trans
    Scheme.fromSpecStalk_closedPoint

lemma ne_genericPoint_of_coheight_ne_zero {s : D.S} (hs : Order.coheight s ≠ 0) :
    s ≠ genericPoint D.S := by
  rintro rfl
  refine hs (Order.coheight_eq_zero.2 fun b _ ↦ ?_)
  exact Scheme.le_iff_specializes.2 ((genericPoint_spec D.S).specializes (Set.mem_univ b))

/-- Purity step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois` (common to the
trait case and to the case of depth at least two in the proof of [Stacks 0EYJ]): over a
Noetherian base, at a point `s` other than the generic point, if the normalization `N ⟶ C` is
étale over all strict generizations of `s` and over `σ(s)`, it is étale over all of `C_s`.

The generic point `ξ_s` of the irreducible fibre `C_s` specializes to `σ(s)`, so `N` is étale
over `ξ_s`, a dense point of `C_s`, and purity
(`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`) applies. -/
theorem etaleOver_of_etaleOverSection [IsNoetherian D.S] {s : D.S} (hs : s ≠ genericPoint D.S)
    (H : ∀ s' : D.S, s' ⤳ s → s' ≠ s → D.EtaleOver s') (hsec : D.EtaleOverSection s) :
    D.EtaleOver s := by
  rw [etaleOver_iff]
  refine Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth D.isIntegrallyClosed_stalk D.c
    D.ν D.isDomain_isIntegrallyClosed_stalk D.c_ν s hs
    (fun y h₁ h₂ ↦ (D.etaleOver_iff _).1 (H _ h₁ h₂) y rfl) (fun x hx ↦ ?_)
  exact ⟨D.fibreGenericPoint s, D.fibreGenericPoint_specializes hx, D.c_fibreGenericPoint s,
    D.mem_etaleLocus_of_fibreGenericPoint hsec⟩

end AlgebraicGeometry.Scheme.SpreadingDatum
