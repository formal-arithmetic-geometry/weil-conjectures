/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.LisseFiltration
import Sheaf.DeligneLaumon.GeometricSemisimplicity
import Sheaf.DeligneLaumon.SimpleLisseSupportModel
import Sheaf.DeligneLaumon.SemisimpleFrobeniusOrbitDescent
import Sheaf.DeligneLaumon.ConstantFieldRestrictionStalk
import WeilConjectures.WeilSheaf.StalkUpperStar

/-! # Geometric constituent orbits of a simple lisse Weil sheaf

This records a decomposition and its point transports, before selecting eigenvalues
or an ambient subquotient diagram.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.WeilSheaf

open ProEtale

private theorem finite_point_lift {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [Surjective f] [LocallyOfFiniteType f] [QuasiCompact f] (z : Z.finitePoints) :
    ∃ y : Y.finitePoints, f y.1 = z.1 := by
  have : Finite (IsLocalRing.ResidueField (Z.presheaf.stalk z.1)) :=
    Z.mem_finitePoints.1 z.2
  obtain ⟨y, hy⟩ := f.surjective z.1
  have : Nonempty (f.fiber z.1) :=
    ⟨(f.fiberHomeo z.1).symm ⟨y, hy⟩⟩
  have : LocallyOfFiniteType (f.fiberToSpecResidueField z.1) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (f.fiberToSpecResidueField z.1) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨w, hw⟩ := (f.fiberToSpecResidueField z.1).exists_mem_finitePoints
  refine ⟨⟨f.fiberι z.1 w, Scheme.Hom.map_mem_finitePoints _ hw⟩, ?_⟩
  exact (f.fiberHomeo z.1 w).2

private theorem charpoly_pow_equiv {K : Type} [Field K]
    {M N : FrobeniusModule.{u + 1, 0} K} (e : M.Equiv N) (r : ℕ) :
    (N.frobeniusEnd ^ r).charpoly = (M.frobeniusEnd ^ r).charpoly := by
  have hpow : ∀ k : ℕ, e.toLinearEquiv.conj M.frobeniusEnd ^ k =
      e.toLinearEquiv.conj (M.frobeniusEnd ^ k) := by
    intro k
    induction k with
    | zero => simp only [pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearEquiv.conj_comp]
  rw [e.frobeniusEnd_eq_conj, hpow, LinearEquiv.charpoly_conj]

-- The unused existential isomorphism binder belongs to the unchanged original signature.
set_option linter.unusedVariables false in
/-- A simple lisse Weil sheaf splits geometrically after a constant extension on its
supporting component. Its summands have conjugate local Frobenius at suitably
translated lifts of a given closed point.

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraphs 1 and 7, and the geometric-socle
argument in the first step of that unit.
(blueprint: lem-zl-geometric-constituent-orbit).

Proof: A simple lisse object has exactly one nonzero connected clopen support
component. Nonzero stalks put x and y there. A finite constant extension splits its
geometric components; choose one. The Frobenius return to that component is still
arithmetically simple. The geometric socle spans it: the finite sum of Frobenius
translates of a simple subobject stabilizes by rank and is a nonzero Weil subobject.
Its geometric isotypic blocks form one Frobenius orbit. On a stabilized block the
return acts as T tensor B; an eigenline of B gives a proper Weil subobject unless
the multiplicity is one. A further constant extension fixes each simple block,
giving S and the direct-sum isomorphism v. The restriction functor R is the actual
iterated pro-etale Weil transport followed by restriction to the component.
Both operations are exact and preserve lisse sheaves. The local point-transport
formula identifies its Frobenius with the residue-degree power of the original
one, with the same exponent for residue cardinality. At all points this also
preserves reality, including repeated powered eigenvalues. Given two summands,
a power of the original Frobenius return carries one to the other; apply it to
the geometric lift of t. Its image t' in the constant-extension model has the
same original image and the same residue degree. The Weil map identifies the
local Frobenius modules on the two summands at t and t'. These transports do not
require the points x and y to differ. Smoothness has constant relative dimension
on the chosen geometric component. If this dimension is zero, the component is
a finite-field point and the simple quotient is a constant line. Pull back the
entire construction to the affine line over that field, using its origin for
both s and t; pullback remains exact, lisse and real, and the one summand stays
geometrically simple. Otherwise retain the component. -/
theorem exists_geometric_constituent_orbit
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsAffine X]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (V : WeilSheaf k₀ l X) (hV : V.IsIrreducibleLisse)
    (x y : X.finitePoints)
    (hx : Nontrivial (V.stalk x).carrier) (hy : Nontrivial (V.stalk y).carrier) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₀ k₁)
      (_ : Fact (ringChar k₁ ≠ l)) (d : ℕ) (C : Scheme.{u})
      (_ : C.Over (Spec (CommRingCat.of k₁))) (_ : IsAffine C)
      (_ : SmoothOfRelativeDimension d (C ↘ Spec (CommRingCat.of k₁)))
      (_ : GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁)))
      (_ : IsSeparated (C ↘ Spec (CommRingCat.of k₁)))
      (_ : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁)))
      (_ : QuasiCompact (C ↘ Spec (CommRingCat.of k₁)))
      (R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C)
      (_ : PreservesFiniteLimits R) (_ : PreservesFiniteColimits R)
      (n : ℕ) (S : Fin n → WeilSheaf k₁ l C)
      (v : R.obj V ≅ ⨁ S) (c : C ⟶ X),
      0 < d ∧
      (∀ F : WeilSheaf k₀ l X, F.IsLisse → (R.obj F).IsLisse) ∧
      (∀ (F : WeilSheaf k₀ l X) (ι : PadicAlgCl l →+* ℂ),
        F.IsReal ι → (R.obj F).IsReal ι) ∧
      (∀ a, (S a).IsGeometricallyIrreducible) ∧
      c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
        (C ↘ Spec (CommRingCat.of k₁)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) ∧
      ∃ (s t : C.finitePoints) (e f : ℕ), 0 < e ∧ 0 < f ∧
        c s.1 = x.1 ∧ c t.1 = y.1 ∧
        (C ↘ Spec (CommRingCat.of k₁)).residueCard s.1 =
          (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 ^ e ∧
        (C ↘ Spec (CommRingCat.of k₁)).residueCard t.1 =
          (X ↘ Spec (CommRingCat.of k₀)).residueCard y.1 ^ f ∧
        ((R.obj V).stalk s).frobeniusEnd.charpoly =
          ((V.stalk x).frobeniusEnd ^ e).charpoly ∧
        ((R.obj V).stalk t).frobeniusEnd.charpoly =
          ((V.stalk y).frobeniusEnd ^ f).charpoly ∧
        ∀ a b : Fin n, ∃ t' : C.finitePoints,
          c t'.1 = y.1 ∧
          (C ↘ Spec (CommRingCat.of k₁)).residueCard t'.1 =
            (C ↘ Spec (CommRingCat.of k₁)).residueCard t.1 ∧
          Nonempty (((S b).stalk t).Equiv ((S a).stalk t')) := by
  classical
  obtain ⟨k₁, hk₁, hfin₁, halg₁, hl₁, d, C₁, hover₁, haff₁, hsm₁, hconn₁,
    hsep₁, hft₁, hqc₁, hirr₁, R₁, hlim₁, hcolim₁, c₁, hd, hV₁, hlisse₁,
    hpoint₁, hc₁, s₁, t₁, hs₁, ht₁⟩ :=
    exists_simple_lisse_support_model V hV x y hx hy
  obtain ⟨N, T, hT, ⟨vT⟩⟩ := exists_geometric_semisimple_decomposition (R₁.obj V) hV₁
  obtain ⟨k₂, hk₂, hfin₂, halg₂, halgext₂, hl₂, r, hr, hcard, C₂, hover₂,
    c₂, hc₂, n, S, ⟨v⟩, hS, horbit⟩ :=
    exists_semisimple_frobenius_orbit_descent (R₁.obj V) hV₁ N T hT vT
  have : IsAffine C₂ := IsAffine.of_isPullback hc₂
  have : SmoothOfRelativeDimension d (C₂ ↘ Spec (CommRingCat.of k₂)) := by
    let := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) hc₂ hsm₁
  have : GeometricallyConnected (C₂ ↘ Spec (CommRingCat.of k₂)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hc₂ hconn₁
  have : IsSeparated (C₂ ↘ Spec (CommRingCat.of k₂)) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hc₂ hsep₁
  have : LocallyOfFiniteType (C₂ ↘ Spec (CommRingCat.of k₂)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hc₂ hft₁
  have : QuasiCompact (C₂ ↘ Spec (CommRingCat.of k₂)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hc₂ hqc₁
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k₁ k₂))) :=
    ⟨Function.surjective_to_subsingleton _⟩
  have : Surjective c₂ :=
    MorphismProperty.of_isPullback (P := @Surjective) hc₂.flip inferInstance
  have : LocallyOfFiniteType c₂ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hc₂.flip inferInstance
  have : QuasiCompact c₂ :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hc₂.flip inferInstance
  obtain ⟨s₂, hs₂⟩ := finite_point_lift c₂ s₁
  obtain ⟨t₂, ht₂⟩ := finite_point_lift c₂ t₁
  let R₂ := constantFieldRestrictionOfSquare (l := l) hc₂ r hcard
  have hpoint₂ : HasPointwisePowerTransport R₂ c₂ :=
    hasPointwisePowerTransport_constantFieldRestrictionOfSquare hc₂ r hcard
  let : Algebra k₀ k₂ := ((algebraMap k₁ k₂).comp (algebraMap k₀ k₁)).toAlgebra
  refine ⟨k₂, hk₂, hfin₂, inferInstance, hl₂, d, C₂, hover₂, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    R₁ ⋙ R₂, inferInstance, inferInstance, n, S, v, c₂ ≫ c₁, hd, ?_, ?_, hS, ?_, ?_⟩
  · intro F hF
    exact isLisse_constantFieldRestriction
      (Scheme.Hom.geometricFiberBaseChangeIso hc₂) r
      (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hc₂ r hcard)
      (hlisse₁ F hF)
  · intro F ι hF
    exact hpoint₂.isReal (hpoint₁.isReal hF)
  · rw [Category.assoc, hc₁, ← Category.assoc, hc₂.w, Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl
  · obtain ⟨a₁, e₁, ha₁, he₁, hq₁, hF₁⟩ := hpoint₁ s₁
    obtain ⟨b₁, f₁, hb₁, hf₁, hq'₁, hF'₁⟩ := hpoint₁ t₁
    have hax : a₁ = x := Subtype.ext (ha₁.symm.trans hs₁)
    have hby : b₁ = y := Subtype.ext (hb₁.symm.trans ht₁)
    subst a₁
    subst b₁
    obtain ⟨a₂, e₂, ha₂, he₂, hq₂, hF₂⟩ := hpoint₂ s₂
    obtain ⟨b₂, f₂, hb₂, hf₂, hq'₂, hF'₂⟩ := hpoint₂ t₂
    have has : a₂ = s₁ := Subtype.ext (ha₂.symm.trans hs₂)
    have hbt : b₂ = t₁ := Subtype.ext (hb₂.symm.trans ht₂)
    subst a₂
    subst b₂
    refine ⟨s₂, t₂, e₁ * e₂, f₁ * f₂, Nat.mul_pos he₁ he₂, Nat.mul_pos hf₁ hf₂,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Scheme.Hom.comp_apply, hs₂] using hs₁
    · simpa only [Scheme.Hom.comp_apply, ht₂] using ht₁
    · rw [hq₂, hq₁, pow_mul]
    · rw [hq'₂, hq'₁, pow_mul]
    · calc
        ((R₂.obj (R₁.obj V)).stalk s₂).frobeniusEnd.charpoly =
            (((R₁.obj V).stalk s₁).frobeniusEnd ^ e₂).charpoly := by
          simpa only [FrobeniusModule.powFrobenius_frobeniusEnd] using
            (hF₂ (R₁.obj V)).some.charpoly_frobeniusEnd
        _ = ((V.stalk x).frobeniusEnd ^ (e₁ * e₂)).charpoly := by
          simpa only [FrobeniusModule.powFrobenius_frobeniusEnd, pow_mul] using
            charpoly_pow_equiv (hF₁ V).some e₂
    · calc
        ((R₂.obj (R₁.obj V)).stalk t₂).frobeniusEnd.charpoly =
            (((R₁.obj V).stalk t₁).frobeniusEnd ^ f₂).charpoly := by
          simpa only [FrobeniusModule.powFrobenius_frobeniusEnd] using
            (hF'₂ (R₁.obj V)).some.charpoly_frobeniusEnd
        _ = ((V.stalk y).frobeniusEnd ^ (f₁ * f₂)).charpoly := by
          simpa only [FrobeniusModule.powFrobenius_frobeniusEnd, pow_mul] using
            charpoly_pow_equiv (hF'₁ V).some f₂
    · intro a b
      obtain ⟨t', ht', hqt', hw⟩ := horbit t₂ a b
      refine ⟨t', ?_, hqt', hw⟩
      simpa only [Scheme.Hom.comp_apply, ht', ht₂] using ht₁

end AlgebraicGeometry.WeilSheaf
