/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.CoefficientHeart
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.CohomologicalDimension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Sheaf.Paper.UniformConstructibleExtRational
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# A uniform Ext bound for rational constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-uniform-constructible-ext,
_section.md and sk-lem-uniform-constructible-ext.proof.md
(blueprint: sk-lem-uniform-constructible-ext).

Ext is formed in the ambient abelian category of all module objects over the pulled-back
condensed ring, hence in its ordinary unbounded derived category. The second conjunct
retains the explicit bound for an open immersion followed by a closed immersion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem ext_zero_left {A : Type*} [Category A] [Abelian A] [HasExt A]
    {C : A} (hC : IsZero C) (N : A) (q : ℕ) : Subsingleton (Abelian.Ext C N q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hid : 𝟙 C = 0 := hC.eq_of_src _ _
  rw [← Abelian.Ext.mk₀_id_comp x, hid, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp]

private theorem ext_zero_right {A : Type*} [Category A] [Abelian A] [HasExt A]
    (C : A) {N : A} (hN : IsZero N) (q : ℕ) : Subsingleton (Abelian.Ext C N q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hid : 𝟙 N = 0 := hN.eq_of_src _ _
  rw [← Abelian.Ext.comp_mk₀_id x, hid, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

private theorem ext_iso_left {A : Type*} [Category A] [Abelian A] [HasExt A]
    {C C' : A} (e : C ≅ C') (N : A) (q : ℕ)
    [Subsingleton (Abelian.Ext C N q)] : Subsingleton (Abelian.Ext C' N q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hx : (Abelian.Ext.mk₀ e.hom).comp x (zero_add q) = 0 := Subsingleton.elim _ _
  have := congrArg (fun y ↦ (Abelian.Ext.mk₀ e.inv).comp y (zero_add q)) hx
  simpa using this

private theorem ext_iso_right {A : Type*} [Category A] [Abelian A] [HasExt A]
    (C : A) {N N' : A} (e : N ≅ N') (q : ℕ)
    [Subsingleton (Abelian.Ext C N q)] : Subsingleton (Abelian.Ext C N' q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hx : x.comp (Abelian.Ext.mk₀ e.inv) (add_zero q) = 0 := Subsingleton.elim _ _
  have := congrArg (fun y ↦ y.comp (Abelian.Ext.mk₀ e.hom) (add_zero q)) hx
  simpa using this

private theorem ext_shortExact_left {A : Type*} [Category A] [Abelian A] [HasExt A]
    {S : ShortComplex A} (hS : S.ShortExact) (N : A) (q : ℕ)
    [Subsingleton (Abelian.Ext S.X₁ N q)] [Subsingleton (Abelian.Ext S.X₃ N q)] :
    Subsingleton (Abelian.Ext S.X₂ N q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₂ hS N x
    (Subsingleton.elim _ _)
  rw [← hy, Subsingleton.elim y 0, Abelian.Ext.comp_zero]

private theorem ext_shortExact_right {A : Type*} [Category A] [Abelian A] [HasExt A]
    (C : A) {S : ShortComplex A} (hS : S.ShortExact) (q : ℕ)
    [Subsingleton (Abelian.Ext C S.X₁ q)] [Subsingleton (Abelian.Ext C S.X₃ q)] :
    Subsingleton (Abelian.Ext C S.X₂ q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₂ C hS x
    (Subsingleton.elim _ _)
  rw [← hy, Subsingleton.elim y 0, Abelian.Ext.zero_comp]

private theorem property_of_filtration {A : Type*} [Category A] [Abelian A]
    (P : A → Prop) (hzero : ∀ C, IsZero C → P C)
    (hiso : ∀ (C : A) (D : A), (C ≅ D) → P C → P D)
    (hext : ∀ {S : ShortComplex A}, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {C : A} {m : ℕ} (T : Fin (m + 1) → Subobject C)
    (hbot : T 0 = ⊥) (htop : T (Fin.last m) = ⊤)
    (h : ∀ a : Fin m, T a.castSucc ≤ T a.succ)
    (hquot : ∀ a : Fin m, P (cokernel (Subobject.ofLE _ _ (h a)))) : P C := by
  have hsteps : ∀ a : Fin (m + 1), P (T a : A) := by
    intro a
    induction a using Fin.induction with
    | zero =>
        rw [hbot]
        exact hzero _ ((isZero_zero A).of_iso Subobject.botCoeIsoZero)
    | succ a ih =>
        exact hext (S := ShortComplex.mk _ _ (cokernel.condition _))
          { exact := ShortComplex.exact_cokernel _ } ih (hquot a)
  have hend := hsteps (Fin.last m)
  rw [htop] at hend
  exact hiso _ _ (asIso (⊤ : Subobject C).arrow) hend


private theorem base_field_cd_finite
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k]
    (hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k)) :
    cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤ := by
  rcases hk with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : Finite k := Finite.of_injective e e.injective
    exact lt_of_le_of_lt ((cohomologicalDimension_baseField ℓ Fact.out k).2 inferInstance)
      (by simp)
  · have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    have : IsAlgClosed k := IsAlgClosed.of_ringEquiv D.k k e.symm
    rw [(cohomologicalDimension_baseField ℓ Fact.out k).1 inferInstance]
    simp

private theorem immersion_cd_finite
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hk : cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤)
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    {S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S < ⊤ := by
  let : S.Over (Spec (.of k)) := ⟨a ≫ X ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (S ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (a ≫ X ↘ Spec (.of k)))
  have : QuasiCompact (S ↘ Spec (.of k)) :=
    quasiCompact_of_compactSpace _
  exact cohomologicalDimension_lt_top_of_finiteType ℓ Fact.out hk

private theorem open_relative_cd_finite
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hk : cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤)
    {X : Scheme.{u}} [IsNoetherian X] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j < ⊤ := by
  let : U.Over (Spec (.of k)) := ⟨j ≫ X ↘ Spec (.of k)⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ X ↘ Spec (.of k)))
  have : QuasiCompact (U ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (j ≫ X ↘ Spec (.of k)))
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  exact relativeCohomologicalDimension_lt_top_of_finiteType ℓ Fact.out hk j

/-- Uniform Ext bound for a single lisse locally closed stratum.
Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-uniform-constructible-ext,
stratum calculation in the rational/torsion/integral detail nodes
(blueprint: sk-lem-uniform-constructible-ext).

This is the geometric input: the rational stratum estimate, together with finite
cohomological dimension of finite type strata, converts its `WithTop ℕ` cutoff to a
natural-number cutoff. The bound is independent of the constructible target. -/
private theorem uniformLisseConstructibleExtNat
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (_hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k]
    (hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [IsNoetherian X] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (S : Scheme.{u}) (a : S ⟶ X) [IsImmersion a]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) S))
    (hL : IsLisseCoefficientModule (coefficientHeartRingObj Λ) L) :
    ∃ d : ℕ, ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ∀ q : ℕ, d < q →
        Subsingleton (Abelian.Ext
          ((coefficientHeartLocallyClosedExtension
            (coefficientHeartRingObj Λ) a inferInstance).obj L)
          N.obj q) := by
  classical
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := by
    let := Fintype.ofFinite D.k₀
    exact charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p := Algebra.charP_iff D.k₀ D.k D.p |>.mp inferInstance
  have hkchar : CharP k D.p := by
    rcases hk with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact charP_of_injective_ringHom e.symm.toRingHom.injective D.p
    · exact charP_of_injective_ringHom e.symm.toRingHom.injective D.p
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let U : X.Opens := ⟨(Set.range a.imageι)ᶜ,
    a.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hcomp : Set.range a.imageι = (Set.range U.ι)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  obtain ⟨E, f, hf, Lmodel, hmodel, e, W, d, hW, hlat, hd, hc, hrestr, hvan, hglobal⟩ :=
    uniformConstructibleExtRational k D.p ℓ _hℓ.symm Λ _hΛ X
      S a.image U a.toImage a.imageι U.ι hcomp L hL
  have hbase := base_field_cd_finite D ℓ k hk
  have hcut : ∀ r, W.cutoff r < ⊤ := by
    intro r
    have : IsImmersion (W.stratification.immersion r) := W.stratification.isImmersion r
    have : CompactSpace (W.stratification.domain r) := W.stratum_compact r
    have : QuasiSeparatedSpace (W.stratification.domain r) := W.stratum_qsep r
    have : IsOpenImmersion (W.complementMap r) := W.complement_isOpen r
    have : QuasiCompact (W.complementMap r) := W.complement_qc r
    have hc := immersion_cd_finite ℓ k hbase (W.stratification.immersion r)
    have hj := open_relative_cd_finite ℓ k hbase (W.complementMap r)
    rw [W.cutoff_eq r]
    exact WithTop.add_lt_top.mpr ⟨WithTop.add_lt_top.mpr ⟨hj, hc⟩, WithTop.coe_lt_top 2⟩
  have hdfin : d ≠ ⊤ := by
    rw [hd]
    apply ne_of_lt
    apply max_lt
    · simp
    · apply lt_top_iff_ne_top.mpr
      apply sSup_ne_top (Set.finite_range _)
      rintro ⟨r, hr⟩
      exact (ne_of_lt (hcut r.1)) hr
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hdfin
  refine ⟨n, ?_⟩
  intro N q hq
  have hqd : d < (q : WithTop ℕ) := by
    rw [← hn]
    exact WithTop.coe_lt_coe.mpr hq
  rcases coefficientHeart ℓ Λ _hΛ k D.p _hℓ.symm X with
    ⟨_, _, _, _, _, _, _, _, _, _, hfil, _⟩
  obtain ⟨m, T, hbot, htop, hle, hquot⟩ := hfil N
  apply property_of_filtration (fun B ↦ Subsingleton (Abelian.Ext
    ((coefficientHeartLocallyClosedExtension
      (coefficientHeartRingObj Λ) a inferInstance).obj L) B q))
    (fun B hB ↦ ext_zero_right _ hB q)
    (fun B C e h ↦ by have := h; exact ext_iso_right _ e q)
    (fun hS h1 h3 ↦ by have := h1; have := h3; exact ext_shortExact_right _ hS q)
    T hbot htop hle
  intro r
  obtain ⟨T', b, hb, M, hM, ⟨e⟩⟩ := hquot r
  have : IsImmersion b := hb
  have : TopologicalSpace.NoetherianSpace T' := b.isEmbedding.isInducing.noetherianSpace
  let V : X.Opens := ⟨(Set.range b.imageι)ᶜ,
    b.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hcompb : Set.range b.imageι = (Set.range V.ι)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hv := hvan T' b.image V b.toImage b.imageι V.ι hcompb M hM q hqd
  have : Subsingleton (Abelian.Ext
      ((coefficientHeartLocallyClosedExtension
        (coefficientHeartRingObj Λ) a inferInstance).obj L)
      ((coefficientHeartLocallyClosedExtension
        (coefficientHeartRingObj Λ) b hb).obj M) q) := hv
  exact ext_iso_right _ e.symm q


private theorem uniformConstructibleExt_core
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (_hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] [CharP k D.p]
    (hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ C : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ∃ d : ℕ, ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
        ∀ q : ℕ, d < q → Subsingleton (Abelian.Ext C.obj N.obj q)) := by
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have hh := coefficientHeart ℓ Λ _hΛ k D.p _hℓ.symm X
  rcases hh with ⟨_, _, _, _, _, _, _, _, _, _, hfil, _⟩
  intro C
  obtain ⟨m, T, hbot, htop, hle, hq⟩ := hfil C
  let P : (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X)) → ℕ → Prop := fun A d ↦
    ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ∀ q : ℕ, d < q → Subsingleton (Abelian.Ext A N.obj q)
  have hi : ∀ (A B : _), (A ≅ B) → ∀ {d}, P A d → P B d := by
    intro A B e d h N q hq
    have := h N q hq
    exact ext_iso_left e N.obj q
  have he : ∀ {S : ShortComplex _} (hS : S.ShortExact) {d},
      P S.X₁ d → P S.X₃ d → P S.X₂ d := by
    intro S hS d h1 h3 N q hq
    have := h1 N q hq
    have := h3 N q hq
    exact ext_shortExact_left hS N.obj q
  have hquot : ∀ a : Fin m, ∃ d, P (cokernel (Subobject.ofLE _ _ (hle a))) d := by
    intro a
    obtain ⟨S, j, hj, L, hL, ⟨e⟩⟩ := hq a
    have : IsImmersion j := hj
    obtain ⟨d, hd⟩ := uniformLisseConstructibleExtNat D ℓ _hℓ Λ _hΛ k hk X S j L hL
    refine ⟨d, ?_⟩
    intro N q hq'
    have := hd N q hq'
    exact ext_iso_left e.symm N.obj q
  classical
  choose d hd using hquot
  let b := Finset.univ.sup d
  refine ⟨b, property_of_filtration (fun A ↦ P A b) ?_ ?_ ?_ T hbot htop hle ?_⟩
  · intro A hA N q hq
    exact ext_zero_left hA N.obj q
  · intro A B e h
    exact hi A B e h
  · intro S hS h1 h3
    exact he hS h1 h3
  · intro a N q hq
    exact hd a N q (lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ a)) hq)

/-- The existence clause of the uniform constructible Ext bound, independently of the
unrefined explicit cutoff in its second clause.

Source: blueprint main-20261015, sk-lem-uniform-constructible-ext, opening paragraph;
the repaired det-uniform-constructible-ext-rational, refined source cutoff
(blueprint: sk-lem-uniform-constructible-ext).

Proof: for each locally closed lisse source, use the rational estimate with its fixed
finite refinement. The base field is finite or algebraically closed, so its torsion
cohomological dimension is finite. Each refined stratum and complementary open has finite
cohomological dimension by the finite-type bounds. The finite maximum is therefore a
natural number. Covariant Ext exactness along a target filtration preserves that bound.
Now fix a source filtration and take the maximum of its finitely many natural bounds.
Contravariant Ext exactness proves the bound for the source, for all targets at once.
The empty source filtration has bound zero. No global integral lattice is assumed. -/
theorem uniformConstructibleExt_exists
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (_hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k]
    (_hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ C : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ∃ d : ℕ, ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
        ∀ q : ℕ, d < q → Subsingleton (Abelian.Ext C.obj N.obj q)) := by
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := by
    let := Fintype.ofFinite D.k₀
    exact charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p := Algebra.charP_iff D.k₀ D.k D.p |>.mp inferInstance
  rcases _hk with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : CharP k D.p := charP_of_injective_ringHom e.symm.toRingHom.injective D.p
    exact uniformConstructibleExt_core D ℓ _hℓ Λ _hΛ k (Or.inl ⟨e⟩) X
  · have : CharP k D.p := charP_of_injective_ringHom e.symm.toRingHom.injective D.p
    exact uniformConstructibleExt_core D ℓ _hℓ Λ _hΛ k (Or.inr ⟨e⟩) X

/-- The displayed open-closed cutoff is a natural number in the standing finite-field
setting. This proves its finiteness without asserting Ext vanishing at that cutoff.
Source: blueprint main-20261015, sk-lem-uniform-constructible-ext, proof opening paragraph
(blueprint: sk-lem-uniform-constructible-ext).

Proof: the base field has finite cohomological dimension by the finite/algebraically
closed alternatives. The composite immersion makes S finite type over it. The finite-type
absolute and relative dimension bounds apply to S and j. Their sum with two is finite in
`WithTop ℕ`, hence is the coercion of a natural number. Empty S and empty U are allowed. -/
theorem uniformConstructibleExt_cutoff
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k]
    (hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (S Z U : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j] :
    ∃ d : ℕ, (d : WithTop ℕ) =
      relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j +
        cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S + 2 := by
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have hbase := base_field_cd_finite D ℓ k hk
  have hS := immersion_cd_finite ℓ k hbase (v ≫ i)
  have hj := open_relative_cd_finite ℓ k hbase j
  apply WithTop.ne_top_iff_exists.mp
  exact ne_of_lt (WithTop.add_lt_top.mpr
    ⟨WithTop.add_lt_top.mpr ⟨hj, hS⟩, WithTop.coe_lt_top 2⟩)

/-- Every rational constructible sheaf has a bound on Ext uniform in all constructible
second arguments. For `a = i ∘ v`, the bound is exactly `cd_ℓ(j) + cd_ℓ(S) + 2`.
The base field is the fixed finite field or its algebraic closure, expressed invariantly
by a field isomorphism. Natural-number degrees and bounds encode the nonnegative-integer
convention: a degree strictly above such a bound is necessarily nonnegative.
The qcqs instances in the stratum clause only supply the domains of `sk-def-cd`; they
hold for every locally closed stratum and complementary open of the standing scheme.

Source: blueprint sk-lem-uniform-constructible-ext, statement and its four-step DAG proof
(blueprint: sk-lem-uniform-constructible-ext).

Proof plan:
1. The global finite-field datum and sk-def-sf-setting put X in sk-def-sfb-dc-setting.
By sk-lem-base-field-cd the base has finite ell-cohomological dimension. The finite-type
bounds of sk-def-cd make cd_ell(S) and cd_ell(j) finite. Empty strata cause no exception.
2. Apply det-uniform-constructible-ext-rational to a lisse L on S and every locally
closed b:T -> X and lisse M on T. Its bound is independent of b and M. The torsion
estimate det-uniform-constructible-ext-torsion has cutoff cd_ell(j)+cd_ell(S)+1;
det-uniform-constructible-ext-integral adds one for the derived inverse limit of the
reductions modulo powers of the uniformizer. The support fibre formula of
sk-lem-formal-closed-support and its limit compatibility in sk-lem-formal-closed-support-ii
are the support and inverse-limit constructions used there. The rational stratum lemma
includes passage to E and Qbar_l; it does not assume a global integral lattice in L.
3. Filter an arbitrary constructible N by sk-lem-coefficient-heart(3). Induct along
its exact subobject filtration. The exact segment from lem-sc-abelian-ext-covariant-exact
has outer terms Ext^q(a_!L,N_previous) and Ext^q(a_!L,b_!M), both zero above the same
cutoff. Its middle term vanishes, with no dependence on the target filtration length.
4. Fix the finite source filtration of C from sk-lem-coefficient-heart(3). Take the
maximum of zero and the finitely many stratum cutoffs. Induct along this filtration,
using lem-coef-ext-contravariant-six-term: Ext^q(a_!L,N) -> Ext^q(C_step,N) ->
Ext^q(C_previous,N) has zero outer terms. This gives the first conjunct for every N
simultaneously. The empty filtration gives d_0=0. For a single stratum apply step 3
directly to obtain the second conjunct. The two extra degrees are the closed-support
cone degree and the derived inverse-limit degree, respectively. -/
-- STATEMENT-DISPUTED: the explicit unrefined cutoff is not supplied by the repaired
-- rational stratum lemma, which retains it only with a global source-model lattice.
theorem uniformConstructibleExt
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (_hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k]
    (_hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ C : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ∃ d : ℕ, ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
        ∀ q : ℕ, d < q → Subsingleton (Abelian.Ext C.obj N.obj q)) ∧
    (∀ (S Z U : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : U ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
      [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j],
      Set.range i.base = (Set.range j.base)ᶜ →
      ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) S),
        IsLisseCoefficientModule (coefficientHeartRingObj Λ) L →
        ∃ d : ℕ,
          (d : WithTop ℕ) = relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j +
            cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S + 2 ∧
          ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
            ∀ q : ℕ, d < q →
              Subsingleton (Abelian.Ext
                ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i).obj
                  ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj Λ) v).obj L))
                N.obj q)) := by
  sorry

end AlgebraicGeometry.ProEtale
