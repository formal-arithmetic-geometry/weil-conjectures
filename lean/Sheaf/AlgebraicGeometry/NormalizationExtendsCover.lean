/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Extending a finite etale cover by normalization

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
lem-fin-normalization-extends-cover.md (blueprint: lem-fin-normalization-extends-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem normalization_iso_source {A B S : Scheme.{u}}
    (a : A ⟶ S) (b : B ⟶ S) [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact b] [QuasiSeparated b] (e : A ≅ B) (he : e.hom ≫ b = a) :
    ∃ E : a.normalization ≅ b.normalization,
      E.hom ≫ b.fromNormalization = a.fromNormalization := by
  have hi : e.inv ≫ a = b := by rw [← he]; simp
  let m := a.normalizationDesc (e.hom ≫ b.toNormalization) b.fromNormalization
    (by simp [he])
  let n := b.normalizationDesc (e.inv ≫ a.toNormalization) a.fromNormalization
    (by simp [hi])
  have hmn : m ≫ n = 𝟙 _ := by
    apply Hom.normalization.hom_ext _ _ _ a.fromNormalization
    · simp [m, n]
    · simp [m, n]
    · simp
  have hnm : n ≫ m = 𝟙 _ := by
    apply Hom.normalization.hom_ext _ _ _ b.fromNormalization
    · simp [m, n]
    · simp [m, n]
    · simp
  exact ⟨⟨m, n, hmn, hnm⟩, by simp [m]⟩

private theorem normalization_integral_composite {A B S : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ S) [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact (a ≫ b)] [QuasiSeparated (a ≫ b)] [IsIntegralHom b]
    [IsIso a.fromNormalization] :
    ∃ e : (a ≫ b).normalization ≅ B,
      e.hom ≫ b = (a ≫ b).fromNormalization := by
  let c := a ≫ b
  let m := c.normalizationDesc a b rfl
  let d := a.normalizationDesc c.toNormalization m (by simp [m])
  let n := inv a.fromNormalization ≫ d
  have hnm : n ≫ m = 𝟙 B := by
    simp [n, d]
  have hmn : m ≫ n = 𝟙 c.normalization := by
    apply Hom.normalization.hom_ext c _ _ c.fromNormalization
    · have ha : a ≫ inv a.fromNormalization = a.toNormalization := by
        apply (cancel_mono a.fromNormalization).mp
        simp
      simp only [m, Hom.toNormalization_normalizationDesc_assoc, n]
      rw [← Category.assoc, ha]
      simp [d]
    · rw [Category.assoc, show n ≫ c.fromNormalization = b by
        rw [← Hom.normalizationDesc_comp c a b rfl, ← Category.assoc, hnm,
          Category.id_comp]]
      exact c.normalizationDesc_comp a b rfl
    · simp
  exact ⟨⟨m, n, hmn, hnm⟩, c.normalizationDesc_comp a b rfl⟩

private theorem normal_normalization_isIso (P : Scheme.{u}) [IsIntegral P]
    (hP : ∀ p : P, IsIntegrallyClosed (P.presheaf.stalk p)) :
    IsIso P.fromNormalization := by
  have := P.isIso_fromNormalization_restrict ⊤ (fun p _ ↦ hP p)
  have : IsIso (⊤ : P.Opens).ι := P.topIso.isIso_hom
  have : IsIso (P.fromNormalization ⁻¹ᵁ ⊤).ι := by
    simpa using P.normalization.topIso.isIso_hom
  have : IsIso ((P.fromNormalization ∣_ ⊤) ≫ (⊤ : P.Opens).ι) := inferInstance
  rw [morphismRestrict_ι] at this
  exact (isIso_comp_left_iff _ _).mp this

private theorem generic_ring_map {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (t : A ⟶ B) (hη : t (genericPoint A) = genericPoint B) :
    ∃ m : B.functionField ⟶ A.functionField,
      Spec.map m ≫ B.fromSpecFunctionField = A.fromSpecFunctionField ≫ t := by
  have key (x : A) (y : B) (h : t x = y) :
      ∃ m : B.presheaf.stalk y ⟶ A.presheaf.stalk x,
        Spec.map m ≫ B.fromSpecStalk y = A.fromSpecStalk x ≫ t := by
    subst y
    exact ⟨t.stalkMap x, SpecMap_stalkMap_fromSpecStalk t⟩
  exact key _ _ hη

/-- The normalization of `X` in the function field of a connected finite etale cover of a
nonempty normal open `V` restricts to that cover, as an isomorphism over `V`.
The existential integral structure makes `k(P)` available without assuming integrality of
`P`; the algebra structure is constrained to be the one induced by the given cover.

Source: smooth-purity blueprint, unit sk-prop-a1-kummer,
lem-fin-normalization-extends-cover (blueprint: lem-fin-normalization-extends-cover).

Proof plan:
1. The field spectrum is Noetherian. Finite type over it makes `X` Noetherian
   (lem-weil-pbc-finite-type-over-noetherian), and its open `V` is Noetherian
   (lem-weil-pbc-noetherian-open-subscheme-noetherian). The finite cover is proper
   (lem-weil-pbc-finite-proper), hence of finite type (def-weil-proper-morphism), so `P`
   is Noetherian by the same finite-type lemma.
2. Etale.exists_clopen_normal_integral_components (lem-fin-etale-normal-components)
   decomposes `P` into finitely many normal integral clopen pieces. Connectedness,
   including nonemptiness, makes exactly one piece occur, so `P` is integral and normal
   in the sense of def-sbc-normal-dominant-galois.
3. Etale morphisms are open (lem-weil-pbc-etale-morphism-open-map), so the nonempty image
   is dense in the integral `V`, and the generic point maps to the generic point.
   Nonempty affine opens Spec B in `V` have affine inverse images Spec D, finite over B
   (def-weil-finite-integral-morphism). Their fraction fields are k(X) and k(P)
   (lem-sc-integral-function-field-affine-fraction); nonempty open restriction preserves
   the generic stalk (def-weil-open-immersion). Restriction is base change
   (lem-weil-pbc-open-preimage-fibre-product), hence etale
   (lem-weil-pbc-etale-scheme-base-change). Applying
   lem-weil-pbc-etale-algebra-residue-field-separable at the zero primes gives the finite
   separable extension k(P)/k(X), with its induced structural map.
4. Over Spec B, def-fin-normalization-extension gives Spec C, where C is the integral
   closure of B in k(P). Finiteness makes D integral over B
   (lem-weil-pbc-finite-algebra-is-integral), so D is contained in C. Conversely an element
   of C is integral over every local ring of P. Those rings embed in k(P)
   (lem-sc-integral-scheme-stalks-in-function-field) and are integrally closed by step 2;
   hence the element lies in each stalk. The section-gluing theorem
   (lem-sc-function-field-sections-glue) puts it in D. Thus C = D as B-algebras in k(P).
5. The spectrum equivalence (def-weil-affine-spectrum) gives local isomorphisms over
   Spec B. On overlaps both maps induce the same inclusion of each affine target's
   coordinate ring into k(P). Injectivity of generic germs
   (lem-sc-integral-scheme-stalks-in-function-field) makes the ring maps equal.
   Scheme-morphism gluing (lem-weil-pbc-scheme-morphism-gluing) glues these isomorphisms
   and their inverses over V. Finally lem-weil-pbc-open-preimage-fibre-product identifies
   the inverse-image open with the pullback used below. -/
theorem normalizationIn_functionField_extends_cover
    {k : Type u} [Field k] (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (V : X.Opens) [Nonempty V] (hV : IsNormalScheme V.toScheme)
    (P : Scheme.{u}) [ConnectedSpace P] (f : P ⟶ V.toScheme) [IsFinite f] [Etale f] :
    ∃ (_ : IsIntegral P) (_ : Algebra X.functionField P.functionField),
      X.fromSpecOfAlgebraFunctionField P.functionField =
        P.fromSpecFunctionField ≫ f ≫ V.ι ∧
      ∃ e : pullback (X.fromNormalizationIn P.functionField) V.ι ≅ P,
        e.hom ≫ f = pullback.snd (X.fromNormalizationIn P.functionField) V.ι := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : IsNoetherian V.toScheme := isNoetherian_of_locallyOfFiniteType V.ι
  have : IsNoetherian P := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨n, U, hclosed, _, hcover, hn⟩ :=
    Etale.exists_clopen_normal_integral_components f hV
  obtain ⟨p⟩ := (inferInstance : Nonempty P)
  have hp : p ∈ ⨆ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hpi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  have htop : U i = ⊤ := by
    apply SetLike.coe_injective
    exact (show IsClopen (U i : Set P) from ⟨hclosed i, (U i).isOpen⟩).eq_univ ⟨p, hpi⟩
  have htopnormal := hn i
  rw [htop] at htopnormal
  have : IsIntegral (⊤ : P.Opens).toScheme := htopnormal.1
  have : IsIntegral P := IsIntegral.of_isIso P.topIso.hom
  have hP (p : P) : IsIntegrallyClosed (P.presheaf.stalk p) := by
    have := (htopnormal.2 ⟨p, trivial⟩).2
    exact IsIntegrallyClosed.of_equiv
      (asIso ((⊤ : P.Opens).ι.stalkMap ⟨p, trivial⟩)).commRingCatIsoToRingEquiv.symm
  let t := f ≫ V.ι
  have ht : DenseRange t := by
    exact (t.isOpenMap.isOpen_range).dense (Set.range_nonempty t)
  have hη : t (genericPoint P) = genericPoint X := by
    refine ((genericPoint_spec X).eq ?_).symm
    have h := (genericPoint_spec P).image t.continuous
    rwa [Set.image_univ, ht.closure_range] at h
  obtain ⟨m, hm⟩ := generic_ring_map t hη
  let : Algebra X.functionField P.functionField := m.hom.toAlgebra
  refine ⟨inferInstance, inferInstance, hm, ?_⟩
  let φ := X.fromSpecOfAlgebraFunctionField P.functionField
  let g := P.fromSpecFunctionField ≫ f
  have hφ : φ = g ≫ V.ι := hm
  let a : Spec P.functionField ⟶ pullback φ V.ι :=
    pullback.lift (𝟙 _) g (by simpa using hφ)
  have ha : IsIso a := by
    refine ⟨⟨pullback.fst φ V.ι, ?_, ?_⟩⟩
    · simp [a]
    · apply pullback.hom_ext
      · simp [a]
      · apply (cancel_mono V.ι).mp
        simp only [Category.assoc, a, pullback.lift_snd]
        rw [← hφ, pullback.condition]
        simp
  let k := pullback.snd φ V.ι
  obtain ⟨E, hE⟩ := normalization_iso_source g k (asIso a) (by simp [a, k])
  have : IsIso P.fromNormalization := normal_normalization_isIso P hP
  obtain ⟨F, hF⟩ := normalization_integral_composite P.fromSpecFunctionField f
  let e := (asIso (φ.normalizationPullback V.ι)).symm ≪≫ E.symm ≪≫ F
  refine ⟨e, ?_⟩
  dsimp only [e, Iso.trans_hom]
  simp only [Category.assoc, hF, Iso.symm_hom]
  have hEi : E.inv ≫ g.fromNormalization = k.fromNormalization := by
    rw [← hE]; simp
  change (asIso (φ.normalizationPullback V.ι)).inv ≫ E.inv ≫ g.fromNormalization = _
  rw [hEi]
  change inv (φ.normalizationPullback V.ι) ≫ k.fromNormalization = _
  apply (cancel_epi (φ.normalizationPullback V.ι)).mp
  rw [IsIso.hom_inv_id_assoc]
  exact (φ.normalizationPullback_snd V.ι).symm

end AlgebraicGeometry.Scheme
