module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.RingTheory.Depth
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import WeilConjectures.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.DepthQuotientNonzerodivisor
import WeilConjectures.RingTheory.DepthLeSupportDimension

/-! # Cohen-Macaulay stalks of local complete intersections over a field

Source: Stacks Project, Algebra, Tag 00SB (`lemma-lci-CM`), applied on affine charts.
(blueprint: lem-sfb-lci-cohen-macaulay-stalks).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem depth_le_of_ringEquiv {A B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A ≤ IsLocalRing.depth (R := B) B := by
  classical
  have hm (C : Type u) [CommRing C] [IsLocalRing C] :
      IsLocalRing.maximalIdeal C • (⊤ : Submodule C C) ≠ ⊤ := by
    rw [Ideal.smul_top_eq_map]
    change (IsLocalRing.maximalIdeal C).map (algebraMap C C) ≠ ⊤
    simpa only [Algebra.algebraMap_self, Ideal.map_id] using
      (IsLocalRing.maximalIdeal.isMaximal C).ne_top
  simp only [IsLocalRing.depth, Ideal.depth, hm, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hmem a ha)

private theorem depth_eq_of_ringEquiv {A B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A = IsLocalRing.depth (R := B) B :=
  le_antisymm (depth_le_of_ringEquiv e) (depth_le_of_ringEquiv e.symm)

private theorem cm_of_ringEquiv {A B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (h : (IsLocalRing.depth (R := A) A : WithBot ℕ∞) = ringKrullDim A) :
    (IsLocalRing.depth (R := B) B : WithBot ℕ∞) = ringKrullDim B := by
  rw [← depth_eq_of_ringEquiv e, ← ringKrullDim_eq_of_ringEquiv e]
  exact h

private theorem regular_local_cm (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    (IsLocalRing.depth (R := A) A : WithBot ℕ∞) = ringKrullDim A := by
  classical
  let d := (IsLocalRing.maximalIdeal A).spanFinrank
  have hd : ringKrullDim A = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  obtain ⟨s, hslen, hsspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (p := (IsLocalRing.maximalIdeal A : Submodule A A))
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  let rs := s.toList
  have hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A := by
    simpa [Ideal.ofList, rs] using hsspan
  have hlen : rs.length = d := by simpa [rs, d] using hslen
  have hrs : IsLocalRing.IsRegularSystemOfParameters rs :=
    ⟨hspan, by rw [hlen, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators A d hd rs hrs).1
  have hge : (d : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by
    unfold IsLocalRing.depth Ideal.depth
    split_ifs
    · exact le_top
    · apply le_sSup
      refine ⟨rs, hreg, ?_, ?_⟩
      · intro x hx
        rw [← hspan]
        exact Ideal.subset_span hx
      · rw [hlen]
  apply le_antisymm
  · simpa only [Module.supportDim_self_eq_ringKrullDim] using
      IsLocalRing.depth_le_supportDim (R := A) A
  · rw [hd]
    exact WithBot.coe_le_coe.mpr hge

private theorem quotient_regular_cm (n : ℕ) (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    (hcm : (IsLocalRing.depth (R := A) A : WithBot ℕ∞) = ringKrullDim A)
    (rs : List A) (hlen : rs.length = n) (hreg : RingTheory.Sequence.IsRegular A rs)
    (B : Type u) [CommRing B] [IsLocalRing B] (e : A ⧸ Ideal.ofList rs ≃+* B) :
    (IsLocalRing.depth (R := B) B : WithBot ℕ∞) = ringKrullDim B := by
  classical
  induction n generalizing A B with
  | zero =>
    have hrs : rs = [] := List.length_eq_zero_iff.mp hlen
    subst rs
    have e' : A ≃+* A ⧸ Ideal.ofList ([] : List A) := by
      exact (RingEquiv.quotientBot A).symm.trans
        (Ideal.quotEquivOfEq (Ideal.ofList_nil (R := A)).symm)
    exact cm_of_ringEquiv (e'.trans e) hcm
  | succ n ih =>
    cases rs with
    | nil => simp at hlen
    | cons x xs =>
      have hx : x ∈ IsLocalRing.maximalIdeal A := by
        change ¬ IsUnit x
        intro hunit
        apply hreg.2
        simp [Ideal.ofList_cons, Ideal.span_singleton_eq_top.mpr hunit]
      have hsplit := (RingTheory.Sequence.isRegular_cons_iff' A x xs).mp hreg
      have hxreg : x ∈ nonZeroDivisors A := by
        apply mem_nonZeroDivisors_iff.mpr
        constructor
        · intro a ha
          exact hsplit.1 (by simpa using ha)
        · intro a ha
          exact hsplit.1 (by simpa [mul_comm] using ha)
      obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := A))
      have hatop : a ≠ ⊤ := by
        intro h
        exact ringKrullDim_ne_top (R := A) (ha.symm.trans (by simp [h]))
      obtain ⟨d, hd'⟩ := ENat.ne_top_iff_exists.mp hatop
      have hd : ringKrullDim A = (d : WithBot ℕ∞) := by
        simpa only [WithBot.coe_natCast] using ha.symm.trans
          (congrArg (fun b : ℕ∞ ↦ (b : WithBot ℕ∞)) hd'.symm)
      have hdepth : (d : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by
        apply WithBot.coe_le_coe.mp
        exact (hcm.trans hd).ge
      obtain ⟨hQ, hnoeth, hdim, hmax, hdepthQ, _⟩ :=
        IsLocalRing.depth_quotient_nonzerodivisor A d hd hdepth x hx hxreg
      let := hQ
      let : DistribMulAction A (Submodule A A) := Submodule.pointwiseDistribMulAction
      let Q := A ⧸ Ideal.span {x}
      have heq : x • (⊤ : Submodule A A) = Ideal.span {x} := by
        rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]
        simp
      have htail : RingTheory.Sequence.IsRegular Q
          (xs.map (Ideal.Quotient.mk (Ideal.span {x}))) := by
        let e' : QuotSMulTop x A ≃ₗ[A] Q := Submodule.quotEquivOfEq _ _ heq
        have hsmul (a : Q) (b : QuotSMulTop x A) : e' (a • b) = a • e' b := by
          induction a using Quotient.inductionOn with
          | h a =>
            change e' (a • b) = a • e' b
            exact e'.map_smul a b
        apply (e'.toAddEquiv.isRegular_congr ?_).mp hsplit.2
        exact List.forall₂_same.mpr (fun a _ b ↦ hsmul a b)
      have hcmQ : (IsLocalRing.depth (R := Q) Q : WithBot ℕ∞) = ringKrullDim Q := by
        apply le_antisymm
        · simpa only [Module.supportDim_self_eq_ringKrullDim] using
            IsLocalRing.depth_le_supportDim (R := Q) Q
        · rw [hdim]
          exact WithBot.coe_le_coe.mpr hdepthQ
      let eQ : Q ⧸ Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x}))) ≃+*
          A ⧸ Ideal.ofList (x :: xs) := by
        rw [← Ideal.map_ofList, Ideal.ofList_cons]
        exact DoubleQuot.quotQuotEquivQuotSup (Ideal.span {x}) (Ideal.ofList xs)
      exact ih Q hcmQ _ (by simpa using hlen) htail B (eQ.trans e)

private theorem global_lci_cm (k T : Type u) [Field k] [CommRing T] [Algebra k T]
    [IsNoetherianRing T] [Nontrivial T] (h : Algebra.IsGlobalCompleteIntersection k T)
    (q : Ideal T) [q.IsPrime] :
    (IsLocalRing.depth (R := Localization.AtPrime q) (Localization.AtPrime q) :
      WithBot ℕ∞) = ringKrullDim (Localization.AtPrime q) := by
  classical
  rcases h with hzero | ⟨n, c, fs, hcn, ⟨e⟩, hdim⟩
  · exact False.elim (not_subsingleton T hzero)
  let P := MvPolynomial (Fin n) k
  let J : Ideal P := Ideal.span (Set.range fs)
  let q' : Ideal (P ⧸ J) := q.comap e.toRingHom
  let r : Ideal P := q'.comap (Ideal.Quotient.mk J)
  have : q'.IsPrime := Ideal.IsPrime.comap _
  have : r.IsPrime := Ideal.IsPrime.comap _
  let R := Localization.AtPrime r
  have hJr : J ≤ r := by
    intro a ha
    change e (Ideal.Quotient.mk J a) ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    exact q.zero_mem
  have hJR : J.map (algebraMap P R) ≤ IsLocalRing.maximalIdeal R := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R r a).mpr (hJr ha)
  let B := R ⧸ J.map (algebraMap P R)
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJR)
  let : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hloc : IsLocalization.AtPrime B q' := by
    have heq : Algebra.algebraMapSubmonoid (P ⧸ J) r.primeCompl = q'.primeCompl :=
      q'.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    change IsLocalization q'.primeCompl B
    rw [← heq]
    infer_instance
  let := hloc
  have heq : q'.primeCompl.map e.toRingEquiv.toMonoidHom = q.primeCompl :=
    e.toRingEquiv.map_primeCompl_comap_eq q
  let eB : B ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv q'.primeCompl B (Localization.AtPrime q')).toRingEquiv.trans
      (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q')
        (Localization.AtPrime q) e.toRingEquiv
        heq)
  have : Nontrivial (P ⧸ J) := e.toRingEquiv.nontrivial
  have hdim' : topologicalKrullDim (Spec (CommRingCat.of (P ⧸ J))) +
      (c : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum (P ⧸ J)) + _ = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hdim
    rw [hdim, ← Nat.cast_add, Nat.sub_add_cancel hcn]
  have hreg := MvPolynomial.isRegular_localizationAtPrime_of_quotient_dimension
    k n c fs hdim' r hJr
  have hlist : Ideal.ofList ((List.ofFn fs).map (algebraMap P R)) =
      J.map (algebraMap P R) := by
    rw [← Ideal.map_ofList]
    congr 1
    change Ideal.span _ = Ideal.span _
    congr 1
    ext a
    simp
  let eQ : R ⧸ Ideal.ofList ((List.ofFn fs).map (algebraMap P R)) ≃+* B :=
    Ideal.quotEquivOfEq hlist
  exact quotient_regular_cm _ R (regular_local_cm R) _ rfl hreg _ (eQ.trans eB)

/-- Every stalk of a scheme locally of finite type over a field, with an affine cover
by local-complete-intersection coordinate algebras, is Noetherian and has depth equal
to its Krull dimension. The point need not be closed.

Source: Stacks Project, Algebra, Tag 00SB (`lemma-lci-CM`), with Tags 00SC and 02JN.
(blueprint: lem-sfb-lci-cohen-macaulay-stalks).

Proof plan, following the six steps of the node:
1. Fix any point x and choose a covering chart Spec S containing x. The affine-open
   stalk localization lemma identifies its stalk with S localized at the corresponding
   prime p. The local-complete-intersection definition gives g outside p such that
   T = S[1/g] is a global complete intersection.
2. The extended prime q in T consists of fractions s/g^a with s in p. Fraction relations
   make this well-defined. The maps s/t to (s/1)/(t/1) and
   (s/g^a)/(t/g^b) to (s*g^b)/(g^a*t) identify S_p with T_q. Their denominators are
   admissible, and their composites are identities. The prime q makes T nonzero.
3. Write T as P/J, where P is a polynomial ring in n variables and J is generated by
   c equations, with dimension T = n-c. Let r be the inverse image of q in P.
   Polynomial-ring regularity makes R = P_r Noetherian regular local.
   `lem-weil-pbc-global-complete-intersection-local-regular-sequence` makes the c
   localized equations regular in R. Localization of a quotient identifies T_q
   with R modulo these equations.
4. If d is the dimension of R, its maximal ideal has d generators. By
   `lem-weil-pbc-regular-local-generators-regular-sequence` they are a regular sequence.
   The definition of depth then gives depth R at least d, at this arbitrary prime r.
5. Induct through the c equations. The invariant is that each partial quotient is a
   nonzero Noetherian local ring with depth at least dimension. The base is step 4.
   Each next equation is a nonzerodivisor in the maximal ideal by regularity.
   `lem-weil-pbc-quotient-local-structure` identifies the quotient local structure;
   `lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm` preserves the invariant and
   decreases dimension by one. The iterated quotient is the quotient by the initial
   list of equations. Thus the final quotient B has depth at least dimension.
6. Apply `lem-weil-pbc-depth-le-support-dimension` to the finite nonzero B-module B.
   Its support is all of Spec B, since every prime localization is nonzero. This gives
   depth B at most dimension B and hence equality. The ring isomorphisms above preserve
   ideals and prime chains, maximal ideals, and multiplication on successive quotients.
   They preserve Noetherianity, dimension, and lengths of regular sequences, so the
   original stalk is Noetherian with the same depth-dimension equality. Since x was
   arbitrary, the conclusion holds at all points, including nonclosed points. -/
theorem isNoetherianRing_stalk_and_depth_eq_ringKrullDim_of_lci
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hlci : ∃ (I : Type u) (A : I → CommRingCat.{u})
      (aA : ∀ i, Algebra k (A i)) (ft : ∀ i, Algebra.FiniteType k (A i))
      (φ : ∀ i, Spec (A i) ⟶ X),
      (∀ i, IsOpenImmersion (φ i)) ∧
        (∀ i, φ i ≫ f =
          Spec.map (CommRingCat.ofHom (@algebraMap k (A i) _ _ (aA i)))) ∧
        (∀ z : X, ∃ i, ∃ y : Spec (A i), φ i y = z) ∧
        (∀ i, @Algebra.IsLocalCompleteIntersection k (A i) _ _ (aA i) (ft i)))
    (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) ∧
      (IsLocalRing.depth (R := X.presheaf.stalk x) (X.presheaf.stalk x) : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) := by
  classical
  obtain ⟨I, A, aA, ft, φ, hopen, _, hcover, hlci⟩ := hlci
  obtain ⟨i, y, rfl⟩ := hcover x
  let := aA i
  let := ft i
  let := hopen i
  let S := A i
  let p := y.asIdeal
  have hnoeth : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let := hnoeth
  obtain ⟨s, hs, hglobal⟩ := hlci i
  have hy : y ∈ (⨆ g ∈ s, PrimeSpectrum.basicOpen g) := by rw [hs]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hy
  obtain ⟨g, hg, hyg⟩ := hy
  have hgp : g ∉ p := hyg
  let T := Localization.Away g
  let q : Ideal T := p.map (algebraMap S T)
  have hdis : Disjoint (Submonoid.powers g : Set S) (p : Set S) :=
    (p.disjoint_powers_iff_notMem_of_isPrime g).mpr hgp
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers g) T p inferInstance hdis
  have hqp : q.comap (algebraMap S T) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) T inferInstance hdis
  have hloc : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    change IsLocalization p.primeCompl (Localization.AtPrime q)
    have heq : (q.comap (algebraMap S T)).primeCompl = p.primeCompl := by
      congr 1
    rw [← heq]
    infer_instance
  let := hloc
  let eL : Localization.AtPrime q ≃+* Localization.AtPrime p :=
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime q)
      (Localization.AtPrime p)).toRingEquiv
  have : Nontrivial T := by
    by_contra! h
    let : Subsingleton T := h
    exact (show q.IsPrime from inferInstance).ne_top (Subsingleton.elim q ⊤)
  have hcm := cm_of_ringEquiv eL (global_lci_cm k T (hglobal g hg) q)
  let eX : X.presheaf.stalk (φ i y) ≃+* Localization.AtPrime p :=
    ((asIso ((φ i).stalkMap y)) ≪≫ Spec.stalkIso S y).commRingCatIsoToRingEquiv
  exact ⟨isNoetherianRing_of_ringEquiv (Localization.AtPrime p) eX.symm,
    cm_of_ringEquiv eX.symm hcm⟩

end AlgebraicGeometry
