/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.RingTheory.IndPrincipalZariski
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.NormalOfFlatNormalFibers
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions

/-! # Nagata ascent along weakly etale ring maps

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Math. J. 60 (1976),
Remark 5.7(ii), p. 148, and Remark 5.2, p. 146
(blueprint: lem-exc-nagata-weakly-etale-ascent).
-/

@[expose] public section

universe u v

namespace RingHom

open scoped TensorProduct

private theorem normal_of_weaklyEtale {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.WeaklyEtale R S] [IsNoetherianRing R] [IsNoetherianRing S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  apply normal_of_flat_normal_fibers (algebraMap R S)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) _ hR
  rw [toAlgebra_algebraMap]
  intro p hp q hq
  have : Ring.AbsolutelyFlat (p.Fiber S) :=
    Ring.AbsolutelyFlat.of_flat_lmul' p.ResidueField (p.Fiber S)
      (Algebra.WeaklyEtale.flat_lmul' p.ResidueField (p.Fiber S))
  let fieldq : Field (Localization.AtPrime q) :=
    (Ring.AbsolutelyFlat.isField_of_isLocalization_prime (p.Fiber S) q _).toField
  let : CommRing (Localization.AtPrime q) := fieldq.toCommRing
  let : Ring (Localization.AtPrime q) := fieldq.toRing
  exact ⟨inferInstance, inferInstance⟩

private theorem finite_closure_of_normal_model {D L : Type*} [CommRing D] [Field L]
    [Algebra D L] [IsNoetherianRing D] (T : Subalgebra D L) [Module.Finite D T]
    [IsIntegrallyClosed T] [IsFractionRing T L] :
    Module.Finite D (integralClosure D L) := by
  let ringT : CommRing T := inferInstance
  let : Ring T := ringT.toRing
  let algTL : Algebra T L := inferInstance
  let : Module T L := algTL.toModule
  let : SMul T L := algTL.toSMul
  have hle : integralClosure D L ≤ T := by
    intro x hx
    have hxT : _root_.IsIntegral T x := _root_.IsIntegral.tower_top (R := D) (A := T) hx
    obtain ⟨t, ht⟩ :=
      IsIntegrallyClosed.algebraMap_eq_of_integral (R := T) (K := L) hxT
    change (t : L) = x at ht
    exact ht ▸ t.property
  let j : integralClosure D L →ₗ[D] T :=
    { toFun := fun x ↦ ⟨x.val, hle x.property⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.of_injective j fun x y h ↦ Subtype.ext (congrArg (fun t : T ↦ (t : L)) h)

private theorem exists_finite_field_model (k E L : Type*) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    [Algebra.IsAlgebraic k E] [FiniteDimensional E L] :
    ∃ K : IntermediateField k L, FiniteDimensional k K ∧
      Algebra.adjoin E (K : Set L) = ⊤ := by
  classical
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.trans k E L
  have : Algebra.FiniteType E L := Module.Finite.finiteType L
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := E) (A := L)
  let K := IntermediateField.adjoin k (s : Set L)
  have hfinite : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  refine ⟨K, hfinite, eq_top_iff.mpr ?_⟩
  rw [← hs]
  exact Algebra.adjoin_mono (IntermediateField.subset_adjoin k (s : Set L))

private theorem algebraic_image_of_weaklyEtale_field (k F E : Type*)
    [Field k] [CommRing F] [Field E] [Algebra k F] [Algebra k E]
    [Algebra.WeaklyEtale k F] (φ : F →ₐ[k] E) (x : F) : IsAlgebraic k (φ x) := by
  let P := RingHom.ker φ
  have : P.IsPrime := RingHom.ker_isPrime φ.toRingHom
  let T := Localization.AtPrime P
  have : Ring.AbsolutelyFlat F := Ring.AbsolutelyFlat.of_flat_lmul' k F
    (Algebra.WeaklyEtale.flat_lmul' k F)
  let fieldT : Field T := (Ring.AbsolutelyFlat.isField_of_isLocalization_prime F P T).toField
  let : CommRing T := fieldT.toCommRing
  let : Ring T := fieldT.toRing
  have : Algebra.WeaklyEtale k T := Algebra.WeaklyEtale.trans k F T
  let ψ : T →ₐ[k] E := IsLocalization.liftAlgHom (M := P.primeCompl) (f := φ)
    (fun y ↦ isUnit_iff_ne_zero.mpr y.property)
  have hx : IsAlgebraic k (algebraMap F T x) := by
    by_contra h
    apply Algebra.WeaklyEtale.not_forall_isUnit_aeval (K := k) (algebraMap F T x)
    intro p hp
    exact isUnit_iff_ne_zero.mpr (fun hz ↦ h ⟨p, hp, hz⟩)
  convert hx.algHom ψ using 1
  exact (IsLocalization.lift_eq (M := P.primeCompl) (S := T) (g := φ.toRingHom) _ x).symm

private theorem minimal_kernel_of_weaklyEtale {R C k L : Type*}
    [CommRing R] [IsDomain R] [CommRing C] [Field k] [Field L]
    [Algebra R C] [Algebra R k] [IsFractionRing R k] [Algebra R L]
    [Algebra.WeaklyEtale R C] (h : C →ₐ[R] L)
    (hinj : Function.Injective (algebraMap R L)) :
    IsMinimalPrime (RingHom.ker h) := by
  let G := k ⊗[R] C
  let ringG : CommRing G := inferInstance
  let : Ring G := ringG.toRing
  let : CompleteLattice (Ideal G) := inferInstance
  let : CompleteLattice (Ideal C) := inferInstance
  let algCG : Algebra C G := Algebra.TensorProduct.rightAlgebra
  let : Module C G := algCG.toModule
  let : SMul C G := algCG.toSMul
  let M := Algebra.algebraMapSubmonoid C (nonZeroDivisors R)
  have : IsLocalization M G := inferInstance
  have : Algebra.WeaklyEtale k G := inferInstance
  have : Ring.AbsolutelyFlat G := Ring.AbsolutelyFlat.of_flat_lmul' k G
    (Algebra.WeaklyEtale.flat_lmul' k G)
  have hiff : Ring.AbsolutelyFlat G ↔
      IsReduced G ∧ ∀ P : Ideal G, P.IsPrime → P.IsMaximal :=
    (Ring.AbsolutelyFlat.tfae G).out 0 1
  have hmax : ∀ P : Ideal G, P.IsPrime → P.IsMaximal := (hiff.mp inferInstance).2
  let Q := RingHom.ker h
  have hQ : Q.IsPrime := RingHom.ker_isPrime h.toRingHom
  have hd : Disjoint (M : Set C) (Q : Set C) := by
    rw [Set.disjoint_left]
    rintro c ⟨r, hr, rfl⟩ hc
    have hz : algebraMap R L r = 0 := by simpa [Q] using hc
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) (hinj (hz.trans (map_zero _).symm))
  refine ⟨⟨hQ, bot_le⟩, ?_⟩
  intro P hP hPQ
  have hdP : Disjoint (M : Set C) (P : Set C) :=
    Set.disjoint_of_subset_right hPQ hd
  have hp' := IsLocalization.isPrime_of_isPrime_disjoint M G P hP.1 hdP
  have hq' := IsLocalization.isPrime_of_isPrime_disjoint M G Q hQ hd
  have heq : P.map (algebraMap C G) = Q.map (algebraMap C G) :=
    (hmax _ hp').eq_of_le hq'.ne_top (Ideal.map_mono hPQ)
  have := congrArg (Ideal.comap (algebraMap C G)) heq
  change (P.map (algebraMap C G)).under C = (Q.map (algebraMap C G)).under C at this
  rw [IsLocalization.under_map_of_isPrime_disjoint M G hP.1 hdP,
    IsLocalization.under_map_of_isPrime_disjoint M G hQ hd] at this
  exact this.ge

private theorem normal_quotient_minimal {C : Type*} [CommRing C] [IsNoetherianRing C]
    (hn : ∀ (p : Ideal C) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (Q : Ideal C) (hQ : IsMinimalPrime Q) : IsIntegrallyClosed (C ⧸ Q) := by
  classical
  have : IsReduced C := isReduced_ofLocalizationMaximal C fun p hp ↦ by
    have : IsDomain (Localization.AtPrime p) := (hn p).1
    infer_instance
  obtain ⟨n, A, hA, ⟨e⟩⟩ :=
    (reduced_normal_iff_integrallyClosed_totalFractions C
      (minimalPrimes.finite_of_isNoetherianRing (R := C))).2.mp
      ((reduced_normal_iff_integrallyClosed_totalFractions C
        (minimalPrimes.finite_of_isNoetherianRing (R := C))).1.mp hn)
  have : Q.IsPrime := hQ.isPrime
  let P : PrimeSpectrum (∀ i : Fin n, A i) := PrimeSpectrum.comap e.symm ⟨Q, inferInstance⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq P
  let g : C →+* A i := (Pi.evalRingHom (fun j ↦ A j) i).comp e
  have hg : Function.Surjective g :=
    (Pi.evalRingHom (fun j ↦ A j) i).surjective.comp e.surjective
  have hle : RingHom.ker g ≤ Q := by
    intro c hc
    have he := congrArg PrimeSpectrum.asIdeal hq
    change q.asIdeal.comap (Pi.evalRingHom (fun j ↦ A j) i) = P.asIdeal at he
    have hcq : e c ∈ q.asIdeal.comap (Pi.evalRingHom (fun j ↦ A j) i) := by
      change g c ∈ q.asIdeal
      rw [show g c = 0 from hc]
      exact q.asIdeal.zero_mem
    rw [he] at hcq
    simpa [P] using hcq
  have : IsDomain (A i) := (hA i).1
  have hk : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  have heq : Q = RingHom.ker g := le_antisymm (hQ.2 ⟨hk, bot_le⟩ hle) hle
  have : IsIntegrallyClosed (A i) := (hA i).2
  subst Q
  exact IsIntegrallyClosed.of_equiv
    (RingHom.quotientKerEquivOfSurjective (f := g) hg).symm

private theorem finite_closure_of_isN2 {D : Type u} {k : Type u} {L : Type*}
    [CommRing D] [IsDomain D] [Field k] [Field L]
    [Algebra D k] [IsFractionRing D k] [Algebra k L] [Algebra D L]
    [IsScalarTower D k L] [FiniteDimensional k L] (hD : IsN2 D k) :
    Module.Finite D (integralClosure D L) := by
  have : Small.{u} L := Module.Finite.small k L
  let : IsScalarTower D k (Shrink.{u} L) :=
    IsScalarTower.of_algebraMap_eq fun d ↦ by
      apply (Shrink.algEquiv D L).injective
      rw [AlgEquiv.commutes]
      change algebraMap D L d =
        (Shrink.algEquiv k L) (algebraMap k (Shrink.{u} L) (algebraMap D k d))
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply D k L d
  have : Module.Finite D (integralClosure D (Shrink.{u} L)) := hD (Shrink.{u} L)
  exact Module.Finite.equiv (Shrink.algEquiv D L).mapIntegralClosure.toLinearEquiv

private theorem fractionRing_of_two_models {D E R K L : Type*}
    [CommRing D] [IsDomain D] [Field E] [CommRing R] [IsDomain R] [Field K] [Field L]
    [Algebra D E] [IsFractionRing D E] [Algebra E L] [Algebra D L]
    [IsScalarTower D E L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (T : Subalgebra D L) (hR : ∀ r : R, algebraMap R L r ∈ T)
    (hgen : Algebra.adjoin E (Set.range (algebraMap K L)) = ⊤) :
    IsFractionRing T L := by
  let H := Subfield.closure (Set.range T.val)
  have hD (d : D) : algebraMap D L d ∈ H :=
    Subfield.subset_closure ⟨algebraMap D T d, rfl⟩
  have hE (e : E) : algebraMap E L e ∈ H := by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective D e
    simpa only [map_div₀, ← IsScalarTower.algebraMap_apply] using div_mem (hD a) (hD b)
  have hK (k : K) : algebraMap K L k ∈ H := by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R k
    simp only [map_div₀, ← IsScalarTower.algebraMap_apply]
    exact div_mem (Subfield.subset_closure ⟨⟨_, hR a⟩, rfl⟩)
      (Subfield.subset_closure ⟨⟨_, hR b⟩, rfl⟩)
  have htop : H = ⊤ := by
    apply top_unique
    intro x hxTop
    clear hxTop
    have hx : x ∈ Algebra.adjoin E (Set.range (algebraMap K L)) := by rw [hgen]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hK k
    | algebraMap e => exact hE e
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  apply IsFractionRing.of_field
  intro x
  have hx : x ∈ H := htop ▸ Set.mem_univ x
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp hx
  have hsub : Subring.closure (Set.range T.val) ≤ T.toSubring := by
    apply Subring.closure_le.mpr
    rintro _ ⟨t, rfl⟩
    exact t.property
  exact ⟨⟨a, hsub ha⟩, ⟨b, hsub hb⟩, hab.symm⟩

/-- A weakly etale ring map from a Nagata ring to a Noetherian ring has Nagata target.
Source: Greco, Two theorems on excellent rings, Remark 5.7(ii), p. 148; Remark 5.2
identifies absolute flatness with weak etaleness for Noetherian rings.
(blueprint: lem-exc-nagata-weakly-etale-ascent).

Proof plan (the eight steps of the DAG node):
1. First establish the field-fibre calculation, for reuse below. Let $k\to F$ be any weakly etale
   algebra over a field. By [lem-weil-pbc-weak-etale-field], $F$ is reduced, every finitely
   generated $k$-subalgebra is finite etale, and its residue fields are separable algebraic over
   $k$. Apply [lem-weil-pbc-finite-algebra-is-integral] to the finite subalgebra $k[x]$, for each
   $x\in F$: every element of $F$ is integral over $k$. For any prime $P$ of $F$, the domain $F/P$
   is therefore algebraic over $k$. For $0\ne z\in F/P$, choose a monic relation of least degree.
   Its constant term is nonzero, since otherwise cancellation of $z$ gives a lower-degree
   relation. Solving this relation for $z^{-1}$ shows that $F/P$ is a field. Thus every prime of
   $F$ is maximal, and no two distinct primes are comparable; every prime is also minimal. Now
   [lem-weil-pbc-minimal-prime-reduced-localization-field] says that $F_P$ is a field for each
   $P$. In particular these local rings are normal domains by [def-weil-pbc-normal-ring], because
   the fraction field of a field is that field itself. Thus $F$ is a normal ring, with every prime
   maximal, including when $F$ is the zero ring (there are then no primes).

2. For any weakly etale map $U\to V$ of Noetherian rings and any $U$-algebra $U'$, the
   ring-to-scheme equivalence in [def-weil-pbc-ind-etale-algebra] and the base-change clause of
   [lem-weil-pbc-weakly-etale-composition-base-change], identified on affine spectra by
   [lem-weil-pbc-affine-chart-base-change-iso], makes $U'\to V\otimes_U U'$ weakly etale. In
   particular its fibre at $p\subset U$ is $F_p=V\otimes_U\kappa(p)=(U\setminus p)^{-1}(V/pV)$.
   This ring is Noetherian: $V/pV$ is a cyclic finite $V$-algebra, so
   [lem-weil-pbc-finite-algebra-noetherian] applies, and then
   [lem-weil-pbc-localization-noetherian] applies. Step 1 shows that every $F_p$ is normal and has
   all primes maximal. Its residue fields are separable algebraic over $\kappa(p)$. For $q\subset
   V$ over $p$, the fibre prime is the extension of $q/pV$; its residue field is
   $\operatorname{Frac}(V/q)=\kappa(q)$: localizing $V/q$ first at $U\setminus p$ and then at all
   its nonzero elements gives exactly the same fractions as localizing at all nonzero elements at
   once. Thus $\kappa(q)/\kappa(p)$ is algebraic, including when it is infinite.

3. Fix a prime $q\subset B$, put $p=f^{-1}(q)$, $k=\kappa(p)=\operatorname{Frac}(A/p)$ and
   $E=\kappa(q)=\operatorname{Frac}(B/q)$, and fix an arbitrary finite field extension $L/E$. Step
   2 gives that $E/k$ is algebraic. There is a finite subextension $L_0/k$ inside $L$ with
   $L=EL_0$: choose a finite $E$-basis $x_1,\ldots,x_r$ of $L$. Each $x_i$ satisfies a monic
   polynomial over $E$; the finitely many coefficients of these polynomials lie in a finite
   extension $k_1/k$ inside $E$, because adjoining finitely many algebraic elements is spanned
   successively by bounded powers. The ring $k_1[x_1,\ldots,x_r]$ is finite dimensional over $k_1$
   by the same bounded-power spanning argument and is a domain, hence a field: multiplication by a
   nonzero element is an injective endomorphism of a finite-dimensional vector space and is
   surjective. It is therefore a finite extension of $k$, and so is its subfield
   $L_0=k(x_1,\ldots,x_r)$. Finally $EL_0=L$ since $EL_0$ contains the chosen $E$-basis. No finite
   degree for $E/k$ is asserted.

4. Let $R\subset L_0$ be the integral closure of $A/p$ in $L_0$. Since $A$ is Nagata,
   [def-weil-pbc-nagata-ring] gives that $A/p$ is Japanese; [def-weil-pbc-japanese-domain] gives
   that $R$ is finite over $A/p$, hence over $A$. The precise normalization lemma
   [lem-weil-pbc-integral-closure-finite-extension-normal] gives that $R$ is a normal domain with
   fraction field $L_0$. By [lem-weil-pbc-finite-algebra-noetherian], $R$ is Noetherian. By
   [lem-weil-pbc-localization-normal-domain], each prime localization of $R$ is a normal domain,
   so $R$ is a normal ring as required by the normality ascent lemma.

5. Set $C=B\otimes_A R$. Step 2 gives that $R\to C$ is weakly etale. If $r_1,\ldots,r_s$ generate
   $R$ as an $A$-module, the elements $1\otimes r_j$ generate $C$ as a $B$-module, by expanding
   each pure tensor and then each sum of pure tensors. Thus $C$ is finite over the Noetherian ring
   $B$, and [lem-weil-pbc-finite-algebra-noetherian] makes $C$ Noetherian. Its fibre rings over
   $R$ are normal by step 2; the map $R\to C$ is flat by [def-weil-pbc-ind-etale-algebra]. All
   five hypotheses of [lem-weil-pbc-flat-normal-fibres-noetherian-normal] are now present: $R,C$
   Noetherian, flatness, normal fibres, and $R$ normal. Consequently $C$ is normal.

6. The maps $B\to B/q\subset E\subset L$ and $R\subset L_0\subset L$ agree on $A$ and give $h:C\to
   L$, $b\otimes r\mapsto\bar b r$. Write $Q=\ker h$ and $D=h(C)=C/Q\subset L$. Then $Q\cap R=0$
   and $Q\cap B=q$. The prime $Q$ is minimal: the generic fibre is weakly etale over $L_0$ by step
   2; applying [lem-weil-pbc-weak-etale-field] and the algebraic-domain inverse calculation of
   step 1 shows that all its primes are maximal, so the following extension-contraction argument
   applies. If $Q_0\subseteq Q$ is another prime of $C$, both avoid every nonzero element of $R$.
   Their extensions in $C\otimes_R L_0$ are primes, since the quotients embed in localizations of
   the domains $C/Q_i$. These extensions contract back to $Q_i$: if $sc\in Q_i$ with $0\ne s\in
   R$, primality gives $c\in Q_i$. But the generic fibre $C\otimes_R L_0$ has every prime maximal
   by step 2. The two extended primes, one contained in the other, must be equal, hence $Q_0=Q$.
   This proves minimality without claiming that $h$ is surjective onto $L$.

7. By [lem-weil-pbc-noetherian-finitely-many-minimal-primes], $C$ has finitely many minimal
   primes. It is reduced, since every prime localization of the normal ring $C$ is a domain and
   the maps to those localizations are jointly injective by
   [lem-weil-pbc-prime-localizations-jointly-injective]. Apply
   [lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions] to obtain
   $C\cong\prod_{i=1}^t C_i$ with each $C_i$ a normal domain. A prime in a finite product chooses
   one factor: of the orthogonal idempotents $e_i$ summing to $1$, exactly one is outside a prime;
   all other factors vanish in the quotient. Since $Q$ is minimal, its prime in the selected
   domain factor is $(0)$. Thus $D=C/Q$ is that normal domain factor. It is finite over $B/q$,
   generated by the images of $1\otimes r_j$. Its fraction field inside $L$ contains $E$ because
   it contains $B/q$, and contains $L_0$ because it contains $R$. It therefore equals $EL_0=L$.

8. The finite algebra $D$ is integral over $B/q$ by [lem-weil-pbc-finite-algebra-is-integral].
   Conversely any $x\in L$ integral over $B/q$ satisfies the same monic polynomial over the larger
   subring $D$, so lies in $D$, since $D$ is normal with fraction field $L$. Therefore $D$ is
   exactly the integral closure of $B/q$ in $L$, and it is finite over $B/q$. The prime $q$ and
   finite extension $L/E$ were arbitrary. By [def-weil-pbc-japanese-domain] every $B/q$ is
   Japanese. With the assumed Noetherianity of $B$, [def-weil-pbc-nagata-ring] gives that $B$ is
   Nagata. This part of the argument has not needed J-2. If $B$ is the zero ring there is no prime
   $q$, so the Japanese conditions are vacuous and its assumed Noetherianity still gives the
   conclusion.
-/
theorem isNagataRing_of_weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (f : A →+* B) (hf : @Algebra.WeaklyEtale A B _ _ f.toAlgebra)
    (hA : IsNagataRing A) : IsNagataRing B := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.WeaklyEtale A B := hf
  have : IsNoetherianRing A := hA.1
  refine ⟨inferInstance, ?_⟩
  intro q hq L _ _ _ _ _
  let fieldL : Field L := inferInstance
  let : CommRing L := fieldL.toCommRing
  let : Ring L := fieldL.toRing
  let algBqL : Algebra (B ⧸ q) L := inferInstance
  let : Module (B ⧸ q) L := algBqL.toModule
  let : SMul (B ⧸ q) L := algBqL.toSMul
  let ringBq : CommRing (B ⧸ q) := inferInstance
  let : Ring (B ⧸ q) := ringBq.toRing
  let p : Ideal A := q.comap f
  have : p.IsPrime := Ideal.IsPrime.comap f
  let D := A ⧸ p
  let crD : CommRing D := inferInstance
  let : Ring D := crD.toRing
  have : IsDomain D := inferInstance
  let E := FractionRing (B ⧸ q)
  let k := FractionRing D
  let algEL : Algebra E L := inferInstance
  let : Module E L := algEL.toModule
  let : SMul E L := algEL.toSMul
  let fldE : Field E := inferInstance
  let fldk : Field k := inferInstance
  let : CommRing E := fldE.toCommRing
  let : Ring E := fldE.toRing
  let : CommRing k := fldk.toCommRing
  let : Ring k := fldk.toRing
  let algBE : Algebra (B ⧸ q) E := inferInstance
  let algDk : Algebra D k := inferInstance
  let : Module (B ⧸ q) E := algBE.toModule
  let : SMul (B ⧸ q) E := algBE.toSMul
  let : Module D k := algDk.toModule
  let : SMul D k := algDk.toSMul
  let : Algebra D (B ⧸ q) := Ideal.Quotient.algebraQuotientOfLEComap
    (show p ≤ q.comap (algebraMap A B) from le_rfl)
  let : IsScalarTower A D (B ⧸ q) := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  let algDE : Algebra D E :=
    ((algebraMap (B ⧸ q) E).comp (algebraMap D (B ⧸ q))).toAlgebra
  let : Module D E := algDE.toModule
  let : SMul D E := algDE.toSMul
  let : IsScalarTower D (B ⧸ q) E :=
    IsScalarTower.of_algebraMap_eq (R := D) (S := B ⧸ q) (A := E) (fun _ ↦ rfl)
  have hinj : Function.Injective (algebraMap D E) :=
    (IsFractionRing.injective (B ⧸ q) E).comp Ideal.algebraMap_quotient_injective
  let algkE : Algebra k E := (IsFractionRing.lift hinj).toAlgebra
  let : Module k E := algkE.toModule
  let : SMul k E := algkE.toSMul
  let : IsScalarTower D k E := IsScalarTower.of_algebraMap_eq fun d ↦
    (IsFractionRing.lift_algebraMap hinj d).symm
  let algAk : Algebra A k := ((algebraMap D k).comp (algebraMap A D)).toAlgebra
  let : Module A k := algAk.toModule
  let : SMul A k := algAk.toSMul
  let : IsScalarTower A D k := IsScalarTower.of_algebraMap_eq' rfl
  let algAE : Algebra A E :=
    ((algebraMap (B ⧸ q) E).comp (algebraMap A (B ⧸ q))).toAlgebra
  let : Module A E := algAE.toModule
  let : SMul A E := algAE.toSMul
  let : IsScalarTower A (B ⧸ q) E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq fun a ↦ by
    simp only [IsScalarTower.algebraMap_apply D (B ⧸ q) E,
      IsScalarTower.algebraMap_apply A (B ⧸ q) E]
    congr 1
  let : IsScalarTower A k E := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A D E,
      IsScalarTower.algebraMap_apply A D k,
      IsScalarTower.algebraMap_apply D k E]
  let algBE' : Algebra B E :=
    ((algebraMap (B ⧸ q) E).comp (algebraMap B (B ⧸ q))).toAlgebra
  let : Module B E := algBE'.toModule
  let : SMul B E := algBE'.toSMul
  let : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  let χ : k ⊗[A] B →ₐ[k] E := Algebra.TensorProduct.lift (Algebra.ofId k E)
    (IsScalarTower.toAlgHom A B E) (fun _ _ ↦ Commute.all _ _)
  have halg (b : B) : IsAlgebraic k (algebraMap B E b) := by
    simpa [χ] using algebraic_image_of_weaklyEtale_field k (k ⊗[A] B) E χ (1 ⊗ₜ[A] b)
  have : Algebra.IsAlgebraic k E := ⟨fun x ↦ by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (B ⧸ q) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change IsAlgebraic k (algebraMap B E a / algebraMap B E b)
    simpa only [div_eq_mul_inv] using
      ((halg a).isIntegral.mul (halg b).inv.isIntegral).isAlgebraic⟩
  let algkL : Algebra k L := ((algebraMap E L).comp (algebraMap k E)).toAlgebra
  let : Module k L := algkL.toModule
  let : SMul k L := algkL.toSMul
  let : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq' rfl
  let algDL : Algebra D L := ((algebraMap E L).comp (algebraMap D E)).toAlgebra
  let : Module D L := algDL.toModule
  let : SMul D L := algDL.toSMul
  let : IsScalarTower D E L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower D k L := IsScalarTower.of_algebraMap_eq fun d ↦ by
    change algebraMap E L (algebraMap D E d) =
      algebraMap E L (algebraMap k E (algebraMap D k d))
    rw [IsScalarTower.algebraMap_apply D k E]
  obtain ⟨K, hK, hgen⟩ := exists_finite_field_model k E L
  let fldK : Field K := inferInstance
  let : CommRing K := fldK.toCommRing
  let : Ring K := fldK.toRing
  let algkK : Algebra k K := inferInstance
  let : Module k K := algkK.toModule
  let : SMul k K := algkK.toSMul
  let algDK : Algebra D K := inferInstance
  let : Module D K := algDK.toModule
  let : SMul D K := algDK.toSMul
  let algKL : Algebra K L := inferInstance
  let : Module K L := algKL.toModule
  let : SMul K L := algKL.toSMul
  have : FiniteDimensional k K := hK
  let : IsScalarTower D K L :=
    IsScalarTower.of_algebraMap_eq fun d ↦ rfl
  let R : Type _ := integralClosure D K
  let crR : CommRing R := inferInstance
  let : Ring R := crR.toRing
  let algDR : Algebra D R := inferInstance
  let : Module D R := algDR.toModule
  let : SMul D R := algDR.toSMul
  let algRK : Algebra R K := inferInstance
  let : Module R K := algRK.toModule
  let : SMul R K := algRK.toSMul
  have : IsDomain R := inferInstance
  have : Module.Finite D R := finite_closure_of_isN2 (hA.2 p)
  have : IsFractionRing R K := integralClosure.isFractionRing_of_finite_extension k K
  have : IsIntegrallyClosed R := integralClosure.isIntegrallyClosedOfFiniteExtension k
  have : IsNoetherianRing R := IsNoetherianRing.of_finite D R
  let algAR : Algebra A R := ((algebraMap D R).comp (algebraMap A D)).toAlgebra
  let : Module A R := algAR.toModule
  let : SMul A R := algAR.toSMul
  let : IsScalarTower A D R := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite A R := Module.Finite.trans D R
  let algRL : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : Module R L := algRL.toModule
  let : SMul R L := algRL.toSMul
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let algAL : Algebra A L := ((algebraMap (B ⧸ q) L).comp
    (algebraMap A (B ⧸ q))).toAlgebra
  let : Module A L := algAL.toModule
  let : SMul A L := algAL.toSMul
  let algBL : Algebra B L := ((algebraMap (B ⧸ q) L).comp
    (algebraMap B (B ⧸ q))).toAlgebra
  let : Module B L := algBL.toModule
  let : SMul B L := algBL.toSMul
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  let : IsScalarTower A R L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap (B ⧸ q) L (algebraMap A (B ⧸ q) a) =
      algebraMap K L (algebraMap R K (algebraMap D R (algebraMap A D a)))
    rw [← IsScalarTower.algebraMap_apply D R K,
      ← IsScalarTower.algebraMap_apply D K L]
    rw [IsScalarTower.algebraMap_apply D E L,
      IsScalarTower.algebraMap_apply D (B ⧸ q) E,
      ← IsScalarTower.algebraMap_apply (B ⧸ q) E L,
      ← IsScalarTower.algebraMap_apply A D (B ⧸ q)]
  let C := R ⊗[A] B
  let crC : CommRing C := inferInstance
  let : Ring C := crC.toRing
  let algRC : Algebra R C := inferInstance
  let : Module R C := algRC.toModule
  let : SMul R C := algRC.toSMul
  let algBC : Algebra B C := Algebra.TensorProduct.rightAlgebra
  let : Module B C := algBC.toModule
  let : SMul B C := algBC.toSMul
  have : Module.Finite B C := Module.Finite.equiv
    (Algebra.TensorProduct.commRight A B R).toLinearEquiv
  have : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  have hn : ∀ (P : Ideal C) [P.IsPrime],
      IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) :=
    normal_of_weaklyEtale (R := R) (S := C) fun P _ ↦ ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors⟩
  let h : C →ₐ[A] L := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A R L)
    (IsScalarTower.toAlgHom A B L) (fun _ _ ↦ Commute.all _ _)
  let hR : C →ₐ[R] L := ⟨h.toRingHom, fun r ↦ by
    change algebraMap R L r * algebraMap B L 1 = _
    rw [map_one, mul_one]⟩
  have hmin : IsMinimalPrime (RingHom.ker h) :=
    minimal_kernel_of_weaklyEtale (k := K) hR
      ((algebraMap K L).injective.comp (IsFractionRing.injective R K))
  let T : Subalgebra (B ⧸ q) L :=
    { h.toRingHom.range with
      algebraMap_mem' := fun b ↦ by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
        refine ⟨1 ⊗ₜ[A] b, ?_⟩
        change algebraMap R L 1 * algebraMap B L b = _
        rw [map_one, one_mul]
        rfl }
  let crT : CommRing T := inferInstance
  let : Ring T := crT.toRing
  let algBqT : Algebra (B ⧸ q) T := inferInstance
  let : Module (B ⧸ q) T := algBqT.toModule
  let : SMul (B ⧸ q) T := algBqT.toSMul
  let algTL : Algebra T L := inferInstance
  let : Module T L := algTL.toModule
  let : SMul T L := algTL.toSMul
  let algBT : Algebra B T :=
    ((algebraMap (B ⧸ q) T).comp (algebraMap B (B ⧸ q))).toAlgebra
  let : Module B T := algBT.toModule
  let : SMul B T := algBT.toSMul
  have hright (b : B) : h (algebraMap B C b) = algebraMap B L b := by
    change algebraMap R L 1 * algebraMap B L b = _
    rw [map_one, one_mul]
  let hT : C →ₐ[B] T :=
    { h.toRingHom.rangeRestrict with
      commutes' := fun b ↦ Subtype.ext (hright b) }
  have : Module.Finite B T := Module.Finite.of_surjective hT.toLinearMap
    h.toRingHom.rangeRestrict_surjective
  let : IsScalarTower B (B ⧸ q) T := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  have : Module.Finite (B ⧸ q) T := Module.Finite.of_restrictScalars_finite B (B ⧸ q) T
  have : IsIntegrallyClosed (C ⧸ RingHom.ker h) := normal_quotient_minimal hn _ hmin
  have : IsIntegrallyClosed T :=
    IsIntegrallyClosed.of_equiv (R := C ⧸ RingHom.ker h)
      (RingHom.quotientKerEquivRange h.toRingHom)
  have : IsFractionRing T L := fractionRing_of_two_models (E := E) (R := R) (K := K) T
    (fun r ↦ ⟨r ⊗ₜ[A] 1, by
      change algebraMap R L r * algebraMap B L 1 = _
      rw [map_one, mul_one]⟩) (by
        have hrange : Set.range (algebraMap K L) = (K : Set L) := by
          change Set.range (Subtype.val : K → L) = (K : Set L)
          exact Subtype.range_val
        rw [hrange]
        exact hgen)
  exact finite_closure_of_normal_model T

end RingHom
