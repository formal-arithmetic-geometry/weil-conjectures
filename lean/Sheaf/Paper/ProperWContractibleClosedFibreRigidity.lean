/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.ClosedFibreModuleEvaluation
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.FieldTheory.IsSepClosed

import all Sheaf.Paper.FiniteConstantStratifiedZariskiLocality
import Sheaf.Paper.WeaklyEtaleDerivedEvaluationRestriction
import Sheaf.AlgebraicGeometry.ProperWContractibleTorsionRigidity
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.RingTheory.WContractibleJacobsonHenselian
import Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Proper comparison with the closed fibre of a w-contractible base

Source: main-20261015, det-sf-comp-coherence-refinement.proof.md, paragraph (2).
The closed-point geometry is Ruimy--Tubach--Wolf, Proposition 1.1.2.
The full coefficient-transfer assertion is an agent-formulated obligation, source WANTED.
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity).

The comparison is the right-derived map of the actual module adjunction unit followed
by restriction of sections. Both sides derive evaluation in the module categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The reduced scheme of closed points is the quotient by the intersection of maximal ideals.
Source: Ruimy--Tubach--Wolf, Proposition 1.1.2, and Step 1 of the node
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
abbrev wContractibleClosedPointScheme (R : Type u) [CommRing R] : Scheme.{u} :=
  Spec (CommRingCat.of (R ⧸ Ideal.jacobson (⊥ : Ideal R)))

/-- The specified quotient immersion, with no choice of closed subscheme structure.
Source: Step 1 of the node, quotient by the Jacobson radical
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
abbrev wContractibleClosedPointImmersion (R : Type u) [CommRing R] :
    wContractibleClosedPointScheme R ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.jacobson (⊥ : Ideal R))))

/-- The map from X_C to X_W induced by the quotient C to W.
Source: the two fibre products in the proper comparison node
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
def properClosedFibreMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type u) [CommRing R] (w : Spec (CommRingCat.of R) ⟶ Y) :
    pullback f (wContractibleClosedPointImmersion R ≫ w) ⟶ pullback f w :=
  pullback.lift (pullback.fst f (wContractibleClosedPointImmersion R ≫ w))
    (pullback.snd f (wContractibleClosedPointImmersion R ≫ w) ≫
      wContractibleClosedPointImmersion R)
    ((pullback.condition (f := f) (g := wContractibleClosedPointImmersion R ≫ w)).trans
      (Category.assoc _ _ _).symm)

/-- The canonical map from derived evaluation on X_W to derived global sections on X_C.
Source: final paragraph of the proper closed-fibre comparison
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
def properClosedFibreDerivedRestriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type u) [CommRing R] (w : Spec (CommRingCat.of R) ⟶ Y) [WeaklyEtale w] :=
  closedFibreModuleDerivedRestriction Λ
    (pullback.fst f (wContractibleClosedPointImmersion R ≫ w))
    (Scheme.ProEt.mk (pullback.fst f w)) (properClosedFibreMap f R w)
    (pullback.lift_fst _ _ _)

private theorem jacobson_zeroLocus_closedPoints (R : Type u) [CommRing R]
    [IsWLocalRing R] :
    PrimeSpectrum.zeroLocus (Ideal.jacobson (⊥ : Ideal R) : Set R) =
      closedPoints (PrimeSpectrum R) := by
  have hJ : Ideal.jacobson (⊥ : Ideal R) =
      PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum R)) := by
    apply le_antisymm
    · intro a ha
      apply (PrimeSpectrum.mem_vanishingIdeal _ _).mpr
      intro p hp
      exact (sInf_le (show p.asIdeal ∈
        {m : Ideal R | (⊥ : Ideal R) ≤ m ∧ m.IsMaximal} from
          ⟨bot_le, (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
            (mem_closedPoints_iff.mp hp)⟩)) ha
    · apply le_sInf
      intro m hm a ha
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha ⟨m, hm.2.isPrime⟩
        (mem_closedPoints_iff.mpr
          ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm.2))
  rw [hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    WLocalSpace.isClosed_closedPoints.closure_eq]

private theorem jacobson_quotient_maximal (R : Type u) [CommRing R] [IsWLocalRing R]
    (p : PrimeSpectrum (R ⧸ Ideal.jacobson (⊥ : Ideal R))) : p.asIdeal.IsMaximal := by
  let J := Ideal.jacobson (⊥ : Ideal R)
  let q := Ideal.Quotient.mk J
  have h : PrimeSpectrum.comap q p ∈ closedPoints (PrimeSpectrum R) := by
    rw [← jacobson_zeroLocus_closedPoints R, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    change q a ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact p.asIdeal.zero_mem
  have hm : (p.asIdeal.comap q).IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp (mem_closedPoints_iff.mp h)
  have := hm
  have hmap := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := q) Ideal.Quotient.mk_surjective (m := p.asIdeal.comap q)
    (fun a ha ↦ by rw [Ideal.mem_comap, RingHom.mem_ker.mp ha]; exact p.asIdeal.zero_mem)
  rwa [Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective] at hmap

private theorem jacobson_quotient_residue (R : Type u) [CommRing R]
    [IsWContractibleRing R]
    (hC : IsWContractibleRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (c : wContractibleClosedPointScheme R) :
    IsSepClosed ((wContractibleClosedPointScheme R).residueField c) := by
  let := hC
  have : c.asIdeal.IsMaximal := jacobson_quotient_maximal R c
  have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization c.asIdeal
  exact IsSepClosed.of_ringEquiv (Scheme.Spec.residueFieldIso
    (CommRingCat.of (R ⧸ Ideal.jacobson (⊥ : Ideal R))) c).commRingCatIsoToRingEquiv.symm

private theorem pullback_constructible_to_qcqs {T X : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T] (b : T ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ T ((upperStar Λ b).obj M) := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  unfold IsConstantModelConstructible at hM
  split_ifs at hM with hX
  · exact stratified_pullback Λ b M hM
  · apply stratified_of_affine_neighborhoods Λ
    intro t
    obtain ⟨V, hV, htV, _⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show b t ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨W, hW, htW, hWV⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens)
        (show t ∈ b ⁻¹ᵁ V from htV)
    refine ⟨W, hW, htW, ?_⟩
    let a : Scheme.Opens.toScheme W ⟶ Scheme.Opens.toScheme V := T.homOfLE hWV ≫ b ∣_ V
    have ha : a ≫ (Scheme.Opens.ι V) = (Scheme.Opens.ι W) ≫ b := by
      dsimp only [a]
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    exact stratified_of_iso Λ
      ((squarePullbackIso Λ a (Scheme.Opens.ι W) (Scheme.Opens.ι V) b ha).app M)
      (stratified_pullback Λ a _ (hM V hV))

private theorem pullback_serre_to_qcqs {T X : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T] (b : T ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ T) ((upperStar Λ b).obj M) := by
  let F := upperStar Λ b
  let P := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstantModelConstructible Λ T)
  let Q := P.inverseImage F
  have : PreservesColimitsOfSize.{u + 1, u + 1} F :=
    (upperStarLowerStarAdjunction Λ b).leftAdjoint_preservesColimits
  exact hM Q (fun N hN ↦ ObjectProperty.le_weakSerreCoproductClosure _ _
    (pullback_constructible_to_qcqs Λ b N hN)) inferInstance inferInstance inferInstance
    inferInstance (fun _ ↦ inferInstance)

/-- All closed-point geometry and the proper derived rigidity comparison, with ordinary
uncompleted coefficients, on the full weak Serre coproduct closure.
Source: main-20261015, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph;
Ruimy--Tubach--Wolf 1.1.2 and 1.1.5 supply geometry only. The full coefficient transfer
is the separately named source-WANTED obligation in the DAG.
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity).

Proof plan (all eight steps of the current reviewed DAG):
1. The w-local definition says that the set $W^c$ of closed points is closed, and every point
specializes to a unique member of $W^c$. Since $J$ is the intersection of the maximal ideals,
$V(J)$ is the closure of $W^c$, hence equals $W^c$. The quotient-spectrum homeomorphism
identifies $|C|$ with this subspace. The ideal $J$ is radical (an intersection of prime ideals),
so $R/J$ is reduced; its primes are all maximal. Its local ring at $\mathfrak m/J$ is therefore
the field $R/\mathfrak m$, which is separably closed because $R_{\mathfrak m}$ is strictly
henselian. The component theorem identifies $W^c$ homeomorphically with $\pi_0(W)$. Thus $|C|$
is the same extremally disconnected profinite space. Its connected components are singletons,
its local rings are separably closed fields, and it is w-contractible by the definition. This
proves every asserted geometric property of $C$, also when $R=0$.
Uses: sk-def-pe-wlocal, lem-weil-pbc-spec-quotient-homeomorphism-zero-locus, det-pe-wlocal-
components.

2. Write $T=X_W$, $T_0=X_C$, $b:T\to X$, $t:T_0\hookrightarrow T$, $q:T\to W$, and $q_0:T_0\to
C$. Base change makes $q,q_0$ proper and $t$ a closed immersion. Both bases are affine, hence
qcqs. Finite type over an affine base gives a finite affine cover of each source; separatedness
over that base makes all pairwise affine-open intersections affine. The affine-cover criterion
therefore makes $T,T_0$ qcqs. This verifies the geometric hypotheses of the relative
coefficient-transfer lemma; it does not require $Y$ itself to be quasi-separated.
Uses: lem-weil-pbc-proper-fp-permanence, def-weil-proper-morphism, def-weil-finite-type-
morphism, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-separated-affine-open-intersection, lem-
weil-pbc-quasi-separated-affine-cover-criterion.

3. Apply the Jacobson-henselian lemma to $R$, obtaining the henselian pair $(R,J)$. The identity
$W\to W$ is a closed immersion, hence proper by the closed-immersion clause of proper
permanence. Apply henselian proper $H^0$ comparison to it; its closed fibre
$W\times_R\operatorname{Spec}(R/J)$ is $C$. For every abelian étale sheaf $G$ on $W$, this gives
the actual natural restriction isomorphism
$\Gamma(W_{\mathrm{et}},G)\to\Gamma(C_{\mathrm{et}},i^{-1}G)$. No torsion hypothesis is needed
at this step.
Uses: lem-sfb-wcontractible-jacobson-henselian, sk-thm-pbc-henselian-h0, lem-weil-pbc-proper-fp-
permanence.

4. The schemes $W$ and $C$ are w-contractible. The weakly contractible basis theorem says their
representables are projective, so evaluation is exact on pro-étale abelian sheaves: lift a
section of the target of an epimorphism using a section of its pullback to the representable.
Hence their positive pro-étale abelian cohomology vanishes. The abelian étale/pro-étale
comparison gives the same vanishing for every abelian étale sheaf. Applying $H^1$ to the kernel
of a sheaf epimorphism shows that étale global sections on each base are exact as well.
Uses: sk-thm-pe-weakly-contractible-basis, lem-cbc-abelian-etale-proetale-cohomology-comparison.

5. Let $F$ be any torsion abelian sheaf on $T_{\mathrm{et}}$. Torsion proper base change for $q$
along $i$ gives $i^{-1}Rq_*F\simeq R(q_0)_*t^{-1}F$. Since inverse image is exact, taking degree
$r$ gives $i^{-1}R^rq_*F\simeq R^r(q_0)_*t^{-1}F$. The exact-global-sections Leray
identification from the preceding step and the $H^0$ restriction of step 3 give, for each
$r\geq0$,
$$H^r(T,F)\cong\Gamma(W,R^rq_*F)\cong\Gamma(C,i^{-1}R^rq_*F)\cong\Gamma(C,R^r(q_0)_*t^{-
1}F)\cong H^r(T_0,t^{-1}F).$$
These are the canonical restriction maps: proper base change is the counit mate, the middle
restriction is the adjunction unit of $i$, and Leray uses the composition comparison for these
same adjunctions. Thus this verifies the torsion-rigidity hypothesis of the transfer lemma for
the actual map $t$, with locally torsion $F$ and no common annihilator.
Uses: thm-weil-pbc-bounded-below, def-weil-pbc-exact-global-sections-leray, lem-weil-pbc-exact-
functor-complex-cohomology, lem-kun-leray-bdd.

6. The inverse image $b^*$ is exact and is a left adjoint, so preserves kernels, cokernels,
extensions and all small coproducts. It also preserves the constructible generators. Indeed,
locally on affine opens of $X$ and $T$, pull back a finite constructible stratification and its
pro-étale trivializing covers; inverse images of the constructible strata are constructible, and
the scalar-matrix lemma pulls back each finite scalar presentation to the same scalar matrix.
Since $T$ is qcqs (step 2), its definition asks for one global finite stratification: cover $T$
by finitely many affine opens $V_1,\dots,V_n$, each mapping into an affine open of $X$, and take
the strata $(V_k\setminus(V_1\cup\dots\cup V_{k-1}))\cap S$ with $S$ a pulled-back stratum of
$V_k$. Quasi-compact opens of the qcqs $T$ are retrocompact, so these finitely many locally
closed strata are constructible, and on each the restricted local model is unchanged.
Consequently the class $\{N\in\mathcal A_X:b^*N\in\mathcal P_T\}$ contains the generators and
zero and has every closure operation defining $\mathcal P_X$. Its minimality gives
$b^*M\in\mathcal P_T$ for every $M\in\mathcal P_X$.
Uses: det-prop-sfb-module-pullback-exact-main, sk-def-sfb-module-pushforward-pullback, lem-weil-
pbc-left-adjoint-preserves-colimits, sk-def-sfb-constructible, lem-pur-scheme-constructible-
preimage, lem-sfb-scalar-matrix-inverse-image.

7. Apply the closed torsion-rigidity coefficient-transfer lemma to $(T,T_0,t)$, using step 2 for
qcqs and closedness, step 5 for every torsion étale sheaf and step 6 for $b^*M\in\mathcal P_T$.
It gives the canonical derived restriction isomorphism
$$R\Gamma(T_{\mathrm{pro\acute et}},b^*M)\xrightarrow{\sim}R\Gamma((T_0)_{\mathrm{pro\acute
et}},t^*b^*M).$$
The coefficient topology here is exactly the topology in the item, in particular all continuous
$\Omega$-valued functions. This step uses the stated coefficient-transfer obligation, not a
replacement by complete or solid coefficients.
Uses: lem-sfb-closed-torsion-rigidity-serre-transfer.

8. Finally identify the source of this map with the derived evaluation at the object $X_W$ of
$X_{\mathrm{pro\acute et}}$. Since $b:T\to X$ is an object of $X_{\mathrm{pro\acute et}}$, the
weakly étale localization theorem identifies $T_{\mathrm{pro\acute et}}$ with
$X_{\mathrm{pro\acute et}}/T$. Use the section-ring reconstruction to work with an actual ring
sheaf. The ring-sheaf module category is Grothendieck, so choose a K-injective resolution $I$ of
$M[0]$. Then slice restriction remains K-injective by the ringed slice theorem, and evaluation
$I(T)$ equals global sections of $I|_T$. Thus the same complex represents $R\Gamma(X_W,M)$ and
$R\Gamma(T,b^*M)$. The inverse-image composition comparison identifies $t^*b^*M$ with $a^*M$.
The underived section unit sends a section over $T$ to its restriction on $T_0$ in both
descriptions; applying it to $I|_T$ and then a resolution of $t^*(I|_T)$ gives the same derived
arrow. This identifies the isomorphism of step 7 with the map asserted in the item, in
$D(\mathbf{Ab})$.
Uses: lem-weil-proetale-weakly-etale-localization, lem-sfb-internal-module-operations-transport,
lem-sbc-ringed-topos-sheaf-slice-derived-comparison, sk-def-sfb-module-pushforward-pullback,
lem-weil-pbc-ring-sheaves-grothendieck, lem-sfb-grothendieck-k-injective.
-/
theorem proper_wContractible_closedFibre_rigidity
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y) [IsProper f]
    (R : Type u) [CommRing R] [IsWContractibleRing R]
    (w : Spec (CommRingCat.of R) ⟶ Y) [WeaklyEtale w] :
    IsAffine (wContractibleClosedPointScheme R) ∧
    IsReduced (wContractibleClosedPointScheme R) ∧
    (∀ p : PrimeSpectrum (R ⧸ Ideal.jacobson (⊥ : Ideal R)), p.asIdeal.IsMaximal) ∧
    IsWContractibleRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)) ∧
    (∀ c : wContractibleClosedPointScheme R,
      IsSepClosed ((wContractibleClosedPointScheme R).residueField c)) ∧
    IsClosedImmersion (wContractibleClosedPointImmersion R) ∧
    Set.range (wContractibleClosedPointImmersion R) =
      closedPoints (Spec (CommRingCat.of R)) ∧
    ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible Λ X) M →
      IsIso ((properClosedFibreDerivedRestriction Λ f R w).app
        ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  have hhen := (RingTheory.wcontractible_jacobson_henselian.{u, u} R).1
  let := hhen
  have hC : IsWContractibleRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)) :=
    (henselian_lisse_rigidity Λ R (Ideal.jacobson ⊥)).2.1.mp inferInstance
  have : _root_.IsReduced (R ⧸ Ideal.jacobson (⊥ : Ideal R)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.isRadical_jacobson _)
  have hi : IsClosedImmersion (wContractibleClosedPointImmersion R) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨inferInstance, inferInstance, jacobson_quotient_maximal R, hC,
    jacobson_quotient_residue R hC, hi, ?_, ?_⟩
  · change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.jacobson (⊥ : Ideal R)))) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, jacobson_zeroLocus_closedPoints R]
    rfl
  · intro M hM
    let i := wContractibleClosedPointImmersion R
    let b := pullback.fst f w
    let t := properClosedFibreMap f R w
    let a := pullback.fst f (i ≫ w)
    let p := pullback.snd f w
    let p₀ := pullback.snd f (i ≫ w)
    have ht : t ≫ b = a := pullback.lift_fst _ _ _
    have htp : t ≫ p = p₀ ≫ i := pullback.lift_snd _ _ _
    have sq : IsPullback t p₀ p i := by
      apply IsPullback.of_right _ htp (IsPullback.of_hasPullback f w)
      change IsPullback (t ≫ b) p₀ f (i ≫ w)
      rw [ht]
      exact IsPullback.of_hasPullback f (i ≫ w)
    have : IsClosedImmersion t :=
      MorphismProperty.of_isPullback sq.flip hi
    have : CompactSpace (pullback f w : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace p
    have : QuasiSeparatedSpace (pullback f w : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated p
    have : CompactSpace (pullback f (i ≫ w) : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace p₀
    have : QuasiSeparatedSpace (pullback f (i ≫ w) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated p₀
    apply (weaklyEtale_derived_evaluation_restriction_iff Λ b t a ht _).mpr
    apply (NatTrans.isIso_app_iff_of_iso (torsionRigidityDerivedRestriction Λ t)
      (((upperStar Λ b).mapDerivedCategorySingleFunctor 0).app M)).mpr
    exact closed_torsion_rigidity_serre_transfer Λ ℓ hΛ t
      (fun F hF q ↦ Etale.proper_wContractible_torsion_rigidity R p t p₀ sq F hF q)
      ((upperStar Λ b).obj M) (pullback_serre_to_qcqs Λ b M hM)

end AlgebraicGeometry.ProEtale.CondensedRing
