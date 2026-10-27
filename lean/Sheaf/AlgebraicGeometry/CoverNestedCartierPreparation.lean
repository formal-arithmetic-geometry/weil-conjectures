/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Blowup.AdmissibleBlowup
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite-cover preparation with two Cartier boundaries

Source: Stacks Project, Morphisms, Tags 035H, 035I, 035K, 035B; Divisors,
Tags 02OS and 0809 (blueprint: lem-sfb-cover-nested-cartier-preparation).

The normalization is the existing `Scheme.normalizationIn`. The residue-field algebra
instance below installs the canonical structure obtained from the generic-fibre projection.
The field identifications are isomorphisms of field spectra commuting with their generic
point morphisms; in particular they remember the embeddings of the base function field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The canonical function-field algebra on the residue field of a point of the generic
fibre of a cover. This is the existing affine-spectrum equivalence applied to the point
morphism followed by the second fibre-product projection, with `RingHom.toAlgebra`.
Source: Stacks Project, Morphisms, Tag 02GL, and the generic-fibre construction in
Tags 035H and 035I (blueprint: lem-sfb-cover-nested-cartier-preparation). -/
noncomputable instance Scheme.coverGenericResidueAlgebra
    {T : Scheme.{u}} [IsIntegral T] {S H : Scheme.{u}} (c : H ⟶ S)
    (η : Spec T.functionField ⟶ S) (x : (pullback c η : Scheme.{u})) :
    Algebra T.functionField ((pullback c η).residueField x) :=
  (Spec.homEquiv ((pullback c η).fromSpecResidueField x ≫ pullback.snd c η)).hom.toAlgebra

private theorem finite_residue_of_etale_field {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K))
    [Etale f] (x : Y) :
    let i := Spec.homEquiv (Y.fromSpecResidueField x ≫ f)
    letI := i.hom.toAlgebra
    Module.Finite K (Y.residueField x) := by
  let i := Spec.homEquiv (Y.fromSpecResidueField x ≫ f)
  let := i.hom.toAlgebra
  have : IsClosedImmersion ((Spec (.of K)).fromSpecResidueField (f x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
  have : Surjective ((Spec (.of K)).fromSpecResidueField (f x)) :=
    ⟨fun z ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective
    ((Spec (.of K)).fromSpecResidueField (f x))
  have : Etale (Spec.map (f.residueFieldMap x)) :=
    HasRingHomProperty.Spec_iff.mpr (f.etale_residueFieldMap x)
  have : Etale (Y.fromSpecResidueField x ≫ f) := by
    rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x]
    infer_instance
  have heq : Spec.map i = Y.fromSpecResidueField x ≫ f :=
    Spec.homEquiv.symm_apply_apply _
  have : Etale (Spec.map i) := heq ▸ ‹Etale (Y.fromSpecResidueField x ≫ f)›
  have : Algebra.Etale K (Y.residueField x) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact HasRingHomProperty.Spec_iff.mp ‹Etale (Spec.map i)›
  exact Algebra.FormallyUnramified.finite_of_free _ _

private theorem normalization_open_lift {Y T H : Scheme.{u}} (f : Y ⟶ T)
    [QuasiCompact f] [QuasiSeparated f]
    (S : T.Opens) (a : Y ⟶ H) (c : H ⟶ S.toScheme) [IsIntegralHom c]
    (hf : f = a ≫ c ≫ S.ι) :
    ∃ d : (f.fromNormalization ⁻¹ᵁ S).toScheme ⟶ H,
      d ≫ c = f.fromNormalization ∣_ S := by
  let p := pullback.snd f S.ι
  let a' := pullback.fst f S.ι ≫ a
  have hp : p = a' ≫ c := by
    apply (cancel_mono S.ι).1
    dsimp [p, a']
    simpa only [Category.assoc, ← hf] using (pullback.condition (f := f) (g := S.ι)).symm
  let e := (isPullback_morphismRestrict f.fromNormalization S).flip.isoPullback
  refine ⟨e.hom ≫ inv (f.normalizationPullback S.ι) ≫ p.normalizationDesc a' c hp, ?_⟩
  rw [Category.assoc, Category.assoc, Scheme.Hom.normalizationDesc_comp]
  rw [← f.normalizationPullback_snd S.ι, IsIso.inv_hom_id_assoc]
  exact (isPullback_morphismRestrict f.fromNormalization S).flip.isoPullback_hom_snd

private theorem dominant_of_iso_restrict {B X : Scheme.{u}} [IsIntegral X]
    (b : B ⟶ X) (U : X.Opens) (hU : (U : Set X).Nonempty) [IsIso (b ∣_ U)] :
    IsDominant b := by
  refine ⟨(U.isOpen.dense hU).mono ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := (b ∣_ U).surjective ⟨x, hx⟩
  refine ⟨y.val, ?_⟩
  have h := congrArg (fun z ↦ U.ι z) hy
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι] at h
  exact h

private theorem generic_iso_of_open {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    (i : U ⟶ X) [IsOpenImmersion i] :
    ∃ e : Spec X.functionField ≅ Spec U.functionField,
      e.hom ≫ U.fromSpecFunctionField ≫ i = X.fromSpecFunctionField := by
  let e : Spec X.functionField ≅ Spec U.functionField :=
    (Scheme.Spec.mapIso i.functionFieldIso.op).symm
  have hh : Spec.map i.functionFieldIso.hom ≫ X.fromSpecFunctionField =
      U.fromSpecFunctionField ≫ i := by
    simp only [Scheme.Hom.functionFieldIso, Iso.trans_hom, asIso_hom,
      Spec.map_comp, Category.assoc, Scheme.fromSpecFunctionField,
      TopCat.Presheaf.stalkCongr_hom, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  refine ⟨e, ?_⟩
  change Spec.map i.functionFieldIso.inv ≫ U.fromSpecFunctionField ≫ i = _
  rw [← hh, ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

private theorem generic_iso_of_iso_restrict {B X : Scheme.{u}} [IsIntegral B]
    [IsIntegral X] (b : B ⟶ X) (U : X.Opens) (hU : (U : Set X).Nonempty)
    [IsIso (b ∣_ U)] :
    ∃ e : Spec X.functionField ≅ Spec B.functionField,
      e.hom ≫ B.fromSpecFunctionField ≫ b = X.fromSpecFunctionField := by
  let V := b ⁻¹ᵁ U
  have : Nonempty U.toScheme := ⟨⟨hU.some, hU.some_mem⟩⟩
  have : Nonempty V.toScheme := Nonempty.map (inv (b ∣_ U)) inferInstance
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]
    infer_instance
  obtain ⟨e₁, h₁⟩ := generic_iso_of_open (V.ι ≫ b)
  obtain ⟨e₂, h₂⟩ := generic_iso_of_open V.ι
  refine ⟨e₁ ≪≫ e₂.symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← h₂]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h₁

private theorem nested_boundary_model {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (U V : X.Opens) (hUV : U ≤ V)
    (hU : (U : Set X).Nonempty) :
    ∃ (B : Scheme.{u}) (_ : IsIntegral B) (b : B ⟶ X),
      IsProper b ∧ IsDominant b ∧ IsIso (b ∣_ U) ∧
      (∃ e : Spec X.functionField ≅ Spec B.functionField,
        e.hom ≫ B.fromSpecFunctionField ≫ b = X.fromSpecFunctionField) ∧
      ∃ I J : B.IdealSheafData, I.IsInvertible ∧ J.IsInvertible ∧
        (I.support : Set B) = ((b ⁻¹ᵁ U) : Set B)ᶜ ∧
        (J.support : Set B) = ((b ⁻¹ᵁ V) : Set B)ᶜ := by
  obtain ⟨A, hA, hAs⟩ :=
    X.exists_finiteType_ideal_coe_support_eq_compl_of_isLocallyNoetherian U
  have hAn : A ≠ ⊥ := by
    intro h
    have hs := hU.some_mem
    have ha : hU.some ∈ (A.support : Set X) := by simp [h]
    exact (hAs ▸ ha) hs
  have : IsIntegral A.blowup :=
    (A.isIntegral_blowup_and_isProjectiveBundle hAn (fun W ↦ hA W le_top)).1
  have : IsIso (A.blowupMap ∣_ U) := A.isIso_blowupMap_restrict (by
    rw [hAs]; exact disjoint_compl_right)
  have : IsLocallyNoetherian A.blowup :=
    LocallyOfFiniteType.isLocallyNoetherian A.blowupMap
  let V₁ := A.blowupMap ⁻¹ᵁ V
  let U₁ := A.blowupMap ⁻¹ᵁ U
  have hU₁ : (U₁ : Set A.blowup).Nonempty := by
    obtain ⟨z, -⟩ := (A.blowupMap ∣_ U).surjective ⟨hU.some, hU.some_mem⟩
    exact ⟨z.val, z.property⟩
  obtain ⟨C, hC, hCs⟩ :=
    A.blowup.exists_finiteType_ideal_coe_support_eq_compl_of_isLocallyNoetherian V₁
  have hCn : C ≠ ⊥ := by
    intro h
    have hc : hU₁.some ∈ (C.support : Set A.blowup) := by simp [h]
    exact (hCs ▸ hc) (A.blowupMap.preimage_mono hUV hU₁.some_mem)
  have : IsIntegral C.blowup :=
    (C.isIntegral_blowup_and_isProjectiveBundle hCn (fun W ↦ hC W le_top)).1
  have hCdisj : Disjoint (U₁ : Set A.blowup) (C.support : Set A.blowup) := by
    rw [hCs]
    exact disjoint_compl_right.mono_left (A.blowupMap.preimage_mono hUV)
  have : IsProper C.blowupMap := C.isProper_blowupMap fun W ↦ hC W le_top
  have : IsIso (C.blowupMap ∣_ U₁) := C.isIso_blowupMap_restrict hCdisj
  let b := C.blowupMap ≫ A.blowupMap
  have : IsIso (b ∣_ U) := by
    dsimp [b]
    rw [morphismRestrict_comp]
    infer_instance
  have : IsDominant b := dominant_of_iso_restrict b U hU
  refine ⟨C.blowup, inferInstance, b, inferInstance, inferInstance, inferInstance,
    generic_iso_of_iso_restrict b U hU, (A.comap A.blowupMap).comap C.blowupMap,
    C.comap C.blowupMap, ?_, C.isInvertible_comap_blowupMap, ?_, ?_⟩
  · exact A.isInvertible_comap_blowupMap.comap_blowupMap C
  · rw [Scheme.IdealSheafData.coe_support_comap,
      Scheme.IdealSheafData.coe_support_comap, hAs, Set.preimage_compl,
      Set.preimage_compl]
    rfl
  · rw [Scheme.IdealSheafData.coe_support_comap, hCs, Set.preimage_compl]
    rfl


/-- A prescribed generic field factor of a finite étale cover admits a finite normal model
and an integral proper modification with both nested boundary complements effective Cartier.
The open generic-point morphism `η` is characterized by `hη`; it is the structure map
implicit in the expression `H ×_S Spec k(T)`.

Source: Stacks Project, Morphisms, Tags 035H, 035I, 035K, 035B; Divisors,
Tags 02OS and 0809 (blueprint: lem-sfb-cover-nested-cartier-preparation).

Proof plan (the DAG's nine steps):

1. Apply [lem-weil-pbc-etale-fibre-discrete-separable-points] to $c$ at the generic point of $S$
   (also the generic point of $T$, since $S$ is dense open). Its residue field is $K$. Thus the
   chosen $x$ has residue field $F$ finite separable over $K$, and its point morphism supplies a
   map $\operatorname{Spec}F\to H$ over $S$. In particular the finite-extension hypothesis for
   normalization is satisfied.

2. Take $q:X\to T$ to be the normalization in $F$. Apply [lem-weil-pbc-normalization-in-residue-
   field-extension] at the generic point of $T$: $T$ is quasi-separated because it is separated,
   and $F/K$ is finite by step 1. This gives normal integral $X$ and identifies its generic point
   with $\operatorname{Spec}F$, compatibly with $K$. By [lem-fin-normalization-extension-finite],
   $q$ is finite. By [lem-weil-pbc-finite-proper], it is proper, hence closed. Its image contains
   the generic point of $T$; a closed subset containing that point is all of $T$. Therefore $q$ is
   surjective.

3. We will use the following elementary separatedness calculation for each composition below. If
   $Y\to Z\to W$ has separated factors, its diagonal factors as $Y\to Y\times_ZY\to Y\times_WY$.
   The second arrow is the base change of $\Delta_{Z/W}$, so [lem-weil-pbc-closed-immersion-base-
   change] and [lem-weil-pbc-closed-immersion-comp] make the composite a closed immersion. Hence
   separatedness composes. Also finite type composes by [lem-sfb-finite-type-composition-base-
   change]. In particular $X$ is separated and of finite type over $k$, since $q$ is proper and
   $T$ has these properties.

4. Put $U=q^{-1}S$ and $V=q^{-1}T^\circ$; they are nonempty opens of integral $X$, with
   $U\subseteq V$. The normalization construction [def-fin-normalization-extension] restricts to
   the same integral-closure affine charts on $S$, so $U$ is the normalization of $S$ in
   $\operatorname{Spec}F$. The map $\operatorname{Spec}F\to S$ is qcqs by [lem-weil-pbc-
   normalization-in-residue-field-extension] applied to $S$, which is separated as an open of $T$.
   Factor this map through $H\to S$ using step 1. The latter is integral by [pqf-lem-finite-
   integral-lft]. The statement of [lem-sbc-relative-normalization-universal-property] now gives
   $U\to H$ over $S$. This uses neither normality of $S$ nor normality of $H$.

5. Here and at the next blowup, all schemes in question are separated finite-type $k$-schemes, by
   step 3 and properness of the blowups. They are quasi-compact and quasi-separated by [lem-weil-
   pbc-qcqs-over-affine]. They are locally Noetherian by [pqf-lem-locnoeth-lft], since every ideal
   of the field $k$ is $0$ or $k$, so $\operatorname{Spec}k$ is Noetherian. By [lem-weil-pbc-
   noetherian-scheme-closed-subsets-minimal] their closed subsets satisfy the descending-chain
   condition. Consequently [lem-sfb-noetherian-space-compact-subsets] makes every open in them
   quasi-compact. These observations verify the hypotheses of the complement-ideal construction at
   each use.

6. Choose a finite-type quasi-coherent ideal $\mathcal A\subseteq\mathcal O_X$ with $V(\mathcal
   A)=X\setminus U$, using [lemma-nagata-qc-open-complement-ideal-exists]. It is nonzero because
   it restricts to the unit ideal on the nonempty $U$. Let $b_1:X_1=\operatorname{Bl}_{\mathcal
   A}X\to X$. By [lem-sfb-integral-blowup-projective-geometry], $X_1$ is integral; by [lemma-
   nagata-blowup-proper], $b_1$ is proper. By [thm-nagata-global-blowup-complement], it is an
   isomorphism over $U$, so it is dominant. The first assertion of [det-nagata-boundary-divisor-
   cartier] makes $\mathcal A_1=\mathcal A\mathcal O_{X_1}$ effective Cartier, with support
   $X_1\setminus b_1^{-1}U$.

7. By step 3, $X_1$ is separated finite type over $k$; apply step 5 to it. Put $V_1=b_1^{-1}V$, a
   nonempty open containing $b_1^{-1}U$. Choose a finite-type quasi-coherent ideal $\mathcal
   C\subseteq\mathcal O_{X_1}$ with $V(\mathcal C)=X_1\setminus V_1$ by [lemma-nagata-qc-open-
   complement-ideal-exists]. Again $\mathcal C$ is nonzero. Form
   $b_2:B=\operatorname{Bl}_{\mathcal C}X_1\to X_1$. By [lem-sfb-integral-blowup-projective-
   geometry] and [lemma-nagata-blowup-proper], $B$ is integral and $b_2$ is proper. By [thm-
   nagata-global-blowup-complement], $b_2$ is an isomorphism over $V_1$, hence over $b_1^{-1}U$.
   By the first assertion of [det-nagata-boundary-divisor-cartier], $\mathcal J_B=\mathcal
   C\mathcal O_B$ is effective Cartier with support $B\setminus(b_1b_2)^{-1}V$.

8. Apply [lemma-nagata-cartier-total-transform-blowup] to the effective Cartier ideal $\mathcal
   A_1$ and the ordinary blowup $b_2$. It gives the effective Cartier ideal $\mathcal I_B=\mathcal
   A_1\mathcal O_B$. Its support is $b_2^{-1}V(\mathcal A_1)=B\setminus(b_1b_2)^{-1}U$: on a
   neighbourhood where $\mathcal A_1=(a)$, the support is precisely the locus where the image of
   $a$ is not a unit, the inverse image of $V(a)$. Thus both required boundaries are Cartier
   simultaneously.

9. Set $b=b_1\circ b_2$ and $g=q\circ b$. By [lem-weil-pbc-proper-composition], both are proper.
   Steps 3, 6 and 7 show $B$ is separated finite type over $k$. Both blowups are isomorphisms
   above $U$, so $b^{-1}U\cong U$; these are nonempty opens of integral schemes, hence contain
   their generic points. Their generic stalks are therefore the generic stalks of $B$ and $X$, and
   the displayed isomorphism identifies their function fields over $K$. Thus $k(B)=k(X)=F$
   compatibly with $K$, and both $b$ and $g$ are dominant. Compose $b^{-1}U\cong U\to H$ from step
   4 for the required factorization through $c$. Steps 7--8 give the two support equalities after
   substituting $U=q^{-1}S$, $V=q^{-1}T^\circ$. If either complement is empty, choose its unit
   ideal; the blowup is the identity by [thm-nagata-global-blowup-complement] applied to the whole
   scheme.
-/
theorem exists_cover_nested_cartier_preparation
    {k : Type u} [Field k] (T : Scheme.{u}) [IsIntegral T]
    (t : T ⟶ Spec (.of k)) [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    (S Tcirc : T.Opens) (hST : S ≤ Tcirc)
    (hS : Dense (S : Set T)) (hTcirc : Dense (Tcirc : Set T))
    (H : Scheme.{u}) [Nonempty H] (c : H ⟶ S.toScheme)
    [IsFinite c] [Etale c] [Surjective c]
    (η : Spec T.functionField ⟶ S.toScheme) (hη : η ≫ S.ι = T.fromSpecFunctionField)
    (x : (pullback c η : Scheme.{u})) :
    FiniteDimensional T.functionField ((pullback c η).residueField x) ∧
    IsIntegral (T.normalizationIn ((pullback c η).residueField x)) ∧
    (∀ y : T.normalizationIn ((pullback c η).residueField x),
      IsDomain ((T.normalizationIn ((pullback c η).residueField x)).presheaf.stalk y) ∧
        IsIntegrallyClosed
          ((T.normalizationIn ((pullback c η).residueField x)).presheaf.stalk y)) ∧
    IsSeparated (T.fromNormalizationIn ((pullback c η).residueField x) ≫ t) ∧
    LocallyOfFiniteType (T.fromNormalizationIn ((pullback c η).residueField x) ≫ t) ∧
    QuasiCompact (T.fromNormalizationIn ((pullback c η).residueField x) ≫ t) ∧
    IsFinite (T.fromNormalizationIn ((pullback c η).residueField x)) ∧
    Surjective (T.fromNormalizationIn ((pullback c η).residueField x)) ∧
    ∃ eX : Spec ((pullback c η).residueField x) ≅
        Spec (T.normalizationIn ((pullback c η).residueField x)).functionField,
      eX.hom ≫ (T.normalizationIn ((pullback c η).residueField x)).fromSpecFunctionField =
        (T.fromSpecOfAlgebraFunctionField ((pullback c η).residueField x)).toNormalization ∧
      ∃ (B : Scheme.{u}) (_ : IsIntegral B)
        (b : B ⟶ T.normalizationIn ((pullback c η).residueField x)),
        IsSeparated ((b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ≫ t) ∧
        LocallyOfFiniteType ((b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ≫ t) ∧
        QuasiCompact ((b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ≫ t) ∧
        IsProper b ∧ IsDominant b ∧
        (∃ eB : Spec (T.normalizationIn ((pullback c η).residueField x)).functionField ≅
            Spec B.functionField,
          eB.hom ≫ B.fromSpecFunctionField ≫ b =
            (T.normalizationIn ((pullback c η).residueField x)).fromSpecFunctionField) ∧
        IsIso (b ∣_ (T.fromNormalizationIn ((pullback c η).residueField x) ⁻¹ᵁ S)) ∧
        (∃ a : (T.fromNormalizationIn ((pullback c η).residueField x) ⁻¹ᵁ S).toScheme ⟶ H,
          a ≫ c = T.fromNormalizationIn ((pullback c η).residueField x) ∣_ S) ∧
        (∃ I J : B.IdealSheafData,
          I.IsInvertible ∧ J.IsInvertible ∧
          (I.support : Set B) =
            (((b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ⁻¹ᵁ S) : Set B)ᶜ ∧
          (J.support : Set B) =
            (((b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ⁻¹ᵁ Tcirc) : Set B)ᶜ) ∧
        IsProper (b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ∧
        IsDominant (b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ∧
        ∃ a : ((b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ⁻¹ᵁ S).toScheme ⟶ H,
          a ≫ c = (b ≫ T.fromNormalizationIn ((pullback c η).residueField x)) ∣_ S := by
  have _ := hTcirc
  let F := (pullback c η).residueField x
  have hF : FiniteDimensional T.functionField F :=
    finite_residue_of_etale_field (pullback.snd c η) x
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated t
  let X := T.normalizationIn F
  let q := T.fromNormalizationIn F
  have : IsFinite q := T.isFinite_fromNormalizationIn F t
  have : IsIntegral X := inferInstance
  have hnormal (y : X) : IsDomain (X.presheaf.stalk y) ∧
      IsIntegrallyClosed (X.presheaf.stalk y) := by
    refine ⟨inferInstance, ?_⟩
    apply (T.fromSpecOfAlgebraFunctionField F).isIntegrallyClosed_stalk_normalization
    intro z
    have hz : z = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    subst z
    exact IsIntegrallyClosed.of_equiv
      (stalkClosedPointIso (.of F)).commRingCatIsoToRingEquiv.symm
  have hφdom : IsDominant (T.fromSpecOfAlgebraFunctionField F) := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_spec T]
    apply closure_mono
    apply Set.singleton_subset_iff.mpr
    refine ⟨IsLocalRing.closedPoint F, ?_⟩
    simp only [Scheme.fromSpecOfAlgebraFunctionField, Scheme.Hom.comp_apply,
      Spec_closedPoint, Scheme.fromSpecFunctionField]
    exact T.fromSpecStalk_closedPoint
  have : IsDominant q := by
    have hcomp : IsDominant
        ((T.fromSpecOfAlgebraFunctionField F).toNormalization ≫ q) := by
      change IsDominant ((T.fromSpecOfAlgebraFunctionField F).toNormalization ≫
        (T.fromSpecOfAlgebraFunctionField F).fromNormalization)
      rw [Scheme.Hom.toNormalization_fromNormalization]
      exact hφdom
    exact IsDominant.of_comp (T.fromSpecOfAlgebraFunctionField F).toNormalization q
  have : Surjective q :=
    surjective_of_isDominant_of_isClosed_range q q.isClosedMap.isClosed_range
  obtain ⟨eX, heX⟩ := T.exists_iso_toNormalization_normalizationIn F
  have hU : ((q ⁻¹ᵁ S) : Set X).Nonempty := by
    obtain ⟨z, hz⟩ := hS.nonempty
    obtain ⟨y, hy⟩ := q.surjective z
    exact ⟨y, show q y ∈ S from hy.symm ▸ hz⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (q ≫ t)
  obtain ⟨B, hB, b, hbproper, hbdom, hbiso, eB, IB, JB, hIB, hJB, hIs, hJs⟩ :=
    nested_boundary_model (q ⁻¹ᵁ S) (q ⁻¹ᵁ Tcirc) (q.preimage_mono hST) hU
  have := hB
  have := hbproper
  have := hbdom
  have := hbiso
  let a₀ := (pullback c η).fromSpecResidueField x ≫ pullback.fst c η
  have hf : T.fromSpecOfAlgebraFunctionField F = a₀ ≫ c ≫ S.ι := by
    dsimp [Scheme.fromSpecOfAlgebraFunctionField, a₀]
    simp only [Category.assoc]
    rw [pullback.condition_assoc, hη]
    have hi : Spec.map (CommRingCat.ofHom (algebraMap T.functionField F)) =
        (pullback c η).fromSpecResidueField x ≫ pullback.snd c η :=
      Spec.homEquiv.symm_apply_apply _
    rw [hi, Category.assoc]
  obtain ⟨a, ha⟩ := normalization_open_lift (T.fromSpecOfAlgebraFunctionField F)
    S a₀ c hf
  refine ⟨hF, inferInstance, hnormal, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, eX, heX, B, hB, b, inferInstance, inferInstance,
    inferInstance, hbproper, hbdom, eB, hbiso, ⟨a, ha⟩,
    ⟨IB, JB, hIB, hJB, hIs, hJs⟩, inferInstance, inferInstance, ?_⟩
  refine ⟨(b ∣_ q ⁻¹ᵁ S) ≫ a, ?_⟩
  rw [Category.assoc, ha, ← morphismRestrict_comp]

end AlgebraicGeometry
