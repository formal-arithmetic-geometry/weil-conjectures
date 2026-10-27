/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.TraceFormula.LciPointwiseCriterion
public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections
import Sheaf.TraceFormula.CILocalRingPrincipalNeighbourhood
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection

/-!
# A pointwise syntomic affine local model

Source: Stacks Project, Morphisms, Tag 01UE, implication (3) => (2), and the fibre-stalk
identification in lemma-syntomic-flat-fibres; Algebra, Tags 00SG, 00SY and 00SP
(blueprint: lem-trf-syntomic-pointwise-local-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem finitePresentation_neighbourhood
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : S.Opens) (hV : IsAffineOpen V) (hxV : f x ∈ V)
    (hfp : ∃ (U₀ : X.Opens) (V₀ : S.Opens),
      IsAffineOpen U₀ ∧ IsAffineOpen V₀ ∧ x ∈ U₀ ∧
        ∃ e₀ : U₀ ≤ f ⁻¹ᵁ V₀, (f.appLE V₀ U₀ e₀).hom.FinitePresentation) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
      ∃ e : U ≤ f ⁻¹ᵁ V, (f.appLE V U e).hom.FinitePresentation := by
  obtain ⟨U₀, V₀, hU₀, hV₀, hx₀, e₀, hfp₀⟩ := hfp
  let : IsAffine U₀ := hU₀
  let : IsAffine V₀ := hV₀
  have hres : LocallyOfFinitePresentation (f.resLE V₀ U₀ e₀) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V₀ U₀ e₀) |>.mpr hfp₀
  have := hres
  have : LocallyOfFinitePresentation (U₀.ι ≫ f) := by
    rw [← f.resLE_comp_ι e₀]
    infer_instance
  obtain ⟨W, hW, hxW, eW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    U₀.toScheme.isBasis_affineOpens
    (show (⟨x, hx₀⟩ : U₀) ∈ (U₀.ι ≫ f) ⁻¹ᵁ V from hxV)
  let U := U₀.ι ''ᵁ W
  have hU : IsAffineOpen U := hW.image_of_isOpenImmersion U₀.ι
  have hxU : x ∈ U := ⟨⟨x, hx₀⟩, hxW, rfl⟩
  have eU : U ≤ f ⁻¹ᵁ V := by
    rintro y ⟨z, hz, rfl⟩
    exact eW hz
  refine ⟨U, hU, hxU, eU, ?_⟩
  have hfpW := (U₀.ι ≫ f).finitePresentation_appLE hV hW eW
  have he : U₀.ι ⁻¹ᵁ U = W := U₀.ι.preimage_image_eq W
  have htop : IsIso (U₀.ι.appLE U W he.ge) := by
    change IsIso (U₀.ι.app U ≫ U₀.toScheme.presheaf.map (eqToHom he.symm).op)
    infer_instance
  rw [← Scheme.Hom.appLE_comp_appLE U₀.ι f V U W eU he.ge] at hfpW
  exact (RingHom.finitePresentation_respectsIso.cancel_right_isIso _ _).mp hfpW

private theorem presentation_on_basicOpen
    {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (U : X.Opens) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (x : X) (hx : x ∈ U) (g : Γ(X, U))
    (hg : g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
    (n c : ℕ) (h : Fin c → MvPolynomial (Fin n) Γ(S, V))
    (hh : Algebra.IsRelativeGlobalCompleteIntersectionPresentation h)
    (eh : letI := (f.appLE V U e).hom.toAlgebra
      Nonempty (Localization.Away g ≃ₐ[Γ(S, V)]
        (MvPolynomial (Fin n) Γ(S, V) ⧸ Ideal.span (Set.range h)))) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ (eW : W ≤ f ⁻¹ᵁ V) (N C : ℕ)
        (H : Fin C → MvPolynomial (Fin N) Γ(S, V)),
        Algebra.IsRelativeGlobalCompleteIntersectionPresentation H ∧
          Nonempty
            (@AlgEquiv Γ(S, V) Γ(X, W)
              (MvPolynomial (Fin N) Γ(S, V) ⧸ Ideal.span (Set.range H))
              _ _ _ (f.appLE V W eW).hom.toAlgebra _) := by
  let W := X.basicOpen g
  have eW : W ≤ f ⁻¹ᵁ V := (X.basicOpen_le g).trans e
  let := (f.appLE V U e).hom.toAlgebra
  let := (f.appLE V W eW).hom.toAlgebra
  let := (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq' (by
      exact congrArg CommRingCat.Hom.hom (f.appLE_map e
        (homOfLE (X.basicOpen_le g)).op).symm)
  have := hU.isLocalization_basicOpen g
  obtain ⟨eh⟩ := eh
  refine ⟨W, hU.basicOpen g, ?_, eW, n, c, h, hh, ⟨?_⟩⟩
  · have hm : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ W := by
      change hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ W
      rwa [hU.fromSpec_preimage_basicOpen]
    have he : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) = x :=
      hU.fromSpec_primeIdealOf ⟨x, hx⟩
    exact he ▸ hm
  · exact ((IsLocalization.algEquiv (Submonoid.powers g) Γ(X, W)
      (Localization.Away g)).restrictScalars Γ(S, V)).trans eh

private theorem affine_fibre_ci
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : S.Opens) (hV : IsAffineOpen V)
    (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) (e : U ≤ f ⁻¹ᵁ V)
    (hfp : (f.appLE V U e).hom.FinitePresentation)
    (hci : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra (S.residueField (f x)) A)
      (_ : IsLocalRing A) (_ : IsNoetherianRing A),
      IsRegularLocalRing A ∧ Algebra.EssFiniteType (S.residueField (f x)) A ∧
        ∃ rs : List A, RingTheory.Sequence.IsRegular A rs ∧
          Nonempty
            (@AlgEquiv (S.residueField (f x))
              (A ⧸ Ideal.span (Set.range (fun i : Fin rs.length => rs.get i)))
              ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) _ _ _ _
              (((Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
                (f.fiberToSpecResidueField (f x)).appLE ⊤ ⊤ le_top ≫
                (f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) trivial).hom.toAlgebra))) :
    let := (f.appLE V U e).hom.toAlgebra
    let q := hU.primeIdealOf ⟨x, hx⟩
    ∃ h : (q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, U))).Fiber Γ(X, U),
      h ∉ (PrimeSpectrum.preimageEquivFiber Γ(S, V) Γ(X, U)
        (q.comap (algebraMap Γ(S, V) Γ(X, U))) ⟨q, rfl⟩).asIdeal ∧
      Algebra.IsGlobalCompleteIntersection
        (q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, U))).ResidueField
        (Localization.Away h) := by
  let R := Γ(S, V)
  let B := Γ(X, U)
  let k := S.residueField (f x)
  let := (f.appLE V U e).hom.toAlgebra
  let q := hU.primeIdealOf ⟨x, hx⟩
  let p := q.comap (algebraMap R B)
  have hp : p = hV.primeIdealOf ⟨f x, e hx⟩ :=
    IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hx
  let := S.presheaf.algebra_section_stalk ⟨f x, e hx⟩
  have hloc : IsLocalization.AtPrime (S.presheaf.stalk (f x)) p.asIdeal := by
    simpa only [hp] using hV.isLocalization_stalk ⟨f x, e hx⟩
  let := (S.evaluation V (f x) (e hx)).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f x)) k := (S.residue (f x)).hom.toAlgebra
  have : IsScalarTower R (S.presheaf.stalk (f x)) k :=
    IsScalarTower.of_algebraMap_eq' rfl
  let ep := IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (S.presheaf.stalk (f x))
  let ek : p.asIdeal.ResidueField ≃ₐ[R] k := IsLocalRing.ResidueField.mapAlgEquiv ep
  let Y := f.fiber (f x)
  let i := f.fiberι (f x)
  let t := f.fiberToSpecResidueField (f x)
  let W := i ⁻¹ᵁ U
  have hz : f.asFiber x ∈ W := by
    change i (f.asFiber x) ∈ U
    simpa [i] using hx
  have hbase : (S.fromSpecResidueField (f x)) ⁻¹ᵁ V = ⊤ :=
    S.preimage_fromSpecResidueField (e hx)
  have HW := Scheme.Hom.isPullback_resLE
    (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x)))
    hbase.ge e (show W = i ⁻¹ᵁ U ⊓ t ⁻¹ᵁ ⊤ by simp [W])
  have hW : IsAffineOpen W := by
    let : IsAffine U := hU
    let : IsAffine V := hV
    let : IsAffine (⊤ : (Spec k).Opens) := isAffineOpen_top _
    exact .of_isIso HW.isoPullback.hom
  let b : B ⟶ Γ(Y, W) := i.appLE U W le_rfl
  let a : k ⟶ Γ(Y, W) := (Scheme.ΓSpecIso k).inv ≫ t.appLE ⊤ W le_top
  have H := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x))) hbase.ge e
    (show W = i ⁻¹ᵁ U ⊓ t ⁻¹ᵁ ⊤ by simp [W])).mp
    (isIso_pushoutSection_of_isAffineOpen
      (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x))) hbase.ge e
      (show W = i ⁻¹ᵁ U ⊓ t ⁻¹ᵁ ⊤ by simp [W]) hV (isAffineOpen_top _) hU)
  have H' : IsPushout (f.appLE V U e) (S.evaluation V (f x) (e hx)) b a := by
    refine H.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso k) (Iso.refl _)
      (by simp) ?_ (by simp [b, i, Scheme.Hom.fiberι]) (by simp [a, t,
        Scheme.Hom.fiberToSpecResidueField])
    exact S.fromSpecResidueField_appLE_ΓSpecIso_hom (f x) V (e hx)
  let K := p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber B
  let := a.hom.toAlgebra
  let := ek.toRingHom.toAlgebra
  let : Algebra K Γ(Y, W) := ((algebraMap k Γ(Y, W)).comp ek.toRingHom).toAlgebra
  have : IsScalarTower K k Γ(Y, W) := IsScalarTower.of_algebraMap_eq' rfl
  let aK : CommRingCat.of K ⟶ Γ(Y, W) := CommRingCat.ofHom
    ((algebraMap k Γ(Y, W)).comp ek.toRingHom)
  have HK : IsPushout (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap R K)) b aK := by
    exact H'.of_iso (Iso.refl _) (Iso.refl _) ek.symm.toCommRingCatIso (Iso.refl _)
      (by rfl) (by ext r; exact ek.symm.commutes r)
      (by simp) (by
        ext r
        change a r = a (ek (ek.symm r))
        rw [ek.apply_symm_apply])
  let T := CommRingCat.isPushout_tensorProduct R K B
  let eF : CommRingCat.of F ≅ Γ(Y, W) := T.isoPushout ≪≫ HK.flip.isoPushout.symm
  have eFb : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := K)
      (B := B)).toRingHom ≫ eF.hom = b := by
    simp only [eF, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
      IsPushout.inr_isoPushout_hom]
    rw [Iso.comp_inv_eq, IsPushout.inr_isoPushout_hom]
  have eFa : CommRingCat.ofHom (algebraMap K F) ≫ eF.hom = aK := by
    simp only [eF, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
      IsPushout.inl_isoPushout_hom]
    rw [Iso.comp_inv_eq, IsPushout.inl_isoPushout_hom]
  let ef : F ≃ₐ[K] Γ(Y, W) :=
    { eF.commRingCatIsoToRingEquiv with
      commutes' := fun r ↦ congr($(eFa).hom r) }
  let z := f.asFiber x
  let qW := hW.primeIdealOf ⟨z, hz⟩
  let Q := PrimeSpectrum.preimageEquivFiber R B p ⟨q, rfl⟩
  have hQ : Q = qW.comap ef.toRingHom := by
    apply (PrimeSpectrum.preimageEquivFiber R B p).symm.injective
    apply Subtype.ext
    rw [show (PrimeSpectrum.preimageEquivFiber R B p).symm Q = ⟨q, rfl⟩ from
      (PrimeSpectrum.preimageEquivFiber R B p).symm_apply_apply ⟨q, rfl⟩]
    change q = (qW.comap ef.toRingHom).comap Algebra.TensorProduct.includeRight.toRingHom
    rw [← PrimeSpectrum.comap_comp_apply]
    change q = qW.comap (eF.hom.hom.comp Algebra.TensorProduct.includeRight.toRingHom)
    rw [show eF.hom.hom.comp Algebra.TensorProduct.includeRight.toRingHom = b.hom from
      congrArg CommRingCat.Hom.hom eFb]
    have hi := IsAffineOpen.comap_primeIdealOf_appLE U hU W hW le_rfl hz (f := i)
    simpa only [qW, q, z, i, Scheme.Hom.fiberι_asFiber] using hi.symm
  let D := Y.presheaf.stalk z
  let := Y.presheaf.algebra_section_stalk ⟨z, hz⟩
  have := hW.isLocalization_stalk ⟨z, hz⟩
  let akD : k ⟶ D := (Scheme.ΓSpecIso k).inv ≫ t.appLE ⊤ ⊤ le_top ≫
    Y.presheaf.germ ⊤ z trivial
  let := akD.hom.toAlgebra
  have haD : a ≫ Y.presheaf.germ W z hz = akD := by
    dsimp only [a, akD]
    rw [← t.appLE_map le_top (homOfLE le_top).op]
    simp only [Category.assoc]
    rw [show (f.fiber (f x)).presheaf.map (homOfLE le_top).op ≫
        Y.presheaf.germ W z hz = Y.presheaf.germ ⊤ z trivial from
      Y.presheaf.germ_res (homOfLE le_top) z hz]
  have : IsScalarTower k Γ(Y, W) D :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom haD.symm)
  let : Algebra K D := ((algebraMap k D).comp ek.toRingHom).toAlgebra
  have : IsScalarTower K k D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K Γ(Y, W) D := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro r
    change akD (ek r) = (Y.presheaf.germ W z hz) (a (ek r))
    exact congr($(haD).hom (ek r)).symm)
  let eL : Localization.AtPrime Q.asIdeal ≃ₐ[K] D :=
    (Localization.localAlgEquiv Q.asIdeal qW.asIdeal ef congr($(hQ).asIdeal)).trans
      ((IsLocalization.algEquiv qW.asIdeal.primeCompl
        (Localization.AtPrime qW.asIdeal) D).restrictScalars K)
  obtain ⟨A, hA, aA, hlA, hnA, hrA, hfA, rs, hreg, ⟨eA⟩⟩ := hci
  let := hA
  let := aA
  have := hlA
  have := hnA
  have := hrA
  have := hfA
  let : Algebra K A := ((algebraMap k A).comp ek.toRingHom).toAlgebra
  have : IsScalarTower K k A := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType K k := Algebra.FiniteType.of_surjective
    (Algebra.ofId K k) ek.surjective
  have : Algebra.EssFiniteType K A := Algebra.EssFiniteType.comp K k A
  have hspan : Ideal.span (Set.range (fun j : Fin rs.length ↦ rs.get j)) =
      Ideal.ofList rs := by
    congr 1
    ext r
    simp only [Set.mem_range, Set.mem_ofPred_eq, List.mem_iff_get]
  let eA' : (A ⧸ Ideal.ofList rs) ≃ₐ[K] D := by
    rw [hspan] at eA
    exact eA.restrictScalars K
  have hmax : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal A := by
    have hproper : Ideal.ofList rs ≠ ⊤ := by
      intro ht
      have ht' := hreg.top_ne_smul
      simp only [ht, Submodule.top_smul] at ht'
      exact ht' rfl
    exact fun r hr ↦ (IsLocalRing.le_maximalIdeal hproper)
      (Ideal.subset_span hr)
  have : Algebra.FinitePresentation R B := hfp
  have : Algebra.FiniteType R B := inferInstance
  have hfinite : (algebraMap K F).FiniteType := RingHom.finiteType_algebraMap.mpr
    (inferInstance : Algebra.FiniteType K F)
  exact TraceFormula.ciLocalRingPrincipalNeighbourhood K F hfinite Q.asIdeal A rs
    hreg hmax (eL.trans eA'.symm)

/-- A flat local map of stalks, finite presentation at the given point, and a
complete-intersection fibre local ring give an affine relative-global-complete-intersection
presentation over any prescribed affine neighbourhood of the image.
Source: Stacks Project, Morphisms, Tag 01UE (3) => (2), and Algebra, Tags 00SG, 00SY, 00SP
(blueprint: lem-trf-syntomic-pointwise-local-model).

The hypothesis `hfp` expands the pointwise clause of
`def-sbc-locally-finite-presentation`, rather than requiring finite presentation everywhere.
The hypothesis `hci` is the local-ring condition in `lem-trf-lci-pointwise-criterion`, with
its scalar map induced by the canonical fibre projection. The coefficient ring in the
conclusion is `Γ(S, V)` and the algebra structure on `Γ(X, U)` is the actual map `f.appLE`.
For an affine open these section rings are its canonical affine coordinates.
The presentation predicate includes the asserted dimension of every nonzero fibre.

Proof:
1. Choose affine neighbourhoods `U₀`, `V₀` witnessing `hfp`. The restriction to `U₀` is
   locally of finite presentation: the same pair witnesses it at each of its points.
   Choose an affine neighbourhood of `x` inside `U₀ ∩ f⁻¹(V)` using
   `lem-weil-pbc-affine-opens-basis`. Apply
   `lem-weil-pbc-lfp-affine-opens-finite-presentation` to that restriction and the prescribed
   `V`. This yields a finitely presented coordinate map `R → B` over that exact `V`.
2. The affine stalk identifications identify its localized map `R_p → B_q` with
   `f.stalkMap x`, so it is flat by `hflat` (`def-weil-flat-morphism`).
3. The affine fibre calculation (`def-pc-scheme-fibre`) identifies the localization of
   `B ⊗[R] κ(p)` at the canonical fibre prime with the stalk at `f.asFiber x`. Its local
   complete-intersection presentation is `hci`. Apply
   `lem-trf-ci-local-ring-principal-neighbourhood` to get a principal global-complete-
   intersection neighbourhood of that fibre prime (Stacks Algebra, Tag 00SG).
4. Apply `lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection` with `g=1`
   to the finitely presented map of step 1, flatness of step 2 and the fibre neighbourhood
   of step 3. It gives `g' ∉ q` and the required relative global complete intersection
   polynomial quotient isomorphic as an `R`-algebra to `B[1/g']` (Tag 00SY).
   The principal open `D(g')` is an affine neighbourhood of `x` still mapping into `V`.
5. By `def-weil-pbc-relative-global-complete-intersection`, the specified quotient has
   dimension `n-c` in each nonzero fibre (Tag 00SP), giving the final clause.
-/
theorem syntomic_pointwise_local_model
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : S.Opens) (hV : IsAffineOpen V) (hxV : f x ∈ V)
    (hfp : ∃ (U₀ : X.Opens) (V₀ : S.Opens),
      IsAffineOpen U₀ ∧ IsAffineOpen V₀ ∧ x ∈ U₀ ∧
        ∃ e₀ : U₀ ≤ f ⁻¹ᵁ V₀, (f.appLE V₀ U₀ e₀).hom.FinitePresentation)
    (hflat : (f.stalkMap x).hom.Flat)
    (hci : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra (S.residueField (f x)) A)
      (_ : IsLocalRing A) (_ : IsNoetherianRing A),
      IsRegularLocalRing A ∧ Algebra.EssFiniteType (S.residueField (f x)) A ∧
        ∃ rs : List A, RingTheory.Sequence.IsRegular A rs ∧
          Nonempty
            (@AlgEquiv (S.residueField (f x))
              (A ⧸ Ideal.span (Set.range (fun i : Fin rs.length => rs.get i)))
              ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) _ _ _ _
              (((Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
                (f.fiberToSpecResidueField (f x)).appLE ⊤ ⊤ le_top ≫
                (f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) trivial).hom.toAlgebra))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ (e : U ≤ f ⁻¹ᵁ V) (n c : ℕ) (h : Fin c → MvPolynomial (Fin n) Γ(S, V)),
        Algebra.IsRelativeGlobalCompleteIntersectionPresentation h ∧
          Nonempty
            (@AlgEquiv Γ(S, V) Γ(X, U)
              (MvPolynomial (Fin n) Γ(S, V) ⧸ Ideal.span (Set.range h))
              _ _ _ (f.appLE V U e).hom.toAlgebra _) := by
  obtain ⟨U, hU, hx, e, hfpU⟩ := finitePresentation_neighbourhood f x V hV hxV hfp
  let := (f.appLE V U e).hom.toAlgebra
  let q := hU.primeIdealOf ⟨x, hx⟩
  have hq : q.comap (algebraMap Γ(S, V) Γ(X, U)) = hV.primeIdealOf ⟨f x, e hx⟩ :=
    IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hx
  have hflatq : (Localization.localRingHom
      (q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, U))) q.asIdeal
      (algebraMap Γ(S, V) Γ(X, U)) rfl).Flat := by
    have hf := (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f V hV U hU e hx)).mp hflat
    have key (p : Ideal Γ(S, V)) [p.IsPrime]
        (hp : p = q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, U)))
        (hf : (Localization.localRingHom p q.asIdeal
          (algebraMap Γ(S, V) Γ(X, U)) hp).Flat) :
        (Localization.localRingHom (q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, U)))
          q.asIdeal (algebraMap Γ(S, V) Γ(X, U)) rfl).Flat := by
      subst p
      exact hf
    exact key _ congr($(hq).asIdeal).symm hf
  have hciq : ∃ h : (q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, U))).Fiber Γ(X, U),
      h ∉ (PrimeSpectrum.preimageEquivFiber Γ(S, V) Γ(X, U)
        (q.comap (algebraMap Γ(S, V) Γ(X, U))) ⟨q, rfl⟩).asIdeal ∧
      Algebra.IsGlobalCompleteIntersection
        (q.asIdeal.comap (algebraMap Γ(S, V) Γ(X, U))).ResidueField
        (Localization.Away h) := by
    exact affine_fibre_ci f x V hV U hU hx e hfpU hci
  have hfp' : Algebra.FinitePresentation Γ(S, V) Γ(X, U) := hfpU
  have : Algebra.FinitePresentation Γ(S, V) (Localization.Away (1 : Γ(X, U))) :=
    Algebra.FinitePresentation.trans Γ(S, V) Γ(X, U) _
  obtain ⟨g, hg, n, c, h, hh, eh⟩ :=
    Algebra.exists_relativeGlobalCompleteIntersection_of_syntomicAtPrime q
      ⟨1, q.asIdeal.one_notMem, inferInstance⟩ hflatq hciq
  exact presentation_on_basicOpen f V U hU e x hx g hg n c h hh eh

end AlgebraicGeometry
