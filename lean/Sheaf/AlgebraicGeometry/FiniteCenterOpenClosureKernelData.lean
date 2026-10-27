module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Closure and kernel data for the complement of a finite centre

Source: Stacks Project, Morphisms, Tag 01R8, lemma-quasi-compact-scheme-theoretic-image;
Properties, Tag 01PH, lemma-quasi-coherent-finite-type-ideals, affine-local converse
(blueprint: lem-trf-finite-center-open-closure-kernel-data).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem idealModule_quasicoherent {X : Scheme.{u}} (J : X.IdealSheafData) :
    J.toModules.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
    Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated J.subschemeι _
  exact Scheme.Modules.isQuasicoherent_kernel J.toPushforwardSubscheme

private theorem kernel_on_opens {A B : Scheme.{u}} (j : A ⟶ B) [QuasiCompact j]
    (V : B.Opens) : j.ker.idealOfOpens V = RingHom.ker (j.app V).hom := by
  change RingHom.ker (j.imageι.app V).hom = _
  conv_rhs => rw [← j.toImage_imageι, Scheme.Hom.comp_app, CommRingCat.hom_comp]
  exact (RingHom.ker_comp_of_injective _ (j.toImage.app_injective _)).symm

private theorem finiteIdealComplement_quasiCompact {X : Scheme.{u}}
    (I : X.IdealSheafData) [I.toModules.IsFiniteType] :
    QuasiCompact (Scheme.Opens.ι I.support.compl) := by
  have := idealModule_quasicoherent I
  apply quasiCompact_iff_forall_isAffineOpen.mpr
  intro V hV
  rw [(Scheme.Opens.ι I.support.compl).isEmbedding.isCompact_iff]
  change IsCompact ((Scheme.Opens.ι I.support.compl) ''
    ((Scheme.Opens.ι I.support.compl) ⁻¹' (V : Set X)))
  rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  have hfg : (I.ideal ⟨V, hV⟩).FG := by
    have := Scheme.Modules.finite_sections_of_finiteType I.toModules hV
    let iV : Γ(I.toModules, V) →ₗ[Γ(X, V)] Γ(X, V) :=
      { toFun := I.toModulesι.app V
        map_add' := map_add _
        map_smul' := fun r x ↦ Scheme.Modules.Hom.app_smul I.toModulesι r x }
    have he : (LinearMap.range iV : Ideal Γ(X, V)) = I.ideal ⟨V, hV⟩ :=
      SetLike.coe_injective (I.range_toModulesι_app ⟨V, hV⟩)
    rw [← he]
    exact Submodule.fg_range iV
  have hpiece : (V : Set X) ∩ (I.support.compl : Set X) =
      hV.fromSpec '' (PrimeSpectrum.zeroLocus (I.ideal ⟨V, hV⟩ : Set Γ(X, V)))ᶜ := by
    ext x
    constructor
    · rintro ⟨hxV, hxs⟩
      obtain ⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec := by
        rwa [hV.range_fromSpec]
      refine ⟨p, fun hp ↦ hxs ?_, rfl⟩
      have hm : hV.fromSpec p ∈ X.zeroLocus (I.ideal ⟨V, hV⟩ : Set Γ(X, V)) ∩ V := by
        rw [← hV.fromSpec_image_zeroLocus]
        exact ⟨p, hp, rfl⟩
      exact ((I.coe_support_inter ⟨V, hV⟩).symm ▸ hm).1
    · rintro ⟨p, hp, rfl⟩
      have hxV : hV.fromSpec p ∈ V := by
        change hV.fromSpec p ∈ (V : Set X)
        rw [← hV.range_fromSpec]
        exact ⟨p, rfl⟩
      refine ⟨hxV, fun hsupp ↦ hp ?_⟩
      have hm : hV.fromSpec p ∈ X.zeroLocus (I.ideal ⟨V, hV⟩ : Set Γ(X, V)) ∩ V :=
        (I.coe_support_inter ⟨V, hV⟩) ▸ ⟨hsupp, hxV⟩
      exact hV.fromSpec_preimage_zeroLocus (I.ideal ⟨V, hV⟩ : Set Γ(X, V)) ▸ hm.1
  rw [hpiece]
  exact ((PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr
    ⟨I.ideal ⟨V, hV⟩, hfg, rfl⟩).1).image hV.fromSpec.continuous

/-- The open `Ω = Y ×_X (X ∖ V(I))`, represented by its canonical open subscheme of `Y`.
Its inclusion is the base change of the complement inclusion.
Source: Stacks Project, Properties, Tag 01PH, and Schemes, Tag 01JY
(blueprint: lem-trf-finite-center-open-closure-kernel-data). -/
abbrev finiteCenterOpen {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) : Y.Opens :=
  f ⁻¹ᵁ I.support.compl

/-- The finite-centre complement is retrocompact; its closure is cut out by the actual
sheaf kernel. Any closed subscheme containing that open schematically densely has the
same ideal, also after a further closed embedding into an ambient scheme.

The quotient-ring identifications are on the affine basis, compatible with the canonical
quotient maps. They express the quotient as a sheaf of rings; they do not assert that
sections on an arbitrary open commute with quotient. `IsPullback hR (𝟙 _) s j` says that
`R ×_Y Ω = Ω` with its specified inclusion. Equality of closed subschemes is expressed
by an isomorphism over `Y`, as well as equality of their ideal sheaves.

Source: Stacks Project, Morphisms, Tag 01R8; Properties, Tag 01PH, affine-local converse
(blueprint: lem-trf-finite-center-open-closure-kernel-data).

Proof:
1. On each affine open of `X`, finite type gives finitely many ideal generators by
   lem-weil-pbc-quasi-coherent-finite-type-affine. The complement is their finite union
   of basic opens, which are quasi-compact by lem-weil-pbc-spec-localization-away-basic-open
   and lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact. Thus its inclusion is
   quasi-compact, including the empty union.
2. Apply lem-pc-quasi-compact-base-change and lem-weil-pbc-open-immersion-base-change
   to obtain quasi-compactness of `j`.
3. By lem-weil-pbc-scheme-image-qc-kernel the image ideal agrees with the sectionwise
   kernel on the affine basis, hence on all opens. It is quasi-coherent, and the
   closed-immersion quotient description gives the compatible quotient-ring isomorphisms.
4. The kernel restricts to zero on `Ω`. Apply lem-pc-closed-subscheme-base-change-ideal-image
   and lem-weil-pbc-closed-immersions-equal-ideal-isomorphic to obtain `S ×_Y Ω = Ω`.
   The induced `h` is a quasi-compact open immersion by base change. It is a monomorphism
   by lem-weil-pbc-open-immersion-monomorphism, so its diagonal is an isomorphism and it
   is quasi-separated.
5. lemma-nagata-scheme-image-ideal-qc makes the structure-sheaf map for the factor
   through the image injective. Its kernel is zero, so def-nagata-scheme-theoretic-image
   gives `SIm(h) = S`.
6. For `R`, its specified pullback square makes `hR` a quasi-compact open immersion.
   lem-weil-pbc-scheme-image-qc-kernel and `SIm(hR) = R` make its raw kernel zero
   on an affine basis, hence its map injective on every open.
7. Factor the map from `O_Y` through `O_R`. The last map is injective by step 6,
   so the ideal of `s` equals the kernel for `j`, namely `J`. Apply
   lem-weil-pbc-closed-immersions-equal-ideal-isomorphic to identify `R` and `S` over `Y`.
8. Closed immersions compose, locally by composition of quotient ring maps. On every
   open of `P`, factor through `O_R` and use step 6 again. The ambient kernel is the
   ideal of `s ≫ k`; the factorization through `O_Y` also identifies it with the inverse
   image of `J`. These sectionwise equalities commute with restriction.
-/
theorem finiteCenterOpen_closure_kernel_data {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) [I.toModules.IsFiniteType] :
    QuasiCompact (finiteCenterOpen f I).ι ∧
    (finiteCenterOpen f I).ι.ker.toModules.IsQuasicoherent ∧
    (∀ V : Y.Opens,
      (finiteCenterOpen f I).ι.ker.idealOfOpens V =
        RingHom.ker ((finiteCenterOpen f I).ι.app V).hom) ∧
    (∀ V : Y.affineOpens,
      ∃ e : CommRingCat.of (Γ(Y, V) ⧸ (finiteCenterOpen f I).ι.ker.ideal V) ≅
          Γ((finiteCenterOpen f I).ι.image, (finiteCenterOpen f I).ι.imageι ⁻¹ᵁ V),
        CommRingCat.ofHom (Ideal.Quotient.mk ((finiteCenterOpen f I).ι.ker.ideal V)) ≫
          e.hom = (finiteCenterOpen f I).ι.imageι.app V) ∧
    IsIso (pullback.snd (finiteCenterOpen f I).ι.imageι (finiteCenterOpen f I).ι) ∧
    IsOpenImmersion (finiteCenterOpen f I).ι.toImage ∧
    QuasiCompact (finiteCenterOpen f I).ι.toImage ∧
    QuasiSeparated (finiteCenterOpen f I).ι.toImage ∧
    IsIso (pullback.diagonal (finiteCenterOpen f I).ι.toImage) ∧
    (∀ V : (finiteCenterOpen f I).ι.image.Opens,
      Function.Injective ((finiteCenterOpen f I).ι.toImage.app V)) ∧
    IsSchemeTheoreticallyDominant (finiteCenterOpen f I).ι.toImage ∧
    (∀ (R : Scheme.{u}) (s : R ⟶ Y) [IsClosedImmersion s]
      (hR : (finiteCenterOpen f I).toScheme ⟶ R),
      IsPullback hR (𝟙 (finiteCenterOpen f I).toScheme) s (finiteCenterOpen f I).ι →
      IsSchemeTheoreticallyDominant hR →
      QuasiCompact hR ∧
      (∀ V : R.Opens, Function.Injective (hR.app V)) ∧
      s.ker = (finiteCenterOpen f I).ι.ker ∧
      (∃ e : R ≅ (finiteCenterOpen f I).ι.image,
        e.hom ≫ (finiteCenterOpen f I).ι.imageι = s) ∧
      ∀ (P : Scheme.{u}) (k : Y ⟶ P) [IsClosedImmersion k] (V : P.Opens),
        (s ≫ k).ker.idealOfOpens V =
          RingHom.ker (((finiteCenterOpen f I).ι ≫ k).app V).hom ∧
        (s ≫ k).ker.idealOfOpens V =
          Ideal.comap (k.app V).hom
            ((finiteCenterOpen f I).ι.ker.idealOfOpens (k ⁻¹ᵁ V))) := by
  have := finiteIdealComplement_quasiCompact I
  have hj : QuasiCompact (finiteCenterOpen f I).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f I.support.compl) inferInstance
  let j := (finiteCenterOpen f I).ι
  have hpb : IsIso (pullback.snd j.imageι j) := by
    have hfst : pullback.fst j.imageι j = pullback.snd j.imageι j ≫ j.toImage := by
      rw [← cancel_mono j.imageι, Category.assoc, j.toImage_imageι, pullback.condition]
    refine ⟨⟨pullback.lift j.toImage (𝟙 _) (by simp), ?_, ?_⟩⟩
    · apply pullback.hom_ext
      · simpa using hfst.symm
      · simp
    · simp
  refine ⟨hj, idealModule_quasicoherent _, kernel_on_opens _, ?_, hpb,
    inferInstance, inferInstance, inferInstance, inferInstance,
    j.toImage.app_injective, inferInstance, ?_⟩
  · intro V
    exact ⟨(j.ker.subschemeObjIso V).symm, (j.ker.subschemeι_app V).symm⟩
  · intro R s hs hR sq hd
    have hqc : QuasiCompact hR :=
      MorphismProperty.of_isPullback sq.flip hj
    have hfac : hR ≫ s = j := by simpa using sq.w
    have hker : s.ker = j.ker := by
      rw [← hfac, Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant]
    have heq : j.imageι.ker = s.ker := by simpa using hker.symm
    have hiso := IsClosedImmersion.isIso_lift j.imageι s heq
    refine ⟨hqc, hR.app_injective, hker,
      ⟨asIso (IsClosedImmersion.lift j.imageι s heq.le),
        IsClosedImmersion.lift_fac j.imageι s heq.le⟩, ?_⟩
    intro P k hk V
    have hkercomp : (s ≫ k).ker = (j ≫ k).ker := by
      calc
        (s ≫ k).ker = (hR ≫ (s ≫ k)).ker :=
          (Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant hR (s ≫ k)).symm
        _ = (j ≫ k).ker := by rw [← Category.assoc, hfac]
    refine ⟨by rw [hkercomp]; exact kernel_on_opens _ _, ?_⟩
    rw [hkercomp, kernel_on_opens, kernel_on_opens, Scheme.Hom.comp_app,
      CommRingCat.hom_comp, RingHom.comap_ker]

end AlgebraicGeometry
