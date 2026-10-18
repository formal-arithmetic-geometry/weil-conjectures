/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal
import WeilConjectures.ConstructibleSheaf.FiniteTypePushforward
import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
import Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.FiniteLocalAbelianForget
import Sheaf.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.GroupTheory.Schreier

/-!
# Constructible coefficients on the projective line

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-line-constructible.md`,
order 1618 (blueprint: thm-fin-projective-line-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Forgetting to sets commutes with the inverse image on the small étale site.
private noncomputable def abelianSetPullbackIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.etaleSetPullback g).obj
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) ≅
    (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
      ((upperStar AddCommGrpCat.{u + 1} g).obj F) := by
  let B := MorphismProperty.Over.pullback @Etale ⊤ g
  let U := CategoryTheory.forget AddCommGrpCat.{u + 1}
  let (V : Y.Etaleᵒᵖ) : IsFiltered (CostructuredArrow B.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence B V.unop)
  let : Limits.PreservesFilteredColimitsOfSize.{u, u + 1} U :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} U
  let (V : Y.Etaleᵒᵖ) : U.PreservesPointwiseLeftKanExtensionAt F.obj B.op V := by
    infer_instance
  have : U.PreservesLeftKanExtension F.obj B.op := by infer_instance
  have : Y.smallEtaleTopology.PreservesSheafification U := by infer_instance
  let e := U.leftKanExtensionCompIsoOfPreserves F.obj B.op
  exact (presheafToSheaf Y.smallEtaleTopology (Type (u + 1))).mapIso e.symm ≪≫
    (sheafComposeNatIso Y.smallEtaleTopology U
      (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (sheafificationAdjunction Y.smallEtaleTopology (Type (u + 1)))).app
        (B.op.leftKanExtension F.obj)

private theorem constructibleAbelian_underlyingSets {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsConstructibleAbelianSheaf F) :
    Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) := by
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨S, _, hS⟩ := hF
  refine ⟨S, fun i ↦ ?_⟩
  let G := (upperStar AddCommGrpCat.{u + 1} (S.immersion i)).obj F
  obtain ⟨V, hV⟩ := hS i
  have hlocal : Scheme.IsLocallyConstantSheaf G := by
    refine ⟨⟨⟨V, fun j ↦ ?_⟩⟩⟩
    rw [Scheme.isConstant_over_iff_upperStar]
    obtain ⟨A, _, ⟨e⟩⟩ := hV j
    exact Sheaf.isConstant_of_iso _ e
  have hfinite (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S.domain i) :
      Finite (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G) := by
    obtain ⟨j, x, hx⟩ := V.exists_eq (s default)
    have : Etale (V.f j) := V.map_prop j
    obtain ⟨s', hs', _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (V.f j) s x hx
    obtain ⟨A, hA, ⟨e⟩⟩ := hV j
    let es := ((upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} (V.f j) s').app G).symm ≪≫
      (Scheme.pointSmallEtale s').sheafFiber.mapIso e ≪≫
      (Scheme.pointSmallEtale s').sheafFiberConstantSheafIso A
    have ht : Finite (((Scheme.pointSmallEtale (s' ≫ V.f j)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G) :=
      @Finite.of_equiv _ _ hA
        ((CategoryTheory.forget AddCommGrpCat.{u + 1}).mapIso es).toEquiv.symm
    rwa [hs'] at ht
  let e := (abelianSetPullbackIso (S.immersion i) F).symm
  obtain ⟨⟨V', hV'⟩, hfin⟩ :=
    (Scheme.finite_local_abelian_forget_iff G).2 ⟨hlocal, hfinite⟩
  refine ⟨⟨V', fun j ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · have := hV' j
    exact Sheaf.isConstant_congr _
      (((S.domain i).smallEtaleTopology.overPullback (Type (u + 1))
        (V'.etalePrecoverageToEtale j)).mapIso e)
  · exact (hfin.isFinitelyGenerated_sheafFiber Ω s).of_iso
      ((Scheme.pointSmallEtale s).sheafFiber.mapIso e)

private theorem module_constructible_of_abelian
    {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F ≅ G)
    (hG : Scheme.IsConstructibleAbelianSheaf G) : Scheme.IsConstructibleSheaf F := by
  have hsets := constructibleAbelian_underlyingSets G hG
  have hF : Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) := by
    obtain ⟨S, hS⟩ := hsets
    refine ⟨S, fun i ↦ ?_⟩
    let es := (Scheme.etaleSetPullback (S.immersion i)).mapIso
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e.symm)
    obtain ⟨⟨V, hV⟩, hfin⟩ := hS i
    refine ⟨⟨V, fun j ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
    · have := hV j
      exact Sheaf.isConstant_congr _
        (((S.domain i).smallEtaleTopology.overPullback (Type (u + 1))
          (V.etalePrecoverageToEtale j)).mapIso es)
    · exact (hfin.isFinitelyGenerated_sheafFiber Ω s).of_iso
        ((Scheme.pointSmallEtale s).sheafFiber.mapIso es)
  exact Scheme.isConstructibleSheaf_of_finite_coefficient_underlying_sets Λ F hF ⊥
    (Finite.of_surjective (Ideal.Quotient.mk ⊥) Ideal.Quotient.mk_surjective)
    (fun U r hr m ↦ by
      have : r = 0 := hr
      subst r
      exact zero_smul Λ m)

private theorem constantModule_curve_constructible
    (k : Type u) [Field k] (X S : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] (f : X ⟶ S) [IsProjective f.left]
    (hdim : ∀ s : S.left,
      topologicalKrullDim (Limits.pullback f.left
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.left.residueField s) (AlgebraicClosure (S.left.residueField s)))) ≫
          S.left.fromSpecResidueField s) : Scheme.{u}) ≤ 1)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ S.left]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f.left).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  obtain ⟨n, _, hn, hu⟩ :=
    HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S.left)
  have hkill (m : M) : n • m = 0 := by
    rw [← Nat.cast_smul_eq_nsmul Λ, hn, zero_smul]
  have hdvd := card_dvd_exponent_pow_rank' (Multiplicative M) hkill
  have horder : IsUnit (Nat.card M : Γ(S.left, ⊤)) := by
    apply isUnit_of_dvd_unit _ (hu.pow (Group.rank (Multiplicative M)))
    change Nat.card M ∣ n ^ Group.rank (Multiplicative M) at hdvd
    obtain ⟨r, hr⟩ := hdvd
    exact ⟨(r : Γ(S.left, ⊤)), by
      simpa only [Nat.cast_mul, Nat.cast_pow] using
        congrArg (fun a : ℕ ↦ (a : Γ(S.left, ⊤))) hr⟩
  let A := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M
  have hA : Finite A := inferInstanceAs (Finite M)
  have hab := isConstructibleAbelianSheaf_higherDirectImage_constant_of_projective_curve
    k X S f hdim A horder q
  let C := (constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let D := higherDirectImage Λ f.left q C
  obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso Λ f.left q C
  have : Limits.PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1} Λ
  have : X.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let ec := (constantCommuteCompose X.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app M
  let ea := e ≪≫ (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f.left).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso ec))
  have hD : Scheme.IsConstructibleSheaf D :=
    module_constructible_of_abelian Λ D _ ea hab
  exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((lowerStar (ModuleCat.{u + 1} Λ) f.left).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj C))) hD

private theorem curve_constructible_affine
    (k : Type u) [Field k] (S : Scheme.{u}) [IsAffine S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    {X : Scheme.{u}} (f : X ⟶ S) [IsProjective f]
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ 1)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ S] :
    HasConstructibleDirectImages Λ f := by
  classical
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  refine hasConstructibleDirectImages_of_exists_mono f fun Q hQ ↦ ?_
  have : Scheme.IsConstructibleSheaf Q := hQ
  obtain ⟨r, Y, h, hh, M, hM, φ, hφ⟩ :=
    exists_mono_biproduct_lowerStar_of_locallyOfFiniteType Λ (f ≫ aS) Q
  let C (i : Fin r) := (constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i)
  let G (i : Fin r) := (lowerStar (ModuleCat.{u + 1} Λ) (h i)).obj (C i)
  have hc (i : Fin r) : Scheme.IsConstructibleSheaf (C i) := by
    have := hM i
    have : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    apply Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf
    refine {
      toIsLocallyConstantSheaf := isLocallyConstantSheaf_constantSheaf (M i)
      isFinitelyGenerated_sheafFiber := ?_ }
    intro Ω _ _ s
    exact ((ModuleCat.isFinitelyGenerated_iff (M i)).2 Module.Finite.of_finite).of_iso
      ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso (M i)).symm
  have hg (i : Fin r) : Scheme.IsConstructibleSheaf (G i) := by
    have := hh i
    have := hc i
    exact Scheme.IsConstructibleSheaf.lowerStar_of_isFinite (h i) (C i)
  have hgood (i : Fin r) (q : ℤ) :
      Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj (G i)))) := by
    have := hh i
    have := hM i
    have : IsProjective (h i ≫ f) :=
      (finite_over_projective_affineLocally f (h i)).2 inferInstance
    have : LocallyOfFiniteType ((h i ≫ f) ≫ aS) := inferInstance
    have : QuasiCompact ((h i ≫ f) ≫ aS) := inferInstance
    let X' : Over (Spec (.of k)) := Over.mk ((h i ≫ f) ≫ aS)
    let S' : Over (Spec (.of k)) := Over.mk aS
    let g : X' ⟶ S' := Over.homMk (h i ≫ f)
    have : LocallyOfFiniteType X'.hom := by
      change LocallyOfFiniteType ((h i ≫ f) ≫ aS)
      infer_instance
    have : QuasiCompact X'.hom := by
      change QuasiCompact ((h i ≫ f) ≫ aS)
      infer_instance
    have : LocallyOfFiniteType S'.hom := by
      change LocallyOfFiniteType aS
      infer_instance
    have : QuasiCompact S'.hom := by
      change QuasiCompact aS
      infer_instance
    have : IsProjective g.left := by
      change IsProjective (h i ≫ f)
      infer_instance
    have : HasInvertibleExponent Λ S'.left := by
      change HasInvertibleExponent Λ S
      infer_instance
    have hdim : ∀ s : S,
        topologicalKrullDim (Limits.pullback (h i ≫ f)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
              S.fromSpecResidueField s) : Scheme.{u}) ≤ 1 := by
      intro s
      let t := Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s
      let e := Limits.pullbackRightPullbackFstIso f t (h i)
      rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
      let p := Limits.pullback.snd (h i) (Limits.pullback.fst f t)
      exact (topologicalKrullDim_le_of_continuous p.continuous
        (fun _ _ hxy heq ↦ p.eq_of_specializes_of_apply_eq_of_isIntegralHom hxy heq)).trans
          (hf _ t)
    have hi := constantModule_curve_constructible k X' S' g hdim Λ (M i) q
    exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        (rightDerivedLowerStarSingleLowerStarIso (h i) f (C i))).symm hi
  have : ∀ i, Scheme.IsConstructibleSheaf (G i) := hg
  refine ⟨⨁ G, φ, hφ, Scheme.IsConstructibleSheaf.biproduct G, fun q ↦ ?_⟩
  let H := _root_.DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ⋙
      _root_.DerivedCategory.homologyFunctor _ q
  have : ∀ i, Scheme.IsConstructibleSheaf (H.obj (G i)) := fun i ↦ hgood i q
  have hsum := Scheme.IsConstructibleSheaf.biproduct (fun i ↦ H.obj (G i))
  exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
    (H.mapBiproduct G).symm hsum

/-- Every higher direct image of a constructible finite-coefficient module sheaf along
`ℙ¹_S → S` is constructible when `S` is of finite type over a field and the coefficients
are annihilated by a positive integer invertible in that field. The coefficient convention
is imposed on `Spec k`; invertibility of its constant global section is invertibility in `k`.
The two homogeneous coordinates are indexed by `ULift (Fin 2)`.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-line-constructible.md`,
order 1618 (blueprint: thm-fin-projective-line-constructible).

Proof. Work first over an affine open of `S`, with the original finite coefficient ring.
Every constructible sheaf embeds into a finite sum of finite pushforwards of finite constant
module sheaves. These sums are constructible. The proved embedding criterion
`hasConstructibleDirectImages_of_exists_mono` reduces the assertion to their higher images;
its finite truncation argument replaces the explicit Cartan–Eilenberg resolution of the plan.
Derived direct image and homology preserve these finite sums.

For a finite morphism `h` into the projective line, the composite with the projection is
projective over the affine Noetherian base. After any geometric base change the map from its
fibre to the projective-line fibre is finite, hence integral. Incomparability of primes says
this map identifies no two comparable points, so it cannot increase topological Krull
dimension. The projective-line fibre has dimension at most one.

The additive group of a finite module killed by `N` has order dividing a power of `N`, hence
invertible on the base. Apply projective-curve finiteness for finite constant abelian sheaves.
The coefficient-forgetting comparison identifies this with the underlying abelian sheaf of
the module higher image. Its finite locally constant strata remain finite locally constant
on forgetting to sets; the finite-coefficient reconstruction theorem recovers module
constructibility. Exactness of finite direct image and the derived composition isomorphism
identify this result with the higher image of the finite pushforward used in the embedding.

Finally apply this affine argument to every affine open of `S`. The cartesian projective-space
base-change square and étale localization identify the restricted higher images. Constructibility
is local for this open cover on the Noetherian base. Convert between the two constructibility
predicates and between bounded-below and unbounded derived categories using their comparison
isomorphisms. The argument includes empty bases and every integer cohomological degree.
-/
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine
    (k : Type u) [Field k] (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    (F : Sheaf (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf
      (ProjectiveSpace (ULift.{u} (Fin 2)) S) Λ _ hcoeff.2.1 F) (q : ℤ) :
    @Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace (ULift.{u} (Fin 2)) S ↘ S)).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  let : Finite Λ := hcoeff.2.1
  let : HasInvertibleExponent Λ (Spec (.of k)) :=
    ⟨N, hcoeff.1, hcoeff.2.2.1, hcoeff.2.2.2⟩
  have : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of k))
  have : CompactSpace S :=
    QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : IsNoetherian S := {}
  have hall : HasConstructibleDirectImages Λ (ProjectiveLine S ↘ S) := by
    intro E hE n
    refine Scheme.IsConstructibleSheaf.of_iSup_eq_top
      (fun U : S.affineOpens ↦ U.1) (iSup_affineOpens_eq_top S) _ fun U ↦ ?_
    have : IsAffine U.1 := U.2
    have : HasInvertibleExponent Λ U.1 :=
      HasInvertibleExponent.of_hom (U.1.ι ≫ S ↘ Spec (.of k))
    have : IsHProjective (ProjectiveLine U.1 ↘ U.1) :=
      ⟨⟨ULift.{u} (Fin 2), inferInstance, 𝟙 _, inferInstance, Category.id_comp _⟩⟩
    have : IsProjective (ProjectiveLine U.1 ↘ U.1) :=
      IsHProjective.isProjective _
    have hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.1),
        topologicalKrullDim (Limits.pullback (ProjectiveLine U.1 ↘ U.1) s : Scheme.{u}) ≤ 1 := by
      intro Ω _ _ s
      let e := (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) s).isoPullback
      rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
      exact topologicalKrullDim_projectiveLine_le_one Ω
    have hl := curve_constructible_affine k U.1 (U.1.ι ≫ S ↘ Spec (.of k))
      (ProjectiveLine U.1 ↘ U.1) hf Λ
    let g := ProjectiveSpace.map (ULift.{u} (Fin 2)) U.1.ι
    have hE' : Scheme.IsConstructibleSheaf ((upperStar (ModuleCat.{u + 1} Λ) g).obj E) := by
      have : Scheme.IsConstructibleSheaf E := hE
      exact Scheme.IsConstructibleSheaf.upperStar g E
    exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
      (upperStarHomologyRightDerivedLowerStarIso
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) U.1.ι) E n).symm (hl _ hE' n)
  have hC := hall F ((Scheme.isConstructibleEtaleModuleSheaf_iff F).1 hF) q
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff _).2
  let R := lowerStar (ModuleCat.{u + 1} Λ) (ProjectiveLine S ↘ S)
  exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (R.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).symm hC

end AlgebraicGeometry.Etale
