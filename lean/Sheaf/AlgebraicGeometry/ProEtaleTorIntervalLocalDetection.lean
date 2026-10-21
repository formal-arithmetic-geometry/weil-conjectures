/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q87 and P4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection

/-! # Detection of a fixed Tor interval on the pro-etale site

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure, ctf-equals-bc proof, Locality and Strata;
Stacks Project, Tags 04JC, 015F, 010N, 07A4, 03CE, 04TQ and 09AH
(blueprint: lem-sfb-tor-interval-local-detection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

/-- Transport a homotopy-level tensor presentation to a class of complexes. -/
private noncomputable def tensorPresentationOfHomotopy
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (P : ObjectProperty (CochainComplex D ℤ))
    (S : ObjectProperty (HomotopyCategory D (.up ℤ)))
    (hS : ∀ K, P K → S ((HomotopyCategory.quotient D (.up ℤ)).obj K))
    {t : CochainComplex D ℤ × CochainComplex D ℤ ⥤ CochainComplex D ℤ}
    {B : HomotopyCategory D (.up ℤ) × HomotopyCategory D (.up ℤ) ⥤
      HomotopyCategory D (.up ℤ)}
    (b : (HomotopyCategory.quotient D (.up ℤ)).prod
      (HomotopyCategory.quotient D (.up ℤ)) ⋙ B ≅
        t ⋙ HomotopyCategory.quotient D (.up ℤ))
    {T : DerivedCategory D × DerivedCategory D ⥤ DerivedCategory D}
    (r : (S.ι.prod S.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
      ((S.ι ⋙ DerivedCategory.Qh).prod (S.ι ⋙ DerivedCategory.Qh)) ⋙ T) :
    (P.ι.prod P.ι) ⋙ t ⋙ DerivedCategory.Q ≅
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ T := by
  let H : P.FullSubcategory ⥤ S.FullSubcategory :=
    { obj := fun K ↦ ⟨(HomotopyCategory.quotient D (.up ℤ)).obj K.obj, hS K.obj K.property⟩
      map := fun f ↦ ObjectProperty.homMk ((HomotopyCategory.quotient D (.up ℤ)).map f.hom)
      map_id K := by
        apply ObjectProperty.hom_ext
        exact (HomotopyCategory.quotient D (.up ℤ)).map_id K.obj
      map_comp f g := by
        apply ObjectProperty.hom_ext
        exact (HomotopyCategory.quotient D (.up ℤ)).map_comp f.hom g.hom }
  exact Functor.isoWhiskerLeft (P.ι.prod P.ι)
      ((Functor.isoWhiskerLeft t (DerivedCategory.quotientCompQhIso D)).symm ≪≫
        Functor.isoWhiskerRight b.symm DerivedCategory.Qh) ≪≫
    Functor.isoWhiskerLeft (H.prod H) r ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso D))
        (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso D))) T

/-- The specified resolving-class tensor has the flat-complex presentation used by
canonical pro-etale tensor pullback. -/
private theorem torTensorModel (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ a : ProEtaleTensorModel X A,
      a.tensor = SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A := by
  classical
  have h :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u + 1, u,
      u + 1, u + 2, 0, 0}
      (ProEt.topology X) A
  let P := h.choose
  have hP := h.choose_spec.1
  let b := h.choose_spec.2.2.1.choose_spec.1.some
  let r := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  refine ⟨⟨SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A,
    ?_⟩, rfl⟩
  exact tensorPresentationOfHomotopy (proEtaleFlatRepresentatives X A) P
    (fun K hK ↦ (hP _).2
      ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).2 hK.1, hK.2⟩) b r

/-- Exact inverse image commutes with the cohomology of derived tensor with a module. -/
private theorem torTensorPullbackIsZero {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : DerivedCategory (proEtaleRingModules X A)) (M : proEtaleRingModules X A) (q : ℤ)
    (h : ∀ N : proEtaleRingModules Y
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A),
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology Y)
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A)).obj
          ((proEtaleRingDerivedPullback f A _ (Iso.refl _)).obj K,
            (DerivedCategory.singleFunctor _ 0).obj N)))) :
    IsZero ((proEtaleRingModulePullback f A _ (Iso.refl _)).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A).obj
          (K, (DerivedCategory.singleFunctor _ 0).obj M)))) := by
  obtain ⟨a, ha⟩ := torTensorModel X A
  obtain ⟨b, hb⟩ := torTensorModel Y
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A)
  let F := proEtaleRingModulePullback f A _ (Iso.refl _)
  let e := (proEtaleCanonicalTensorPullback f A _ (Iso.refl _) a b).2.choose
  let s := (F.mapDerivedCategorySingleFunctor 0).app M
  have he := e.app (K, (DerivedCategory.singleFunctor _ 0).obj M)
  have hz := h (F.obj M)
  rw [← hb] at hz
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    (b.tensor.mapIso (Iso.prod (Iso.refl _) s)))
  rw [← ha]
  exact hz'.of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso he)

/-- The normalized module unit identifies its underlying sheaf with abelian inverse image. -/
private theorem torModuleInverseImageUnderlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (M : proEtaleRingModules Y R) :
    Nonempty ((SheafOfModules.toSheaf _).obj ((proEtaleModuleInverseImage f R).obj M) ≅
      (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj M)) := by
  obtain ⟨adj, h⟩ := proEtaleModuleInverseImage_canonicalUnitComparison f R
  let P := SheafOfModules.toSheaf ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let Q := SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
  let e := ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
    (P.obj M) (Q.obj ((proEtaleModuleInverseImage f R).obj M))).symm
      (P.map (adj.unit.app M))
  have : IsIso e := h M
  exact ⟨(asIso e).symm⟩

/-- Scalar extension along an isomorphism reflects vanishing of inverse image. -/
private theorem torInverseImageIsZero {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (M : proEtaleRingModules X A)
    (h : IsZero ((proEtaleRingModulePullback f A _ (Iso.refl _)).obj M)) :
    IsZero ((proEtaleModuleInverseImage f A).obj M) := by
  let B := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A
  let rc := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (Iso.refl B)
  let e := proEtaleScalarEquivalence Y rc
  let adj := proEtaleRingExtensionAdjunction f A B (Iso.refl _)
  let t := adj.leftAdjointUniq e.symm.toAdjunction
  have hz : IsZero (e.inverse.obj ((proEtaleModuleInverseImage f A).obj M)) :=
    h.of_iso (t.app _).symm
  exact (e.functor.map_isZero hz).of_iso (e.counitIso.app _).symm

/-- A quasi-compact pro-etale cover detects zero module sheaves with arbitrary coefficients. -/
private theorem torModuleCoverDetection (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (𝒱 : X.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale))
    [QuasiCompactCover 𝒱.toPreZeroHypercover] (M : proEtaleRingModules X A)
    (h : ∀ t, IsZero ((proEtaleRingModulePullback (𝒱.f t) A _ (Iso.refl _)).obj M)) :
    IsZero M := by
  let V := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)
  let G := V.obj M
  have hz (t : 𝒱.I₀) :
      IsZero ((AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
        (𝒱.f t) inferInstance).obj G) := by
    obtain ⟨e⟩ := torModuleInverseImageUnderlying (𝒱.f t) A M
    have hG := ((SheafOfModules.toSheaf _).map_isZero
      (torInverseImageIsZero (𝒱.f t) A M (h t))).of_iso e.symm
    let W : X.ProEt := ProEt.mk (𝒱.f t)
    obtain ⟨comparison⟩ := (proEtaleObjectInverseImageRestriction X W (ULift.{u} ℤ)).2.2.1
    exact hG.of_iso (comparison.sheafIso.app G).symm
  have hg : Presieve.ofArrows 𝒱.X 𝒱.f ∈ proetalePrecoverage X :=
    𝒱.ofQuasiCompactCover.mem₀
  let z : G ⟶ 0 := 0
  have hi : IsIso z := by
    apply AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction
      AddCommGrpCat.{u + 1} z 𝒱.f hg
    intro t
    have : (AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
        (𝒱.f t) inferInstance).Additive := ⟨by intros; ext U; rfl⟩
    exact (hz t).isIso ((AlgebraicGeometry.ProEtale.localizationRestriction
      AddCommGrpCat.{u + 1} (𝒱.f t) inferInstance).map_isZero (isZero_zero _)) _
  have hG : IsZero G := (isZero_zero _).of_iso (asIso z)
  apply (IsZero.iff_id_eq_zero M).2
  apply V.map_injective
  simpa using hG.eq_of_src (V.map (𝟙 M)) (V.map (0 : M ⟶ M))

/-- Tor amplitude in one fixed interval is detected by a pro-etale covering family,
and by restriction to a closed subscheme and its complementary quasi-compact open.
Coefficients are an arbitrary commutative ring sheaf, and complexes are unbounded.
The interval condition is expanded as the test on every module in degree zero.
The coefficient on each source is the actual inverse-image ring; the structural
identification is its identity, so the displayed derived pullback is inverse image.

Source: blueprint main-20261015, ctf-equals-bc proof, Locality and Strata;
Stacks Project, Tags 04JC, 015F, 010N, 07A4, 03CE, 04TQ and 09AH
(blueprint: lem-sfb-tor-interval-local-detection).

Proof:
1. For any f, use the coefficient f⁻¹ A and its identity structural map.
   The specified pro-etale module pullback is exact and its derived pullback is
   Mathlib's exact termwise descent. Its homology and single-functor comparisons
   give H^q(f⁻¹ E) ≅ f⁻¹ H^q(E) and f⁻¹(M[0]) ≅ (f⁻¹M)[0].
2. Present the specified resolving-class tensor by flat K-flat complexes, using
   lem-weil-pbc-site-derived-tensor-descent and quotientCompQhIso. The pro-etale
   specialization of lem-weil-pbc-ringed-topoi-derived-tensor-pullback then gives
   f⁻¹(K ⊗ᴸ M[0]) ≅ f⁻¹K ⊗ᴸ (f⁻¹M)[0].
3. For a cover, fix M and q outside [c,d], and put F = H^q(K ⊗ᴸ M[0]).
   Steps 1 and 2 and each local Tor bound make its module pullbacks zero.
   Scalar transport along the identity coefficient isomorphism reflects zero.
   The canonical module-unit comparison identifies the underlying sheaf with
   abelian inverse image. The abelian clause of
   lem-sfb-proetale-object-inverse-image-restriction identifies this with slice
   restriction. Apply the proved pro-etale cover-local isomorphism criterion to
   F → 0. Faithfulness of the forgetful functor reflects zero to module sheaves.
   Vary M and q to obtain the first assertion.
4. For the closed/open pair, apply steps 1 and 2 to both immersions. Testing
   their Tor bounds on i⁻¹M and j⁻¹M makes i⁻¹F and j⁻¹F zero. Apply
   lem-exc-open-closed-detection with the inverse-image coefficient rings and
   identity identifications. This gives F = 0. Vary M and q to obtain the
   second assertion, with the same interval and no quasi-coherence assumption. -/
theorem proEtale_torInterval_local_detection
    (X : Scheme.{u}) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : DerivedCategory (proEtaleRingModules X A)) (c d : ℤ) (_hcd : c ≤ d) :
    (∀ (𝒱 : X.Cover.{u + 1} (Scheme.precoverage @WeaklyEtale))
      (_ : QuasiCompactCover 𝒱.toPreZeroHypercover),
      (∀ t : 𝒱.I₀,
        ∀ (M : proEtaleRingModules (𝒱.X t)
            ((proEtaleSheafInverseImage (𝒱.f t) CommRingCat.{u + 1}).obj A))
          (q : ℤ), q < c ∨ d < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology (𝒱.X t))
              ((proEtaleSheafInverseImage (𝒱.f t) CommRingCat.{u + 1}).obj A)).obj
              (((proEtaleRingDerivedPullback (𝒱.f t) A _ (Iso.refl _)).obj K),
                (DerivedCategory.singleFunctor _ 0).obj M)))) →
      ∀ (M : proEtaleRingModules X A) (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A).obj
            (K, (DerivedCategory.singleFunctor _ 0).obj M)))) ∧
    (∀ (Z U : Scheme.{u}) (i : Z ⟶ X) (j : U ⟶ X)
      (_ : IsClosedImmersion i) (_ : IsOpenImmersion j) (_ : QuasiCompact j),
      Set.range j = (Set.range i)ᶜ →
      (∀ (M : proEtaleRingModules Z
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A))
        (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology Z)
            ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)).obj
            (((proEtaleRingDerivedPullback i A _ (Iso.refl _)).obj K),
              (DerivedCategory.singleFunctor _ 0).obj M)))) →
      (∀ (M : proEtaleRingModules U
          ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj A))
        (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology U)
            ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj A)).obj
            (((proEtaleRingDerivedPullback j A _ (Iso.refl _)).obj K),
              (DerivedCategory.singleFunctor _ 0).obj M)))) →
      ∀ (M : proEtaleRingModules X A) (q : ℤ), q < c ∨ d < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X) A).obj
            (K, (DerivedCategory.singleFunctor _ 0).obj M)))) := by
  constructor
  · intro 𝒱 h𝒱 hlocal M q hq
    let := h𝒱
    apply torModuleCoverDetection X A 𝒱
    intro t
    exact torTensorPullbackIsZero (𝒱.f t) A K M q (fun N ↦ hlocal t N q hq)
  · intro Z U i j hi hj hqc hU hclosed hopen M q hq
    let := hi
    let := hj
    let := hqc
    apply proEtaleRingModule_isZero_of_open_closed i j hU A
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)
      ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj A) (Iso.refl _) (Iso.refl _)
    · exact torTensorPullbackIsZero j A K M q (fun N ↦ hopen N q hq)
    · exact torTensorPullbackIsZero i A K M q (fun N ↦ hclosed N q hq)

end AlgebraicGeometry.Scheme
