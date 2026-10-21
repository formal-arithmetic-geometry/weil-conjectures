/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.FiniteDiscreteCoefficientEncoding
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import all Sheaf.Paper.FiniteDiscreteEncodedPresentation
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import WeilConjectures.ConstructibleSheaf.OpenCover
import Sheaf.Paper.FiniteDiscreteConstructibleEncoding
import Sheaf.Paper.FiniteDiscreteRestrictionEncoding
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel

/-!
# Classical etale models for finite discrete internal coefficients

Source: Bhatt--Scholze, The pro-etale topology for schemes, Sections 5.1 and 5.4;
Stacks Project, Tags 09AK, 09AL and 095E
(blueprint: lem-sfb-finite-discrete-constructible-model).

We use the specified common coefficient encoding and the ordinary uncompleted derived
localization. The etale model below is a literally bounded cochain complex. Its cohomology
is constructible on each affine open. Neither side requires finite Tor amplitude.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Maps from the internal regular module are determined by the image of one.
private noncomputable def regularHomEquiv
    {R : Type (u + 1)} [CommRing R]
    (M : Mod Ab.{u + 1} (AddCommGrpCat.of R)) :
    (Mod.regular (AddCommGrpCat.of R) ⟶ M) ≃ M.X :=
  { toFun := fun f ↦ ((MonObj.one : MonoidalCategoryStruct.tensorUnit Ab.{u + 1} ⟶
      AddCommGrpCat.of R) ≫ f.hom) (ULift.up 1)
    invFun := fun x ↦ Mod.regularLift M (AddCommGrpCat.ofHom (uliftZMultiplesHom M.X x))
    left_inv := by
      intro f
      apply Mod.regular_hom_ext
      rw [Mod.one_comp_regularLift]
      apply (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.X).symm).injective
      simp [Equiv.trans_apply, ConcreteCategory.homEquiv, uliftZMultiplesHom]
      rfl
    right_inv := by
      intro x
      change ((MonObj.one : MonoidalCategoryStruct.tensorUnit Ab.{u + 1} ⟶ AddCommGrpCat.of R) ≫
        (Mod.regularLift M (AddCommGrpCat.ofHom (uliftZMultiplesHom M.X x))).hom)
          (ULift.up 1) = x
      rw [Mod.one_comp_regularLift]
      change (1 : ℤ) • x = x
      exact one_zsmul x }

-- The specified equivalence G need not fix the regular module definitionally.
-- Identify the two representing objects using hG and fully faithful coyoneda.
private noncomputable def scalarRegularIso
    {R : Type (u + 1)} [CommRing R]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of R) ⥤ ModuleCat.{u + 1} R)
    [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of R)) :
    G.obj (Mod.regular (AddCommGrpCat.of R)) ≅ ModuleCat.of R R := by
  let e (M : Mod Ab.{u + 1} (AddCommGrpCat.of R)) :
      (Mod.regular (AddCommGrpCat.of R) ⟶ M) ≃ (ModuleCat.of R R ⟶ G.obj M) :=
    (regularHomEquiv M).trans
      (((forget Ab.{u + 1}).mapIso ((eqToIso hG).app M).symm).toEquiv.trans
        ((LinearMap.ringLmapEquivSelf R ℤ (G.obj M)).toEquiv.symm.trans
          (ModuleCat.homEquiv (M := ModuleCat.of R R) (N := G.obj M)).symm))
  have he (M : Mod Ab.{u + 1} (AddCommGrpCat.of R))
      (h : Mod.regular (AddCommGrpCat.of R) ⟶ M) :
      e M h 1 = ((eqToIso hG).inv.app M) (regularHomEquiv M h) := by
    let y : G.obj M := ((eqToIso hG).inv.app M) (regularHomEquiv M h)
    change (1 : R) • y = y
    exact one_smul _ _
  let i : G ⋙ CategoryTheory.coyoneda.obj
      (Opposite.op (G.obj (Mod.regular (AddCommGrpCat.of R)))) ≅
      G ⋙ CategoryTheory.coyoneda.obj (Opposite.op (ModuleCat.of R R)) :=
    NatIso.ofComponents
      (fun M ↦ ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans (e M)).toIso) (by
        intro M N f
        ext g
        apply ModuleCat.hom_ext
        apply LinearMap.ext_ring
        change e N (G.preimage (g ≫ G.map f)) 1 = (e M (G.preimage g) ≫ G.map f) 1
        rw [G.preimage_comp, G.preimage_map]
        let x := ((MonObj.one : MonoidalCategoryStruct.tensorUnit Ab.{u + 1} ⟶ AddCommGrpCat.of R) ≫
          (G.preimage g).hom) (ULift.up 1)
        have hn := ConcreteCategory.congr_hom ((eqToIso hG).inv.naturality f) x
        change ((eqToIso hG).inv.app N) (f.hom x) =
          (G.map f) (((eqToIso hG).inv.app M) x) at hn
        rw [he]
        change ((eqToIso hG).inv.app N) (f.hom x) =
          (G.map f) (e M (G.preimage g) 1)
        rw [he]
        exact hn)
  let j := (Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ _).obj G)).preimageIso i
  exact (CategoryTheory.Coyoneda.fullyFaithful.preimageIso j).unop.symm

-- A finite presentation over B sheafifies to a finite internal presentation.
private lemma encodedConstantFP
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Finite B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
    (T : Scheme.{u}) (P : ModuleCat.{u + 1} (ULift.{u + 1} B)) [Finite P] :
    Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj
        ((constantSheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P)) := by
  let R := ULift.{u + 1} B
  let J := Scheme.ProEt.topology T
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let H := CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncoding J R G hG
  let S := constantSheaf J (ModuleCat.{u + 1} R)
  have : H.IsEquivalence :=
    CategoryTheory.ConstantInternalModuleSheafEncoding.sheafEncodingIsEquivalence J R G hG
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  have : S.Additive := Functor.additive_of_preserves_binary_products S
  let A := (presheafToSheaf J Ab.{u + 1}).obj
    (CategoryTheory.ConstantInternalModuleSheafEncoding.A (C := T.ProEtᵒᵖ) R)
  let c (n : ℕ) : H.obj (Mod.finiteFree A n) ≅
      S.obj (ModuleCat.of R (Fin n → R)) :=
    CategoryTheory.ConstantInternalModuleSheafEncoding.encFiniteFreeIso J R G hG n ≪≫
      S.mapIso (biproduct.mapIso (fun _ ↦ scalarRegularIso G hG) ≪≫
        ModuleCat.biproductIsoPi _)
  have : Module.FinitePresentation R P := Module.finitePresentation_of_finite R P
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' R P
  let f' : ModuleCat.of R (Fin n → R) ⟶ P := ModuleCat.ofHom f
  let g' : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) :=
    ModuleCat.ofHom g
  let ec : P ≅ cokernel g' :=
    (ModuleCat.isColimitCokernelCofork g' f' hg hf).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let d : Mod.finiteFree A m ⟶ Mod.finiteFree A n :=
    H.preimage ((c m).hom ≫ S.map g' ≫ (c n).inv)
  have hc : Mod.IsFinitelyPresented A (H.inv.obj (S.obj P)) := by
    refine ⟨n, m, d, ⟨?_⟩⟩
    apply H.preimageIso
    exact H.asEquivalence.counitIso.app _ ≪≫ S.mapIso ec ≪≫
      PreservesCokernel.iso S g' ≪≫
      cokernel.mapIso _ (H.map d) (c m).symm (c n).symm (by simp [d]) ≪≫
      (PreservesCokernel.iso H d).symm
  unfold finiteDiscreteCoefficientEquivalence
  exact finitePresentation_comap (inv (finiteDiscreteSchemeRingIso B T eR).hom) hc

private lemma internalLisseFP
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Finite B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
    (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    [Scheme.IsFiniteLocallyConstantSheaf F]
    (M : FiniteDiscreteInternalModules B T)
    (e : (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).obj F) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
      M := by
  classical
  obtain ⟨⟨C₀, hC⟩⟩ := Scheme.IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  -- On a nonempty cover member, finiteness of a constant sheaf implies finiteness
  -- of its value. Empty members carry no local finite-presentation obligation.
  let C := C₀.nonemptyMembers
  let D : Scheme.Cover.{u} Scheme.proetalePrecoverage T :=
    ⟨C.toPreZeroHypercover, Scheme.etalePrecoverage_le_proetalePrecoverage _ C.mem₀⟩
  refine ⟨D, ?_⟩
  rintro ⟨i, hi⟩
  have hc : ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (C₀.f i)).obj F).IsConstant
      (C₀.X i).smallEtaleTopology :=
    (Scheme.isConstant_over_iff_upperStar _ (C₀.etalePrecoverageToEtale i) F).mp (hC i)
  obtain ⟨P, ⟨eP⟩⟩ :=
    (((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
      (C₀.f i)).obj F).mem_essImage_of_isConstant)
  have : Scheme.IsFiniteSheaf
      ((constantSheaf (C₀.X i).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P) := by
    have := Scheme.IsFiniteSheaf.upperStar (C₀.f i) F
    exact Scheme.IsFiniteSheaf.of_iso eP.symm
  have : Nonempty (C₀.X i) := hi
  have : Module.Finite (ULift.{u + 1} B) P :=
    Scheme.moduleFinite_of_isFiniteSheaf_constantSheaf (Y := C₀.X i) P
  have : Finite P := Module.finite_of_finite (ULift.{u + 1} B)
  let α := condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) (C₀.f i)
  let raw := ((ProEtale.upperStar Ab.{u + 1} (C₀.f i)).mapMod
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M
  let norm := (Mod.comap (inv α)).obj raw
  let E := finiteDiscreteCoefficientEquivalence B eR G hG (C₀.X i)
  let eN : E.inverse.obj norm ≅
      (constantSheaf (Scheme.ProEt.topology (C₀.X i))
        (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P :=
    (finiteDiscreteCoefficient_restrictionEncoding B eR G hG T (C₀.X i) (C₀.f i) M).some.symm ≪≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (C₀.f i)).mapIso e) ≪≫
      (comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) (C₀.f i)).app F ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (C₀.X i)).mapIso eP.symm ≪≫
      (comparisonUpperStarConstantSheafIso (ULift.{u + 1} B) (C₀.X i)).app P
  have hp := encodedConstantFP B eR G hG (C₀.X i) P
  have hn := finitePresentation_of_iso
    ((E.counitIso.app norm).symm ≪≫ E.functor.mapIso eN).symm hp
  exact finitePresentation_of_comap (inv α) hn

private lemma internalComparisonConstructible
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Finite B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
    (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    [Scheme.IsConstructibleSheaf F] :
    IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).obj F)) := by
  obtain ⟨S, hS⟩ := Scheme.IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} (ULift.{u + 1} B) ↦ M →ₗ[ULift.{u + 1} B] N)
    (CA := fun M : ModuleCat.{u + 1} (ULift.{u + 1} B) ↦ M) (F := F)
  refine ⟨S, fun a ↦ ?_⟩
  have := hS a
  let E := finiteDiscreteCoefficientEquivalence B eR G hG T
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T
  let α := condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) (S.immersion a)
  apply localFinitePresentation_of_comap (inv α)
  apply internalLisseFP B eR G hG (S.domain a)
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (S.immersion a)).obj F)
  exact
    (finiteDiscreteCoefficient_restrictionEncoding B eR G hG T (S.domain a)
      (S.immersion a) (E.functor.obj (N.obj F))).some.symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) (S.immersion a)).mapIso
      (E.unitIso.app (N.obj F)).symm ≪≫
    (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) (S.immersion a)).app F

/-- Finite discrete internal bounded constructible complexes admit precisely the classical
bounded constructible etale models, through the specified common encoding.

Source: Bhatt--Scholze, Sections 5.1 and 5.4; Stacks Tags 09AK, 09AL and 095E
(blueprint: lem-sfb-finite-discrete-constructible-model).

Proof following the seven DAG steps:
1. Write E for finiteDiscreteCoefficientEquivalence and F for its inverse. Their exact
termwise functors descend to inverse derived equivalences by
lem-weil-pbc-exact-functor-derived-factorization. By
lem-weil-pbc-exact-functor-complex-cohomology they commute with cohomology, and preserve and
reflect its vanishing intervals. Put J = D(F)K.
2. A finite B-module P has a finite presentation: the free module on its finite underlying
set surjects onto P, and the kernel is finite because B is finite. Conversely a finitely
presented module is a quotient of a finite power of B and is finite. Every ideal of B is
likewise generated by its finite underlying set, so B is Noetherian. This includes B = 0.
3. If K is internally bounded constructible, apply
lem-weil-pbc-finite-discrete-constructible-encoding to every cohomology module. Step 1 gives
bounded J with finite constant local models on finite strata. Apply
lem-weil-pbc-fixed-module-constructible-origin to obtain an etale antecedent of each H^q(J).
4. Apply lem-weil-pbc-fixed-module-bounded-constructible-origin to J. This gives a bounded
etale derived antecedent with constructible cohomology. Global stratifications restrict to
all affine opens. The bounded-representative lemma, namely
DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, gives a literally bounded cochain complex
L representing it. Apply D(E) and its derived counit to obtain the displayed isomorphism.
5. Conversely, affine-local constructibility of H^q(L) globalizes using the existing
Scheme.IsConstructibleSheaf.of_iSup_eq_top on the cover by all affine opens. Choose the
resulting finite stratification. On each stratum the etale sheaf is finite locally constant;
an etale trivializing cover is also a pro-etale cover. Comparison inverse image commutes
with restriction and takes constant sheaves to constant sheaves. Its exactness identifies
nu^*H^q(L) with H^q(D(nu^*)Q(L)).
6. On each stratum and member of its trivializing cover, a finite constant module P has
the finite presentation of step 2. Sheafify it using the ordinary constant-sheaf functor,
which preserves finite colimits. The restriction compatibility
lem-weil-pbc-finite-discrete-restriction-encoding identifies its image under E with the same
finite presentation over the pulled-back ring object. E takes the rank-one free module to
the regular module: both represent sections of the underlying abelian sheaf by evaluation
at 1. Thus E(P) is locally finitely presented. This is the general ring-object definition
of constructibility, on the same finite strata and covering families.
7. Apply step 6 to every nu^*H^q(L). Step 1 identifies their images with the cohomology of
the displayed derived model. The bounds of L are preserved by both exact functors. The
isomorphism transports the resulting constructibility and vanishing conditions to K,
which is therefore bounded constructible. No step requires a Tor-amplitude bound.
-/
theorem finiteDiscrete_boundedConstructible_iff_classicalModel
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom]
    (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
    (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
    (Z : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z]
    (K : DerivedCategory (FiniteDiscreteInternalModules B Z)) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} B) Z) K ↔
      ∃ (L : CochainComplex
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} B))) ℤ)
        (a b : ℤ), a ≤ b ∧ L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
        (∀ (q : ℤ) (U : Z.Opens), IsAffineOpen U →
          Scheme.IsConstructibleSheaf
            ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) U.ι).obj
              (L.homology q))) ∧
        Nonempty (K ≅
          ((finiteDiscreteCoefficientEquivalence B eR G hG Z).functor.mapDerivedCategory).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) Z).mapDerivedCategory.obj
              (DerivedCategory.Q.obj L))) := by
  let E := finiteDiscreteCoefficientEquivalence B eR G hG Z
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) Z
  have : PreservesFiniteLimits N :=
    (siteComparison_finiteLevel Z (ULift.{u + 1} B)).1
  have : PreservesFiniteColimits N :=
    (siteComparison_finiteLevel Z (ULift.{u + 1} B)).2.1
  constructor
  · intro hK
    let J := E.inverse.mapDerivedCategory.obj K
    have hJ : _root_.DerivedCategory.TStructure.t.bounded J :=
      E.inverse.bounded_mapDerivedCategory_obj hK.1
    have hH (q : ℤ) : ∃ F : Sheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} B)), Scheme.IsConstructibleSheaf F ∧
        Nonempty (N.obj F ≅ (_root_.DerivedCategory.homologyFunctor _ q).obj J) := by
      have hc := finiteDiscreteCoefficient_constructible B eR G hG Z _ (hK.2 q)
      have hc' := isConstructible_of_iso
        ((E.inverse.mapDerivedCategoryHomologyFunctorIso q).app K) hc
      exact exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _ hc'
    obtain ⟨A, hA, ⟨eA⟩⟩ :=
      ProEtale.DerivedCategory.boundedConstructible_of_homology
        (ULift.{u + 1} B) hJ hH
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hA.1
    have hb' : A.IsLE (max a b) :=
      _root_.DerivedCategory.TStructure.t.isLE_of_le A b (max a b) (le_max_right _ _)
    obtain ⟨L, hLa, hLb, ⟨eL⟩⟩ :=
      _root_.DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE A a (max a b)
    refine ⟨L, a, max a b, le_max_left _ _, hLa, hLb, ?_, ?_⟩
    · intro q U _
      have hF := hA.2 q
      have : Scheme.IsConstructibleSheaf (L.homology q) :=
        Scheme.IsConstructibleSheaf.of_iso
          ((_root_.DerivedCategory.homologyFunctor _ q).mapIso eL ≪≫
            (_root_.DerivedCategory.homologyFunctorFactors _ q).app L)
      exact Scheme.IsConstructibleSheaf.upperStar U.ι _
    · exact ⟨(E.mapDerivedCategory.counitIso.app K).symm ≪≫
        E.functor.mapDerivedCategory.mapIso
          (eA.symm ≪≫ N.mapDerivedCategory.mapIso eL)⟩
  · rintro ⟨L, a, b, _, hLa, hLb, hL, ⟨e⟩⟩
    have hb : _root_.DerivedCategory.TStructure.t.bounded
        (_root_.DerivedCategory.Q.obj L) :=
      ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩
    refine ⟨(_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso e.symm
      (E.functor.bounded_mapDerivedCategory_obj (N.bounded_mapDerivedCategory_obj hb)), ?_⟩
    intro q
    have : IsNoetherian Z := {}
    have hglobal : Scheme.IsConstructibleSheaf (L.homology q) := by
      apply Scheme.IsConstructibleSheaf.of_iSup_eq_top
        (fun i : Z.affineOpens ↦ (i : Z.Opens)) (iSup_affineOpens_eq_top Z) _
      intro i
      exact hL q _ i.property
    let ec : E.functor.obj (N.obj (L.homology q)) ≅
        (_root_.DerivedCategory.homologyFunctor _ q).obj K :=
      E.functor.mapIso (N.mapIso
        ((_root_.DerivedCategory.homologyFunctorFactors _ q).app L).symm) ≪≫
      E.functor.mapIso ((N.mapDerivedCategoryHomologyFunctorIso q).app
        (_root_.DerivedCategory.Q.obj L)) ≪≫
      (E.functor.mapDerivedCategoryHomologyFunctorIso q).app
        (N.mapDerivedCategory.obj (_root_.DerivedCategory.Q.obj L)) ≪≫
      (_root_.DerivedCategory.homologyFunctor _ q).mapIso e.symm
    exact constructible_of_iso ec (internalComparisonConstructible B eR G hG Z _)

end AlgebraicGeometry.ProEtale.CondensedRing
