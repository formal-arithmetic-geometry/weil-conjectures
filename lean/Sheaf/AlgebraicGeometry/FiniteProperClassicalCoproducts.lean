/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts
import Sheaf.AlgebraicGeometry.FiniteCoefficientRealizationDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-! # Proper direct image preserves coproducts of classical complexes

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements and Transfer
(blueprint: lem-sfb-finite-proper-classical-coproducts).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem fibre_bound {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ℕ)
    (he : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞)) :
    ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞) := by
  intro y
  let a := pullback.fst f (𝟙 Y)
  have ha : a ≫ f = pullback.snd f (𝟙 Y) := by simp [a, pullback.condition]
  let b := pullback.map (pullback.snd f (𝟙 Y)) (Y.fromSpecResidueField y)
    f (Y.fromSpecResidueField y) a (𝟙 _) (𝟙 _) (by simpa using ha.symm) (by simp)
  have : IsIso b := by dsimp [b, a]; infer_instance
  have hdim := IsHomeomorph.topologicalKrullDim_eq b.homeomorph b.homeomorph.isHomeomorph
  exact hdim ▸ he Y (𝟙 Y) y

private theorem etale_cd (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞)) :
    ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (p : ℕ), 2 * e < p →
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerived p).obj M) := by
  intro M p hp
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M
  have hF : Scheme.IsTorsionAbelianSheaf F := by
    apply (Scheme.isTorsionAbelianSheaf_characterizations F).1.mpr
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro W
    exact IsAddTorsion.module_of_finite A (M.obj.obj W)
  have hvan := Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
    f e he F hF (p : ℤ) (by exact_mod_cast hp)
  obtain ⟨i⟩ := Etale.nonempty_higherDirectImage_forget_iso A f (p : ℤ) M
  have hmod := hvan.of_iso i
  have hz : IsZero (Etale.higherDirectImage A f (p : ℤ) M) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map_injective
    exact hmod.eq_of_src _ _
  exact hz.of_iso
    ((Etale.lowerStar (ModuleCat.{u + 1} A) f).homologyRightDerivedFunctorPlusObjSingleFunctorIso
      M p).symm

private theorem fixed_amplitude (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (c : ℕ)
    (hcd : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (p : ℕ), c < p →
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerived p).obj M)) :
    ∀ (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A))) (b : ℤ), DerivedCategory.etaleOriginHomology A X K →
        K.IsLE b → ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K).IsLE
          (b + (c : ℤ) + 1) := by
  have hbdd (T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A))) (b : ℤ) (hT : DerivedCategory.etaleOriginHomology A X T)
      (hTb : _root_.DerivedCategory.TStructure.t.bounded T) (hTle : T.IsLE b) :
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj T).IsLE (b + c) := by
    obtain ⟨G, hG, ⟨i⟩⟩ := DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology A X hT hTb
    have : G.IsLE b := isLE_of_isLE_mapDerivedCategory_comparisonUpperStar
      (_root_.DerivedCategory.TStructure.t.isLE_of_iso i.symm b)
    have := Functor.isLE_rightDerivedFunctor_obj
      (Etale.lowerStar (ModuleCat.{u + 1} A) f) c hcd G b
    have hbound : ((_root_.DerivedCategory.Plus.ι ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj
          ⟨G, hG⟩).IsLE (b + c) :=
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).isLE_mapDerivedCategory_obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj G) (b + c)
    exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
      (((rightDerivedLowerStarComparisonIso _ f).app ⟨G, hG⟩).symm ≪≫
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso i) _
  have := CountableAB4Star.ofShape
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℕ
  have := CountableAB4Star.ofShape
    (C := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) ℕ
  have := (mapDerivedUpperStarLowerStarAdjunction A f).rightAdjoint_preservesLimits
  intro K b hK hKb
  exact _root_.DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor K (b + c) fun n ↦
      hbdd _ b (_root_.DerivedCategory.homologyProperty_truncGE hK _)
        ⟨⟨-(n : ℤ), inferInstance⟩, ⟨b, inferInstance⟩⟩ inferInstance

private theorem fixed_coproducts (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (I : Type (u + 1))
    (K : I → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : ∀ i, DerivedCategory.etaleOriginHomology A X (K i)) :
    IsIso (sigmaComparison (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor K) := by
  exact _root_.DerivedCategory.isIso_sigmaComparison_of_bounded _
    (DerivedCategory.etaleOriginHomology A X)
    (fun _ n hX ↦ ⟨_root_.DerivedCategory.homologyProperty_truncLE hX n,
      _root_.DerivedCategory.homologyProperty_truncGE hX n⟩)
    (DerivedCategory.etaleOriginHomology_sigma A X) ((2 * e : ℕ) + (1 : ℤ))
    (fun K b hK hKb ↦ by
      simpa only [add_assoc] using fixed_amplitude A f (2 * e) (etale_cd A f e he) K b hK hKb)
    (fun K a _ ↦ Functor.isGE_rightDerivedFunctor_obj _ K a)
    (isIso_sigmaComparison_rightDerivedLowerStar_of_bounded A f) K hK

private noncomputable def realizationToSheafIso (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    finiteCoefficientRealization T A ⋙
        SheafOfModules.toSheaf (finiteCoefficientRingSheaf T A) ≅
      sheafCompose (Scheme.ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
  Functor.isoWhiskerLeft
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))
    (asIso (sheafificationAdjunction (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).counit)

private theorem classical_of_realization (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (K : FiniteCoefficientDerivedCategory T A)
    (i : ((finiteCoefficientRealization T A).mapDerivedCategory.{u + 1, u + 2} :
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ⥤
        FiniteCoefficientDerivedCategory T A).obj L ≅ K)
    (hK : IsClassicalModuleComplex K) : DerivedCategory.etaleOriginHomology A T L := by
  intro n
  let E := finiteCoefficientRealization T A
  let H := (_root_.DerivedCategory.homologyFunctor _ n).obj L
  let U := SheafOfModules.toSheaf.{u + 1} (finiteCoefficientRingSheaf T A) ⋙
    sheafCompose (Scheme.ProEt.topology T) (forget AddCommGrpCat.{u + 1})
  have hEH : IsClassicalModuleSheaf (E.obj H) := by
    apply (isClassical_iso_iff (U.mapIso
      (((E.mapDerivedCategoryHomologyFunctorIso n).app L) ≪≫
        (_root_.DerivedCategory.homologyFunctor _ n).mapIso i))).mpr
    exact hK n
  have hH : IsClassical ((sheafCompose (Scheme.ProEt.topology T)
      (forget (ModuleCat.{u + 1} A))).obj H) := by
    apply (isClassical_iso_iff
      ((sheafCompose (Scheme.ProEt.topology T) (forget AddCommGrpCat.{u + 1})).mapIso
        ((realizationToSheafIso T A).app H))).mp
    exact hEH
  exact ((proEtaleClassicalSheavesModules T A).choose_spec.2.2.2.2 H).mp hH

/-- Proper direct image preserves the ambient coproduct of any small family with
classical cohomology. Both cofans are ambient derived coproducts, and the comparison
is their universal map with components `Rf_*(ι_s)`. The common site/coefficient/index
universe contains the entire family; no boundedness is imposed on its members.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements and Transfer
(blueprint: lem-sfb-finite-proper-classical-coproducts).

Proof plan:
1. Ringed-site module categories are Grothendieck and have enough injectives
   (lem-weil-pbc-ring-sheaves-grothendieck, lem-sp-grothendieck-enough-injectives).
   Properness gives qcqs. The finite-discrete coefficient comparisons identify the
   given coefficient sheaf with constant coefficients
   (lem-weil-pbc-finite-discrete-condensed-ring-constant,
   lem-weil-pbc-finite-discrete-scheme-ring-constant).
2. Ambient sums are termwise derived sums (lem-kun-grothendieck-derived-coproducts).
   Exactness of sums gives their cohomology and good-truncation compatibilities
   (lem-weil-pbc-exact-functor-complex-cohomology, def-kun-truncations).
3. Classical sheaves are the image of exact comparison inverse image, a left adjoint.
   Thus sums and good truncations retain classical cohomology
   (det-pe-classical-sheaves-modules, lem-weil-pbc-left-adjoint-preserves-colimits,
   lem-pur-exact-derived-coproducts).
4. The unbounded derived adjunction makes G = Rf_* preserve products. It is
   triangulated and preserves lower bounds, computed by bounded-below injective
   representatives (def-weil-pbc-proetale-operations,
   lem-weil-pbc-right-adjoint-preserves-limits,
   lem-pc-right-derived-functor-triangulated, lem-weil-pbc-dplus-injective-representative).
5. Finite A kills all its modules by a nonzero integer. The proper torsion bound
   gives etale cohomological dimension c = 2e; forgetting coefficients transfers this
   to A-modules. Hence etale direct image preserves arbitrary unbounded sums
   (lem-kun-proper-torsion-cd-bound, lem-sbc-higher-direct-image-forget-comparison,
   lem-weil-pbc-module-sheaves-colimits-forgetful, lem-exc-direct-image-coproducts).
6. Bounded-below comparison applied to a classical heart sheaf transports this
   upper bound to G of that sheaf in degree zero
   (sk-thm-pe-direct-image-comparison, src-right-derived-functor-plus-compatibility,
   lem-sp-derived-functor-single-identification).
7. Exact countable products and left completeness extend the heart bound to
   classical complexes: L <= b implies GL <= b+c (det-pe-products-exact,
   det-pe-left-complete-iso, lem-weil-derived-countable-products-core,
   lem-sfb-left-complete-heart-upper-bound).
8. On any common finite interval, bounded-below classical equivalence, direct-image
   comparison, and the etale sum theorem make the canonical comparison invertible
   (sk-prop-sf-comparison, det-pe-classical-derived-equivalence).
   Naturality identifies this map on every coprojection.
9. Fix m. Set U_s = truncLE m K_s. The removed upper tail maps into degrees >= m+1,
   so H^m(GU_s) -> H^m(GK_s) is invertible by the truncation long exact sequence
   (def-sbc-standard-tstructure-derived-category, lem-sf-derived-homology-long-exact).
10. Set V_s = truncGE (m-c) U_s. Its removed tail is <= m-c-1; Step 7 maps it to
    degrees <= m-1. Thus H^m(GU_s) -> H^m(GV_s) is invertible, and Step 8 applies
    to the common interval [m-c,m].
11. Steps 2-3 give the same truncation identifications and cohomology isomorphisms
    for the ambient sum and for the sums of the image maps.
12. The comparison is natural in families, as checked on each coprojection.
    Apply H^m to the two truncation squares and cancel the vertical isomorphisms.
    Step 8 makes H^m of the comparison invertible; the cohomology criterion
    (lem-weil-pbc-unbounded-derived-iso-cohomology) finishes for every m.
    For the empty family both sums are zero and additive G sends zero to zero. -/
theorem finiteCoefficientDerivedDirectImage_classical_coproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (he : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞))
    (I : Type (u + 1)) (K : I → FiniteCoefficientDerivedCategory X A)
    (hK : ∀ s : I, IsClassicalModuleComplex (K s)) :
    ∃ (c : Cofan K) (_ : IsColimit c)
      (c' : Cofan (fun s ↦ (finiteCoefficientDerivedDirectImage f A).obj (K s)))
      (hc' : IsColimit c'),
      IsIso (hc'.desc (Cofan.mk ((finiteCoefficientDerivedDirectImage f A).obj c.pt)
        (fun s ↦ (finiteCoefficientDerivedDirectImage f A).map (c.inj s)))) := by
  classical
  let EX := finiteCoefficientRealization X A
  let EY := finiteCoefficientRealization Y A
  let DX : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
        FiniteCoefficientDerivedCategory X A := EX.mapDerivedCategory.{u + 1, u + 2}
  let G := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  let F := finiteCoefficientDerivedDirectImage f A
  let L : I → _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
    fun i ↦ DX.objPreimage (K i)
  let α (i : I) : DX.obj (L i) ≅ K i := DX.objObjPreimageIso (K i)
  have hL (i : I) : DerivedCategory.etaleOriginHomology A X (L i) :=
    classical_of_realization X A (L i) (K i) (α i) (hK i)
  have hG : IsIso (sigmaComparison G L) :=
    fixed_coproducts A f e (fibre_bound f e he) I L hL
  have : PreservesColimit (Discrete.functor L) G :=
    PreservesCoproduct.of_iso_comparison G L
  obtain ⟨γ⟩ := finiteCoefficientRealization_directImage f A
  let β : DX ⋙ F ≅ G ⋙ EY.mapDerivedCategory.{u + 1, u + 2} :=
    (Functor.mapDerivedCategoryCompRightDerivedFunctorIso EX
      (finiteCoefficientModuleDirectImage f A)).symm ≪≫
    Functor.rightDerivedFunctorNatIso γ ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (lowerStar (ModuleCat.{u + 1} A) f) EY
  let c : Cofan L := Cofan.mk (∐ L) (Sigma.ι L)
  have hc : IsColimit c := coproductIsCoproduct L
  have : PreservesColimit (Discrete.functor L) (DX ⋙ F) :=
    preservesColimit_of_natIso (Discrete.functor L) β.symm
  have hFc : IsColimit ((DX ⋙ F).mapCocone c) :=
    isColimitOfPreserves (DX ⋙ F) hc
  have : PreservesColimit (Discrete.functor L ⋙ DX) F :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves DX hc) hFc
  have : PreservesColimit (Discrete.functor K) F :=
    preservesColimit_of_iso_diagram F
      (Discrete.natIso (F := Discrete.functor L ⋙ DX)
        (G := Discrete.functor K) (fun i ↦ α i.as))
  let s : Cofan K := Cofan.mk (∐ K) (Sigma.ι K)
  let t : Cofan (fun i ↦ F.obj (K i)) :=
    Cofan.mk (F.obj s.pt) (fun i ↦ F.map (s.inj i))
  have ht : IsColimit t :=
    (isColimitMapCoconeCofanMkEquiv F K s.inj).1
      (isColimitOfPreserves F (coproductIsCoproduct K))
  refine ⟨s, coproductIsCoproduct K, t, ht, ?_⟩
  change IsIso (ht.desc t)
  have hid : ht.desc t = 𝟙 t.pt := ht.hom_ext (by simp)
  rw [hid]
  infer_instance

end AlgebraicGeometry.ProEtale
