/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.FinitePerfectAdicTowerData
public import Sheaf.Paper.ConstantRealizationDerivedScalarExtension
import Sheaf.Paper.FiniteConstantSliceIsoReflects
import Sheaf.Paper.FinitePerfectAdicConstantScalarExtension
import all Sheaf.Paper.ProEtaleLocalScalarHomologyIso

/-! # Balancing two constant models of consecutive actual quotients

Source: Stacks Project, Tag 09C6, the consecutive quotient balancing isomorphism;
Tags 0D6D and 03Q3 for derived scalar transitivity and geometric stalks.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-models-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local irreducible] completedAdicChangeData completedAdicDerivedChange
  Functor.mapDerivedCategory HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.monoidalCategory

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def chartRestrictionIso (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (K : DerivedCategory (SheafOfModules.{t + 1} R)) :
    (ringedDerivedRestrictionGeneral R U).obj K ≅
      ringedSiteDerivedRestrictionOfUniverses R U K := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem chartScalarIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (U : X.ProEt) (K L : DerivedCategory (proEtaleRingModules X R))
    (e : (ringedDerivedRestrictionGeneral ((adicLisseForget X).obj R) U).obj K ≅
      (ringedDerivedRestrictionGeneral ((adicLisseForget X).obj R) U).obj L) :
    Nonempty
      ((ringedDerivedRestrictionGeneral ((adicLisseForget X).obj S) U).obj
          ((completedAdicDerivedChange X φ).obj K) ≅
        (ringedDerivedRestrictionGeneral ((adicLisseForget X).obj S) U).obj
          ((completedAdicDerivedChange X φ).obj L)) := by
  let J := ProEt.topology X
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let R₀ := (adicLisseForget X).obj R
  let S₀ := (adicLisseForget X).obj S
  let F := SheafOfModules.overFunctor.{t + 1} R₀ U
  let G := SheafOfModules.overFunctor.{t + 1} S₀ U
  have := (ringedOverFunctor_exactGeneral R₀ U).1
  have := (ringedOverFunctor_exactGeneral R₀ U).2.1
  have := (ringedOverFunctor_exactGeneral R₀ U).2.2
  have := (ringedOverFunctor_exactGeneral S₀ U).1
  have := (ringedOverFunctor_exactGeneral S₀ U).2.1
  have := (ringedOverFunctor_exactGeneral S₀ U).2.2
  let ψ := (J.overPullback CommRingCat.{t + 1} U).map φ
  obtain ⟨T, hobj, hmap, hadd, _, _, DT, ε, _, _, hT⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      (J := J.over U) ψ
  have : T.Additive := hadd
  let bT : T ≅ SheafOfModules.ScalarReductionProof.tensorFunctor.{t + 1, t, t + 1} ψ :=
    NatIso.ofComponents (fun N ↦ eqToIso (hobj N)) (by
      intro N N' f
      change T.map f ≫ eqToHom (hobj N') =
        eqToHom (hobj N) ≫ SheafOfModules.changeOfRingsHom ψ N f
      rw [hmap f]
      simp)
  let b : completedAdicChange X φ ⋙ G ≅ F ⋙ T :=
    Functor.isoWhiskerRight (completedTensorIso X φ) G ≪≫
      (tensorOverIso φ U).some ≪≫ Functor.isoWhiskerLeft F bT.symm
  let P : ObjectProperty (CochainComplex (proEtaleRingModules X R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
  have hres : ∀ Z : HomotopyCategory (proEtaleRingModules X R) (.up ℤ),
      ∃ (Y : (show ObjectProperty (HomotopyCategory (proEtaleRingModules X R) (.up ℤ))
          from fun Z ↦ P Z.as).FullSubcategory) (s : Y.obj ⟶ Z),
        HomotopyCategory.quasiIso _ (.up ℤ) s := by
    intro Z
    obtain ⟨C, f, hc, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) Z.as
    exact ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj C, hc⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map f,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  obtain ⟨c⟩ := derivedSquare (completedAdicChange X φ) F G T
    (completedAdicDerivedChange X φ) DT (pbcExtensionCounit φ) ε P hres
    (fun Z ↦ pbcExtensionCounit_isIso φ Z.obj Z.property)
    (fun Z ↦ hT _
      ((SheafOfModules.ringedSite_restriction_exact_kflat.{t + 1, t, 0} J R U).2.2
        Z.obj Z.property)) b
  exact ⟨c.app K ≪≫ DT.mapIso e ≪≫ (c.app L).symm⟩

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def algebraicConstantRepresentative (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    (finitePerfectAdicDerivedConstant X B).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (finiteModelConstantComplex X B P) := by
  have := koszulConstantFunctor_preservesZero X B
  have := (finitePerfectAdicConstant_exact X B).1
  have := (finitePerfectAdicConstant_exact X B).2.1
  have := (finitePerfectAdicConstant_exact X B).2.2
  exact (finitePerfectAdicConstant X B).mapDerivedCategoryFactors.app P

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem reflectConstantIso (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ) (W : X.Etale) (w : W.left)
    (K L : DerivedCategory (ModuleCat.{t} B))
    (e : (ringedDerivedRestrictionGeneral ((adicLisseForget X).obj R)
        ((toProEt X).obj W)).obj
          ((completedAdicDerivedChange X φ).obj
            ((finitePerfectAdicDerivedConstant X B).obj K)) ≅
      (ringedDerivedRestrictionGeneral ((adicLisseForget X).obj R)
        ((toProEt X).obj W)).obj
          ((completedAdicDerivedChange X φ).obj
            ((finitePerfectAdicDerivedConstant X B).obj L))) : Nonempty (K ≅ L) := by
  have := koszulConstantFunctor_preservesZero X B
  let F := finitePerfectAdicDerivedConstant X B ⋙ completedAdicDerivedChange X φ
  let G := ringedDerivedRestrictionGeneral ((adicLisseForget X).obj R) ((toProEt X).obj W)
  let P := DerivedCategory.Q.objPreimage K
  let Q := DerivedCategory.Q.objPreimage L
  let a := DerivedCategory.Q.objObjPreimageIso K
  let b := DerivedCategory.Q.objObjPreimageIso L
  let c (N : CochainComplex (ModuleCat.{t} B) ℤ) :=
    G.mapIso ((completedAdicDerivedChange X φ).mapIso
      (algebraicConstantRepresentative X B N))
  obtain ⟨i⟩ := finiteConstantSlice_iso_reflects X B R φ hφ W ⟨w⟩ P Q
    ⟨(chartRestrictionIso X _ _ _).symm ≪≫ (c P).symm ≪≫
      G.mapIso (F.mapIso a) ≪≫ e ≪≫ G.mapIso (F.mapIso b).symm ≪≫ c Q ≪≫
      chartRestrictionIso X _ _ _⟩
  let Q₀ := @DerivedCategory.Q (ModuleCat.{t} B) _ _
    (finitePerfectModelsAlgebraHasDerived B)
  let Q₁ := DerivedCategory.Q (C := ModuleCat.{t} B)
  let V := HomologicalComplex.quasiIso (ModuleCat.{t} B) (.up ℤ)
  let H := Localization.uniq Q₀ Q₁ V
  let z := Localization.compUniqFunctor Q₀ Q₁ V
  exact ⟨a.symm ≪≫ (z.app P).symm ≪≫ H.functor.mapIso i ≪≫ z.app Q ≪≫ b⟩

/-- On a nonempty etale chart, perfect constant models of consecutive actual
quotients are related by the algebraic derived quotient extension. This assertion
uses no descended etale complexes or local constancy theorem.

Source: Stacks Project, proetale.tex, lemma-connected-adic-lisse (Tag 09C6),
consecutive quotient balancing; derived scalar transitivity (Tag 0D6D), and the
constant-stalk comparison (Tag 03Q3).
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-models-reduction).

Proof: apply exact slice restriction to the normalized consecutive quotient balancing
isomorphism. Derived scalar transitivity identifies the (n+1)-quotient extended along
the actual coefficient projection with the n-quotient. The two compatibility squares
for phi turn this extension into extension along A/I^(n+2) to A/I^(n+1), and identify
the two given constant coefficient realizations. Constant realization commutes with
derived scalar extension, hence gives an isomorphism between the constant realizations
of E' tensor^L (A/I^(n+1)) and E on this same chart. Pull back to its pro-etale site
using the weakly etale slice equivalence. Apply the geometric stalk at an algebraic
closure of the residue field of w. Its tensor compatibility and the constant-stalk
comparison identify this isomorphism with the coefficient-universe lift of the desired
algebraic isomorphism. Exact fully faithful universe lift reflects the isomorphism.
Perfectness permits bounded projective representatives throughout; zero rings and
zero complexes work identically. Nonemptiness is essential: on an empty chart any two
constant realizations are isomorphic. -/
theorem finitePerfectAdic_constant_models_reduction
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) (W : X.Etale) (w : W.left)
    (E' : DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1 + 1))))
    (E : DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))))
    (hE' : DerivedCategory.IsPerfect E') (hE : DerivedCategory.IsPerfect E)
    (e' : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d (n + 1))
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d (n + 1)).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d (n + 1))
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ (n + 1))).obj
            ((finitePerfectAdicDerivedConstant X (A ⧸ d.ideal ^ (n + 1 + 1))).obj E'))))
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            ((finitePerfectAdicDerivedConstant X (A ⧸ d.ideal ^ (n + 1))).obj E)))) :
    Nonempty
      ((ConstantScalarRealization.moduleDerivedExtension
        (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj E' ≅ E) := by
  have _ := hE
  let q := Ideal.Quotient.factorPowSucc d.ideal (n + 1)
  let ψ := completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)
  let U := (toProEt X).obj W
  let G := ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d n) U
  let G' := ringedDerivedRestrictionGeneral (completedAdicFiniteRing X d (n + 1)) U
  let C' := (finitePerfectAdicDerivedConstant X _).obj E'
  let C := (finitePerfectAdicDerivedConstant X _).obj E
  let N := (ConstantScalarRealization.moduleDerivedExtension q).obj E'
  obtain ⟨e'⟩ := e'
  obtain ⟨e⟩ := e
  let i' : G'.obj ((completedAdicQuotientReduction X d (n + 1)).obj M) ≅
      G'.obj ((completedAdicDerivedChange X (φ (n + 1))).obj C') :=
    chartRestrictionIso X _ U _ ≪≫ e' ≪≫ (chartRestrictionIso X _ U _).symm
  obtain ⟨a⟩ := chartScalarIso X ψ U _ _ i'
  let c := pbcReductionNormalization
    (completedAdicCommProjection X d (n + 1)) ψ (completedAdicCommProjection X d n)
    (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n)) M
  have hq : adicConstantMap X q ≫ φ n = φ (n + 1) ≫ ψ := hcompat.1 n
  let b₁ := pbcReductionNormalization (φ (n + 1)) ψ (adicConstantMap X q ≫ φ n)
    hq.symm C'
  let b₂ := pbcReductionNormalization (adicConstantMap X q) (φ n)
    (adicConstantMap X q ≫ φ n) rfl C'
  obtain ⟨s⟩ := finitePerfectAdicConstant_scalarExtension X q E' hE'
  let j : G.obj ((completedAdicDerivedChange X (φ n)).obj
      ((finitePerfectAdicDerivedConstant X _).obj N)) ≅
      G.obj ((completedAdicDerivedChange X (φ n)).obj C) :=
    G.mapIso ((completedAdicDerivedChange X (φ n)).mapIso s).symm ≪≫
      G.mapIso b₂ ≪≫ (G.mapIso b₁).symm ≪≫ a.symm ≪≫ G.mapIso c ≪≫
      chartRestrictionIso X _ U _ ≪≫ e ≪≫ (chartRestrictionIso X _ U _).symm
  exact reflectConstantIso X _ (completedAdicFiniteCommRing X d n) (φ n) (hφ n)
    W w N E j

end AlgebraicGeometry.Scheme
