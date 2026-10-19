/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralDerivedReduction
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible

import Sheaf.Paper.ProjectiveHomologyZeroDifferentialModel
import Sheaf.Paper.CompleteResidueTopCell
import Sheaf.Paper.BoundedProjectiveModelsExtensions
import Sheaf.Paper.WeaklyContractibleUnitProjective
import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts
import all Sheaf.Algebra.Homology.KFlatResolutionGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Integral finite free models from constant residue cohomology

Source: Stacks Project, proetale.tex, Tag 09C3 
(blueprint: lem-sf-complete-constant-residue-free-model).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZeroObject MonoidalCategory
open AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem tor_cohomology_bounds
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj K) := by
  classical
  let R := proEtaleConstantRing X A
  let C := proEtaleRingModules X R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  have := SheafOfModules.monoidalPreadditive_kfg R
  let := HasDerivedCategory.standard C
  let L := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
  have : QuasiIso f := hf
  let t : derivedTensor X A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C)) P f hf hP ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  intro i hi
  exact (h.2 L P ⟨e⟩ f hf hP (MonoidalCategory.tensorUnit C) i hi).of_iso
    ((DerivedCategory.homologyFunctor C i).mapIso t.symm)

set_option synthInstance.maxSize 2048 in
private theorem tor_of_free_model
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (a b : ℤ) (hab : a ≤ b) (hge : P.IsStrictlyGE a) (hle : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (P.X i ≅ ∏ᶜ fun _ : Fin n ↦
      SheafOfModules.unit ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)))) :
    HasProEtaleTorAmplitude X A (DerivedCategory.Q.obj P) a b := by
  classical
  let R := proEtaleConstantRing X A
  let C := proEtaleRingModules X R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  have := SheafOfModules.monoidalPreadditive_kfg R
  have := SheafOfModules.isGrothendieckAbelian_kfg R
  have := SheafOfModules.hasFunctorialFlatResolution_kfg R
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let := HasDerivedCategory.standard C
  let : MonoidalCategory (CochainComplex C ℤ) := inferInstance
  let : MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
  have := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) :=
    DerivedCategory.instMonoidalCategory_weilConjectures C
  have hflat (i : ℤ) : ObjectProperty.flat (P.X i) := by
    obtain ⟨n, ⟨e⟩⟩ := hfree i
    apply ObjectProperty.prop_of_iso _ e.symm
    let f : Fin n → C := fun _ ↦ 𝟙_ C
    exact ObjectProperty.prop_of_isLimit _ (limit.isLimit (Discrete.functor f))
      (fun _ ↦ ObjectProperty.prop_unit _)
  have : P.IsStrictlyGE a := hge
  have : P.IsStrictlyLE b := hle
  have hmono := DerivedCategory.torAmplitudeIn_Q_obj_of_flat P a b hflat
  have hk (P : CochainComplex C ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hright : HomotopyCategory.subcategoryAcyclic C
        (MonoidalCategory.tensorObj ((HomotopyCategory.quotient C (.up ℤ)).obj N)
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hright, hright⟩
  refine ⟨hab, ?_⟩
  rintro L Q ⟨e⟩ f hf hQ M i hi
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let eq : MonoidalCategory.tensorObj (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≅
      derivedTensor X A L ((HomologicalComplex.single C (.up ℤ) 0).obj M) Q f hf hQ :=
    MonoidalCategory.tensorIso (asIso (DerivedCategory.Q.map f)).symm (Iso.refl _) ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft Q _ (hk Q hQ)
  let eq' := MonoidalCategory.tensorIso e.symm
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app M) ≪≫ eq
  have hz : IsZero ((DerivedCategory.homologyFunctor C i).obj
      (MonoidalCategory.tensorObj (DerivedCategory.Q.obj P)
        ((DerivedCategory.singleFunctor C 0).obj M))) := by
    obtain ⟨hge', hle'⟩ := (DerivedCategory.homologyConcentratedIn_iff _ _ _).1 (hmono M)
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ a).1 hge' i hi
    · exact (DerivedCategory.isLE_iff _ b).1 hle' i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso eq'.symm)

private theorem finitePower_biprod_iso
    {C : Type*} [Category C] [Abelian C] [HasFiniteProducts C]
    (B : C) (m n : ℕ) :
    Nonempty (((∏ᶜ fun _ : Fin m ↦ B) ⊞ (∏ᶜ fun _ : Fin n ↦ B)) ≅
      ∏ᶜ fun _ : Fin (m + n) ↦ B) := by
  let f : Fin m → C := fun _ ↦ B
  let g : Fin n → C := fun _ ↦ B
  let c := Fan.mk ((∏ᶜ f) ⊞ (∏ᶜ g))
    (Fan.combPairHoms (limit.cone (Discrete.functor f))
      (limit.cone (Discrete.functor g)) (BinaryBiproduct.bicone (∏ᶜ f) (∏ᶜ g)).toCone)
  have hc : IsLimit c := Fan.combPairIsLimit (limit.isLimit _)
    (limit.isLimit _) (BinaryBiproduct.isLimit _ _)
  let e := hc.conePointUniqueUpToIso (limit.isLimit (Discrete.functor (Sum.elim f g)))
  have hfg : Sum.elim f g = fun _ : Fin m ⊕ Fin n ↦ B := by
    funext i
    cases i <;> rfl
  refine ⟨e ≪≫ ?_⟩
  rw [hfg]
  exact Pi.reindex finSumFinEquiv (fun _ : Fin (m + n) ↦ B)


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- On a weakly contractible affine, a complete complex with finite free residue
cohomology and finite residue Tor amplitude has a bounded finite free sheaf model.

Source: Stacks Project, proetale.tex, Tag 09C3, top-degree cone induction;
Tag 09C2 for integral cohomological bounds; derived.tex Tag 064B for derived maps
(blueprint: lem-sf-complete-constant-residue-free-model).

Proof:
1. Choose an interval [a,b] for residue Tor amplitude. Exact evaluation on the
weakly contractible affine makes finite free sheaves projective. Lift a basis in
each residue cohomology degree to cycles; this gives a bounded finite free
zero-differential residue model. Integral cohomology lies in [a,b] by 09C2.
2. The completed coefficient ring is flat over the constant valuation ring and
its quotient by the nth uniformizer power is the nth constant quotient sheaf.
Thus the two-term free uniformizer complex resolves that quotient. It is K-flat,
and the surjective quotient tower shows the coefficient unit, its finite sums
and shifts are derived complete.
3. Induct on b-a. The uniformizer triangle and the top cohomological bound make
H^b(K) to H^b(K_1) epimorphic. Exact evaluation lifts the top residue basis to
integral cycles and hence defines a derived map B^r[-b] to K. Its reduction is
the inclusion of the top summand in the zero-differential residue model.
4. Its cone L is complete. Its residue is the lower-degree split residue model
plus a contractible identity complex. Hence it has finite free cohomology and
Tor amplitude [a,b-1]. If a=b its residue is zero, so derived Nakayama gives
L=0 and the one-term model of K.
5. Otherwise induction gives a bounded finite free model Q of L. Bounded
projective complexes compute derived maps, so represent the connecting map
L to B^r[-b+1] by a chain map from Q. Its shifted mapping cone represents K;
its terms are Q below b and B^r in degree b. The chain equation supplies the
last differential and proves its square zero. These are sheaf-linear maps,
with no requirement that their coefficients be constant.
Zero residue gives the zero complex by derived Nakayama; rank zero is allowed. -/
theorem complete_constant_residue_free_model
    (S : Scheme.{u}) (hS : IsAffine S)
    (hweak : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 S)))
    (K : DerivedCategory (integralTowerModules.{u, u} l E S))
    (hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E S K)
    (hTor : HasFiniteProEtaleTorAmplitude S
      (Padic.coefficientExtensionRing l E 1)
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K))
    (hfree : ∀ q : ℤ, ∃ N : ℕ, Nonempty
      (((DerivedCategory.homologyFunctor
        (proEtaleRingModules S (proEtaleConstantRing S
          (Padic.coefficientExtensionRing l E 1))) q).obj
        ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)) ≅
        ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E S 0))) :
    ∃ (P : CochainComplex (integralTowerModules.{u, u} l E S) ℤ) (a b : ℤ),
      a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ r : ℤ, ∃ N : ℕ, Nonempty
        (P.X r ≅ ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E S))) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  let C := integralTowerModules.{u, u} l E S
  let B : C := SheafOfModules.unit
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E S)
  let F (X : C) : Prop := ∃ N : ℕ, Nonempty (X ≅ ∏ᶜ fun _ : Fin N ↦ B)
  have hiso {X Y : C} (e : X ≅ Y) (hX : F X) : F Y := by
    obtain ⟨N, ⟨f⟩⟩ := hX
    exact ⟨N, ⟨e.symm ≪≫ f⟩⟩
  have hbiprod (X Y : C) (hX : F X) (hY : F Y) : F (X ⊞ Y) := by
    obtain ⟨m, ⟨eX⟩⟩ := hX
    obtain ⟨n, ⟨eY⟩⟩ := hY
    obtain ⟨e⟩ := finitePower_biprod_iso B m n
    exact ⟨m + n, ⟨biprod.mapIso eX eY ≪≫ e⟩⟩
  have hprojective (X : C) (hX : F X) : Projective X := by
    obtain ⟨N, ⟨e⟩⟩ := hX
    exact Projective.of_iso e.symm
      (finitePower_unit_projective_of_weaklyContractible S hweak _ N)
  let M (L : DerivedCategory C) : Prop :=
    ∃ (P : CochainComplex C ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ (∀ r, F (P.X r)) ∧
      Nonempty (L ≅ DerivedCategory.Q.obj P)
  have hzero (L : DerivedCategory C) (hL : IsZero L) : M L := by
    let P : CochainComplex C ℤ := 0
    have hzP : IsZero P := isZero_zero _
    have hX (i : ℤ) : IsZero (P.X i) :=
      (HomologicalComplex.eval C (.up ℤ) i).map_isZero hzP
    have hge : P.IsStrictlyGE 0 := by
      rw [CochainComplex.isStrictlyGE_iff]
      exact fun i _ ↦ hX i
    have hle : P.IsStrictlyLE 0 := by
      rw [CochainComplex.isStrictlyLE_iff]
      exact fun i _ ↦ hX i
    refine ⟨P, 0, 0, hge, hle, fun i ↦ ⟨0, ⟨?_⟩⟩, ?_⟩
    · refine { hom := 0, inv := 0, hom_inv_id := ?_, inv_hom_id := ?_ }
      · exact (hX i).eq_of_src _ _
      · apply Pi.hom_ext
        intro j
        exact Fin.elim0 j
    · exact ⟨hL.iso (DerivedCategory.Q.map_isZero hzP)⟩
  let R (L : DerivedCategory C) : Prop := ∀ q : ℤ, ∃ N : ℕ, Nonempty
    (((DerivedCategory.homologyFunctor
      (proEtaleRingModules S (proEtaleConstantRing S
        (Padic.coefficientExtensionRing l E 1))) q).obj
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj L)) ≅
      ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E S 0))
  have hsplit (L : DerivedCategory C) (hr : R L) (a b : ℤ)
      (ht : HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E 1)
        ((scalarReductionDerivedExtension.{u, u} l E S 0).obj L) a b) :
      ∃ V : CochainComplex
          (proEtaleRingModules S (proEtaleConstantRing S
            (Padic.coefficientExtensionRing l E 1))) ℤ,
        (∀ i j : ℤ, V.d i j = 0) ∧
        (∀ q : ℤ, ∃ n : ℕ, Nonempty (V.X q ≅ ∏ᶜ fun _ : Fin n ↦
          SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E S 0))) ∧
        (∀ q : ℤ, q < a ∨ b < q → IsZero (V.X q)) ∧
        Nonempty (((scalarReductionDerivedExtension.{u, u} l E S 0).obj L) ≅
          DerivedCategory.Q.obj V) := by
    let A := proEtaleRingModules S (proEtaleConstantRing S
      (Padic.coefficientExtensionRing l E 1))
    let N := (scalarReductionDerivedExtension.{u, u} l E S 0).obj L
    let V := DerivedCategory.Q.objPreimage N
    let eV : DerivedCategory.Q.obj V ≅ N := DerivedCategory.Q.objObjPreimageIso N
    have hp (q : ℤ) : Projective (V.homology q) := by
      obtain ⟨n, ⟨e⟩⟩ := hr q
      let eH := ((DerivedCategory.homologyFunctorFactors A q).app V).symm ≪≫
        (DerivedCategory.homologyFunctor A q).mapIso eV ≪≫ e
      exact Projective.of_iso eH.symm
        (finitePower_unit_projective_of_weaklyContractible S hweak _ n)
    obtain ⟨W, f, hW, hd, hf⟩ :=
      CochainComplex.exists_zero_differential_model_of_projective_homology V hp
    have : QuasiIso f := hf
    refine ⟨W, hd, ?_, ?_, ⟨eV.symm ≪≫ (asIso (DerivedCategory.Q.map f)).symm⟩⟩
    · intro q
      obtain ⟨n, ⟨e⟩⟩ := hr q
      rw [hW q]
      exact ⟨n, ⟨((DerivedCategory.homologyFunctorFactors A q).app V).symm ≪≫
        (DerivedCategory.homologyFunctor A q).mapIso eV ≪≫ e⟩⟩
    · intro q hq
      rw [hW q]
      exact (tor_cohomology_bounds S (Padic.coefficientExtensionRing l E 1) N a b ht q hq).of_iso
         (((DerivedCategory.homologyFunctorFactors A q).app V).symm ≪≫
          (DerivedCategory.homologyFunctor A q).mapIso eV)
  obtain ⟨a, b, hinterval⟩ := hTor
  have hab : a ≤ b := hinterval.1
  have induction_step : ∀ d : ℕ, ∀ L : DerivedCategory C,
      IsDerivedCompleteUnrestricted.{u, u} l E S L →
      HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E 1)
        ((scalarReductionDerivedExtension.{u, u} l E S 0).obj L) a (a + d) →
      R L → M L := by
    intro d
    induction d with
    | zero =>
      intro L hc ht hr
      obtain ⟨V, hV, hVfree, hVbound, eV⟩ := hsplit L hr a _ ht
      obtain ⟨T, hT, ⟨e⟩, ⟨P, hge, hle, hP, he⟩, _, hz, _⟩ :=
        complete_residue_top_cell l E S hS hweak L hc a 0 ht V hV hVfree hVbound eV
      obtain ⟨Q, c, e', hgeQ, hleQ, hQ, ⟨eQ⟩⟩ :=
        DerivedCategory.bounded_projective_models_extensions F hiso hbiprod hprojective T hT
          ⟨P, a + (0 : ℕ), a + (0 : ℕ), hge, hle, hP, he⟩ (hzero _ (hz rfl))
      exact ⟨Q, c, e', hgeQ, hleQ, hQ, ⟨e.symm ≪≫ eQ⟩⟩
    | succ d ih =>
      intro L hc ht hr
      obtain ⟨V, hV, hVfree, hVbound, eV⟩ := hsplit L hr a _ ht
      obtain ⟨T, hT, ⟨e⟩, ⟨P, hge, hle, hP, he⟩, hcT, _, htT⟩ :=
        complete_residue_top_cell l E S hS hweak L hc a (d + 1) ht V hV hVfree hVbound eV
      obtain ⟨W, hWge, hWle, hWd, hWfree, ⟨eW⟩⟩ := htT d rfl
      have htW := tor_of_free_model S (Padic.coefficientExtensionRing l E 1)
        W a (a + d) (by omega) hWge hWle hWfree
      have htCone : HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E 1)
          ((scalarReductionDerivedExtension.{u, u} l E S 0).obj T.obj₃) a (a + d) := by
        refine ⟨htW.1, ?_⟩
        rintro L Q ⟨eL⟩ f hf hQ M i hi
        exact htW.2 L Q ⟨eL ≪≫ eW⟩ f hf hQ M i hi
      have hrCone : R T.obj₃ := by
        intro q
        have : IsIso (W.iCycles q) := W.isIso_iCycles q (q + 1) (by simp) (hWd _ _)
        have : IsIso (W.homologyπ q) := W.isIso_homologyπ (q - 1) q (by simp) (hWd _ _)
        obtain ⟨n, ⟨e⟩⟩ := hWfree q
        refine ⟨n, ⟨(DerivedCategory.homologyFunctor _ q).mapIso eW ≪≫
          (DerivedCategory.homologyFunctorFactors _ q).app W ≪≫
          (asIso (W.homologyπ q)).symm ≪≫ asIso (W.iCycles q) ≪≫ e⟩⟩
      obtain ⟨Q, c, e', hgeQ, hleQ, hQ, ⟨eQ⟩⟩ :=
        DerivedCategory.bounded_projective_models_extensions F hiso hbiprod hprojective T hT
          ⟨P, a + (d + 1 : ℕ), a + (d + 1 : ℕ), hge, hle, hP, he⟩
          (ih T.obj₃ hcT htCone hrCone)
      exact ⟨Q, c, e', hgeQ, hleQ, hQ, ⟨e.symm ≪≫ eQ⟩⟩
  have hd : a + ((b - a).toNat : ℤ) = b := by omega
  have hm := induction_step (b - a).toNat K hcomplete (by simpa only [hd] using hinterval)
    hfree
  obtain ⟨P, c, e, hge, hle, hP, he⟩ := hm
  have hge' : P.IsStrictlyGE (min c e) :=
    P.isStrictlyGE_of_ge (min c e) c (min_le_left _ _)
  exact ⟨P, min c e, e, min_le_right _ _, hge', hle, hP, he⟩

end WeilConjectures
