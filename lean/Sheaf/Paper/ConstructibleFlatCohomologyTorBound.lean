/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q105, C1
-/
module

public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ULift
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Bounded locally constant residue cohomology gives Tor bounds on every slice

Source: Stacks Project, proetale.tex, Tag 09C3, finite residue Tor-amplitude input;
sites-modules.tex, Tags 03ER, 03DJ and 08FC; sites-cohomology.tex, Tags 06YS and 06YU
(blueprint: lem-fix-constructible-flat-cohomology-tor-bound).

The finite coefficient index zero denotes exponent one. Vanishing is vanishing of
module sheaves on the actual localized site, with arbitrary test module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v r w
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open MonoidalCategory

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-- Sheafification on a slice in a universe containing both site and coefficients.
Source: Stacks 03DA (blueprint: lem-fix-constructible-flat-cohomology-tor-bound). -/
instance residueTorSliceAbSheafify (V : Scheme.{t}) (U : V.ProEt) :
    HasSheafify ((ProEt.topology V).over U) AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective criterion on that same slice.
Source: Stacks 03DA (blueprint: lem-fix-constructible-flat-cohomology-tor-bound). -/
instance residueTorSliceAbLocallyBijective (V : Scheme.{t}) (U : V.ProEt) :
    ((ProEt.topology V).over U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Standard localization for all residue coefficient sheaves on the global site.
Source: Stacks 05RU (blueprint: lem-fix-constructible-flat-cohomology-tor-bound). -/
instance residueTorGlobalDerived (V : Scheme.{t})
    (R : Sheaf (ProEt.topology V) RingCat.{max u (t + 1)}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)} R) :=
  HasDerivedCategory.standard _

/-- Standard localization on the actual slice, including either definitionally
identical order of coefficient restriction and forgetting commutativity.
Source: Stacks 05RU (blueprint: lem-fix-constructible-flat-cohomology-tor-bound). -/
instance residueTorSliceDerived (V : Scheme.{t}) (U : V.ProEt)
    (R : Sheaf ((ProEt.topology V).over U) RingCat.{max u (t + 1)}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)} R) :=
  HasDerivedCategory.standard _

private theorem residueTensorPreadditive
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r}) :
    let := SheafOfModules.monoidalCategory R
    MonoidalPreadditive (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let A := SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  have (M : A) : (tensorLeft M).Additive :=
    SheafOfModules.tensorLeft_additive_independent R M
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

set_option maxRecDepth 2048 in
private theorem residueTensorLeftQuasiIso
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{r}}
    {P E E' : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (α : E ⟶ E') (hα : QuasiIso α) (hP : P.IsKFlatIndependentCoefficients) :
    let := SheafOfModules.monoidalCategory R
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 P) α (curriedTensor _) (.up ℤ)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := residueTensorPreadditive R
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hP (CochainComplex.mappingCone α) hc
  let F := curriedTensor (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj P) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj P) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (P.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (P.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (P.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor P (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso P (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso P α F)

-- Flatness of the test sheaf suffices: localize tensoring with the selected K-flat
-- resolution, replace the second representative by the actual single complex,
-- and compute homology with the exact ordinary tensor functor.
set_option maxRecDepth 2048 in
private lemma residueTensorVanishing
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (K : DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (L : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hL : SheafOfModules.IsFlatOnSite (J := J) (R := R) L) (i : ℤ)
    (hi : IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (SheafOfModules.ringedSiteDerivedTensorOfUniverses R K
        ((DerivedCategory.singleFunctor _ 0).obj L))) := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := residueTensorPreadditive R
  let A := SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let Q := DerivedCategory.Q.{w} (C := A)
  let H := DerivedCategory.homologyFunctor A i
  let K₀ := Q.objPreimage K
  let L₀ := Q.objPreimage ((DerivedCategory.singleFunctor A 0).obj L)
  let res := CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K₀
  let P := res.choose
  let f := res.choose_spec.choose
  have hP : P.IsKFlatIndependentCoefficients := res.choose_spec.choose_spec.1
  have hf : QuasiIso f := res.choose_spec.choose_spec.2.2.1
  have : IsIso (Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso A f).2 hf
  let eK : Q.obj P ≅ K := asIso (Q.map f) ≪≫ Q.objObjPreimageIso K
  have hzP : IsZero (P.homology i) := hi.of_iso
    (((DerivedCategory.homologyFunctorFactors A i).app P).symm ≪≫ H.mapIso eK)
  let T := tensorRight L
  have hT : exactFunctor A A T := (exactFunctor A A).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R L) hL
  have : PreservesFiniteLimits T := hT.1
  have : PreservesFiniteColimits T := hT.2
  have hzT : IsZero (((T.mapHomologicalComplex (.up ℤ)).obj P).homology i) :=
    (T.map_isZero hzP).of_iso ((P.sc i).mapHomologyIso T)
  let B := ((curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj P
  have hinv : (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy (B ⋙ Q) := by
    intro X Y g hg
    have hg' : QuasiIso g := (HomologicalComplex.mem_quasiIso_iff _).1 hg
    have ht : QuasiIso (B.map g) := residueTensorLeftQuasiIso g hg' hP
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 ht
  let D := Localization.lift (B ⋙ Q) hinv Q
  let fac : Q ⋙ D ≅ B ⋙ Q := Localization.fac (B ⋙ Q) hinv Q
  let S := (CochainComplex.singleFunctor A 0).obj L
  let eL : Q.obj L₀ ≅ Q.obj S := Q.objObjPreimageIso _ ≪≫
    (DerivedCategory.singleFunctorIsoCompQ A 0).app L
  let e : Q.obj (B.obj L₀) ≅ Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj P) :=
    (fac.app L₀).symm ≪≫ D.mapIso eL ≪≫ fac.app S ≪≫
      Q.mapIso ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor A) L).app P)
  exact (hzT.of_iso ((DerivedCategory.homologyFunctorFactors A i).app _)).of_iso
    (H.mapIso e)

private lemma residueIdealMaximal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  simpa only [Padic.coefficientExtensionIdeal, pow_one, hgen] using hm

-- The local field-section argument also applies to the restriction of a constant ring.
private lemma flat_of_local_field_sections
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] [HasSheafify J AddCommGrpCat.{max c v r}]
    (κ : Type (max c v r)) [Field κ] (R : Sheaf J CommRingCat.{max c v r})
    (η : (Functor.const Cᵒᵖ).obj (RingCat.of κ) ⟶
      R.obj ⋙ forget₂ CommRingCat RingCat)
    (hη : Presheaf.IsLocallySurjective J η)
    (N : SheafOfModules.{max c v r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) N := by
  classical
  apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{c, v,
    max c v r, max c v r} R N).2
  intro U n a s hs
  let S : J.Cover U := Finset.univ.inf fun p : Fin n ↦
    ⟨Presheaf.imageSieve η (a p), Presheaf.imageSieve_mem J η (a p)⟩
  refine ⟨S.val, S.property, ?_⟩
  intro V f hf
  have hlift (p : Fin n) : ∃ z : κ, (η.app (Opposite.op V)) z =
      R.obj.map f.op (a p) := by
    have hp : S ≤ (⟨Presheaf.imageSieve η (a p),
        Presheaf.imageSieve_mem J η (a p)⟩ : J.Cover U) :=
      Finset.inf_le (Finset.mem_univ p)
    exact hp f hf
  choose z hz using hlift
  let ρ : κ →+* R.obj.obj (Opposite.op V) := (η.app (Opposite.op V)).hom
  let : Module κ (N.val.obj (Opposite.op V)) := Module.compHom _ ρ
  have heq : (∑ p : Fin n, z p •
      (show N.val.obj (Opposite.op V) from N.val.map f.op (s p))) = 0 := by
    change (∑ p : Fin n, ρ (z p) • N.val.map f.op (s p)) = 0
    simp_rw [show ∀ p, ρ (z p) = R.obj.map f.op (a p) from hz]
    have hh := congrArg (fun x ↦ (show N.val.obj (Opposite.op V) from
      N.val.map f.op x)) hs
    rw [map_sum, map_zero] at hh
    have hh' : (∑ p : Fin n, (show N.val.obj (Opposite.op V) from
        N.val.map f.op (a p • s p))) = 0 := hh
    calc
      _ = ∑ p : Fin n, (show N.val.obj (Opposite.op V) from
          N.val.map f.op (a p • s p)) := by
        apply Finset.sum_congr rfl
        intro p _
        exact (N.val.map_smul f.op (a p) (s p)).symm
      _ = 0 := hh'
  have : Module.Flat κ (N.val.obj (Opposite.op V)) := inferInstance
  obtain ⟨k, b, x, hb, hbx⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero heq
  refine ⟨k, fun p q ↦ ρ (b p q), x, hb, ?_⟩
  intro q
  simp_rw [← hz]
  change (∑ p : Fin n, ρ (z p) * ρ (b p q)) = 0
  simpa only [map_sum, map_mul, map_zero] using congrArg ρ (hbx q)

/-- Bounded locally constant finite-dimensional residue cohomology gives the same
Tor interval after restriction to every localized site. Module.Finite for the residue
field is exactly finite dimensionality; the coefficient sheaf is R/(varpi), not a
field of characteristic zero. Source: Stacks 09C3, finite residue Tor-amplitude input;
08J5, 03ER, 03DJ, 03EL, 06YQ, 06YS and 06YU
(blueprint: lem-fix-constructible-flat-cohomology-tor-bound).

Proof:
1. The exponent-one coefficient ideal is the maximal ideal, so its quotient is a field.
On a slice, sections of its constant ring sheaf locally come from this field, by the
locally surjective restricted constant-ring unit. Every module sheaf L on that slice is
flat: lift the finitely many coefficients of a relation on their common covering sieve,
view its section module as a vector space over the field, apply the ordinary module
flat relation criterion, and map its factorization coefficients back to the ring sheaf.
The local equational criterion gives exactness of tensoring with L (Stacks 08FC).
2. Exact slice restriction preserves homology, so the given support bound holds for
the recorded restriction of K_1 (Stacks 03DJ).
3. Resolve the canonical representative of this restriction by the selected K-flat P.
Tensoring with P preserves quasi-isomorphisms in the second variable: its mapping cone
is the tensor of an acyclic cone, which is acyclic by K-flatness and signed symmetry.
Localize this functor to replace the second canonical representative by L[0]. The
single-complex tensor comparison identifies the result with termwise tensoring P by L.
4. By step 1 this ordinary tensor functor is exact. Its homology is therefore the tensor
of the homology of P with L, and vanishes in every degree where the original homology
vanishes. These comparisons are all on the localized site, for the arbitrary L.
The finite-dimensional local models, affineness, weak contractibility and completeness
are not needed for this constant-field argument. -/
theorem constructible_flat_cohomology_tor_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (V : Scheme.{t}) [IsAffine V]
    (_hV : (ProEt.topology V).IsWeaklyContractible.{max u (t + 1)} (ProEt.mk (𝟙 V)))
    (K : DerivedCategory (scalarReductionSource l E V))
    (_hcomplete : IntegralOnSlice.IsComplete l E V none K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hbounded : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((scalarReductionDerivedExtension l E V 0).obj K)))
    (_hlocal : ∀ q : ℤ,
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses V
        (Padic.coefficientExtensionRing l E 1)
        (fun M ↦ Module.Finite (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1)) M)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((scalarReductionDerivedExtension l E V 0).obj K))) :
    ∀ (U : V.ProEt)
      (L : SheafOfModules.{max u (t + 1)} ((integralCoefficientSheaf l E V 0).over U))
      (i : ℤ), i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (SheafOfModules.ringedSiteDerivedTensorOfUniverses.{t + 1, t,
            max u (t + 1), (max u (t + 1)) + 1}
          ((integralCoefficientCommRingSheaf l E V 0).over U)
          (ringedSiteDerivedRestrictionOfUniverses.{t + 1, t, max u (t + 1),
              max u (t + 1), (max u (t + 1)) + 1, (max u (t + 1)) + 1}
            (integralCoefficientSheaf l E V 0) U
            ((scalarReductionDerivedExtension l E V 0).obj K))
          ((DerivedCategory.singleFunctor _ 0).obj L))) := by
  intro U L i hi
  let O := integralCoefficientCommRingSheaf l E V 0
  let R := integralCoefficientSheaf l E V 0
  let F := SheafOfModules.overFunctor.{max u (t + 1)} R U
  have : F.Additive := (SheafOfModules.localizedSystemExact.{t + 1, t, u} O U).2.2.2.1
  have : PreservesFiniteLimits F :=
    (SheafOfModules.localizedSystemExact.{t + 1, t, u} O U).2.2.2.2.1
  have : PreservesFiniteColimits F :=
    (SheafOfModules.localizedSystemExact.{t + 1, t, u} O U).2.2.2.2.2
  let K₁ := (scalarReductionDerivedExtension l E V 0).obj K
  let Q := DerivedCategory.Q.{(max u (t + 1)) + 1}
    (C := SheafOfModules.{max u (t + 1)} R)
  let P := Q.objPreimage K₁
  have hz : IsZero (P.homology i) := (_hbounded i hi).of_iso
    (((DerivedCategory.homologyFunctorFactors _ i).app P).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (Q.objObjPreimageIso K₁))
  have hz' : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj P).homology i) :=
    (F.map_isZero hz).of_iso ((P.sc i).mapHomologyIso F)
  have hslice : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (ringedSiteDerivedRestrictionOfUniverses.{t + 1, t, max u (t + 1),
        max u (t + 1), (max u (t + 1)) + 1, (max u (t + 1)) + 1} R U K₁)) :=
    hz'.of_iso ((DerivedCategory.homologyFunctorFactors.{(max u (t + 1)) + 1} _ i).app _)
  have hflat : SheafOfModules.IsFlatOnSite (J := (ProEt.topology V).over U)
      (R := O.over U) L := by
    let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := residueIdealMaximal l E
    let : Field (Padic.coefficientExtensionRing l E 1) :=
      Ideal.Quotient.field (Padic.coefficientExtensionIdeal l E 1)
    let κ := ULift.{t + 1} (Padic.coefficientExtensionRing l E 1)
    let : Field κ := inferInstanceAs
      (Field (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1)))
    let η := Functor.whiskerLeft (Over.forget U).op
      (Functor.whiskerRight (toSheafify (ProEt.topology V)
        ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of κ)))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}))
    exact flat_of_local_field_sections.{t + 1, t, u} κ (O.over U) η
      (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses V
        (Padic.coefficientExtensionRing l E 1) U).2 L
  exact residueTensorVanishing.{t + 1, t, max u (t + 1),
    (max u (t + 1)) + 1} (O.over U)
    (ringedSiteDerivedRestrictionOfUniverses.{t + 1, t, max u (t + 1),
        max u (t + 1), (max u (t + 1)) + 1, (max u (t + 1)) + 1} R U K₁) L hflat i hslice

end WeilConjectures
