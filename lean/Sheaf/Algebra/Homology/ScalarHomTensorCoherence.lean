/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomData
import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Paper.ResolvingRepresentativeWhiskering

/-! # Coherence of normalized scalar tensor comparisons

Source: Stacks 07A4 and 0D6D. The pure-generator equations determine the chain
comparisons before their coherence descends to unbounded derived categories.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures SheafOfModules CategoryTheory.Functor
namespace CategoryTheory.ScalarHomTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R : Sheaf J CommRingCat.{max c v r}}
attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] monoidalCategory
private theorem total_pure_hom_ext
    (P Q : CochainComplex (scalarModules J R) ℤ) (n : ℤ)
    (H : scalarModules J R)
    {f g : ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X n ⟶ H}
    (hh : ∀ (p q : ℤ) (h : p + q = n) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      f.val.app V (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y) =
        g.val.app V (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y)) :
    f = g := by
  let := monoidalCategory R
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext R (P.X p) (Q.X q) H
  intro V x y
  exact hh p q h V x y

variable [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
  (M : ScalarHomModels.{c, v, r, w} J) {S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

private theorem complexIso_unique (μ ν : ScalarHomTensorComparison M a)
    (P Q : CochainComplex (scalarModules J R) ℤ) :
    (μ.complexIso P Q).hom = (ν.complexIso P Q).hom := by
  let s := M.scalar a
  let := s.extension_additive
  apply HomologicalComplex.Hom.ext
  funext n
  apply (s.ordinaryAdjunction.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply total_pure_hom_ext
  intro p q h V x y
  change ((μ.complexIso P Q).hom.f n).val.app V
      (scalarHomUnitSection M a _ V
        (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y)) =
    ((ν.complexIso P Q).hom.f n).val.app V
      (scalarHomUnitSection M a _ V
        (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y))
  exact (μ.generators P Q p q n h V x y).trans (ν.generators P Q p q n h V x y).symm

private theorem tensorIso_unique (μ ν : ScalarHomTensorComparison M a) :
    μ.iso = ν.iso := by
  let A := scalarModules J R
  let B := scalarModules J S
  let s := M.scalar a
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  apply Iso.ext
  apply ff'.map_injective
  apply NatTrans.ext
  funext X
  let P := X.1.obj
  let Q := X.2.obj
  have hp : PR P := X.1.property
  have hq : PR Q := X.2.property
  change μ.iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    ν.iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let eps (Y : CochainComplex A ℤ) := scalarPairComplexComparison s.extension
    s.extension_additive s.derived s.counit Y
  have heps (Y : CochainComplex A ℤ) (hy : PR Y) : IsIso (eps Y) :=
    s.computes Y hy
  have := heps P hp
  have := heps Q hq
  have : IsIso (Prod.mkHom (eps P) (eps Q)) := by
    change IsIso ((asIso (eps P)).prod (asIso (eps Q))).hom
    infer_instance
  apply (cancel_epi (s.derived.map
    (CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R) P Q hp hq).hom)).mp
  apply (cancel_mono ((M.closed S).tensor.map (Prod.mkHom (eps P) (eps Q)))).mp
  have hm := μ.normalization P Q hp hq
  have hn := ν.normalization P Q hp hq
  rw [complexIso_unique M a μ ν P Q] at hm
  simpa only [Category.assoc] using hm.trans hn.symm

private theorem comparison_unique (μ ν : ScalarHomTensorComparison M a) : μ = ν := by
  have hi := tensorIso_unique M a μ ν
  have hc : μ.complexIso = ν.complexIso :=
    funext (fun P ↦ funext (fun Q ↦ Iso.ext (complexIso_unique M a μ ν P Q)))
  cases μ
  cases ν
  cases hc
  cases hi
  rfl

end CategoryTheory.ScalarHomTensor

namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J) {R S : Sheaf J CommRingCat.{max c v r}}

/-- The normalized derived scalar tensor comparisons respect the unit-normalized
left-adjoint composition and identity comparisons.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0D6D.
(blueprint: lem-sfb-scalar-hom-tensor-coherence).

Proof: the proved total_pure_hom_ext and complexIso_unique helpers show that
chain maps and the specified chain comparisons are determined by their pure generators.
The proved tensorIso_unique helper then cancels the representative comparison
isomorphisms and uses fully faithful K-flat restriction to prove derived uniqueness.
Proof irrelevance then gives comparison_unique for the entire normalized comparison.
Identify the unit-normalized extension comparison on a K-flat representative
with t tensor (s tensor x) mapped to t b(s) tensor x. The inverse inserts 1. Choose the
representatives with flat terms. Ordinary tensor
cancellation and exact conservative restriction preserve flat terms under scalar
extension, and the given comparison preserves K-flatness. Thus every intermediate
representative computes its derived scalar pair. The
unit identity identifies this with leftAdjointUniq. Evaluate the two tensor routes
on each total pure generator: each sends t tensor (s tensor (x tensor y)) to
(t b(s) tensor x) tensor (1 tensor y). The specified generator equations for the
three chain tensor comparisons give this equality. Equivalently the existing
cochainPullbackTensorCoherence supplies this chain square for identity geometric
inverse images, after identifying its normalized maps by complexIso_unique.
Tensor balancing, sheafification and coproduct generation extend it to the total
complexes. The normalization squares
and fully faithful restriction to K-flat representatives descend it to the stated
derived equation. For the identity map, scalar multiplication identifies extension
with the identity; the same generator argument gives the identity equation.
No coefficient map is assumed flat; scalar extension preserves K-flat complexes. -/
theorem scalarHomTensorCoherence
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a) :
    (∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
      (X Y : DerivedCategory (scalarModules J R)),
      (M.scalar b).derived.map ((μ a).iso.hom.app (X, Y)) ≫
          (μ b).iso.hom.app ((M.scalar a).derived.obj X, (M.scalar a).derived.obj Y) ≫
            (M.closed T).tensor.map (Prod.mkHom
              ((scalarHomExtensionComp M a b).hom.app X)
              ((scalarHomExtensionComp M a b).hom.app Y)) =
        (scalarHomExtensionComp M a b).hom.app ((M.closed R).tensor.obj (X, Y)) ≫
          (μ (a ≫ b)).iso.hom.app (X, Y)) ∧
    (∀ (R : Sheaf J CommRingCat.{max c v r})
      (X Y : DerivedCategory (scalarModules J R)),
      (M.closed R).tensor.map (Prod.mkHom
          ((scalarHomExtensionId M R).inv.app X) ((scalarHomExtensionId M R).inv.app Y)) =
        (scalarHomExtensionId M R).inv.app ((M.closed R).tensor.obj (X, Y)) ≫
          (μ (𝟙 R)).iso.hom.app (X, Y)) := by
  sorry

end CategoryTheory
