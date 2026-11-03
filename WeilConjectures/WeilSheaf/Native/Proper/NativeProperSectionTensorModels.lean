/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperSectionAdjunctionModels
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
import WeilConjectures.WeilSheaf.Native.Proper.NativeProperSectionTensorDescent
import WeilConjectures.WeilSheaf.Native.Proper.NativeProperKFlatPullTensorSquare
import WeilConjectures.WeilSheaf.Native.NativePullSheafTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-! # Tensor comparison for normalized native section adjunctions

Source: Stacks 07A4, 0G7E; native proper-projection model proof, step 4.
No realization data or direct-image comparison is constructed by this lemma.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  AlgebraicGeometry.Scheme.ContinuousRational.modulePull
  AlgebraicGeometry.Scheme.ContinuousRational.derivedPull

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures Opposite
open WeilConjectures.AdicQbarRealization
open AlgebraicGeometry.Scheme
open scoped TensorProduct AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

variable
  (R : LocallyFiniteAdicRealization.Realization l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (S : LocallyFiniteAdicRealization.Realization l
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
  [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
  (O : Proper.Operations l (NativeBaseChange.geometricMap k₀ p) R S)

variable
  (A : At l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R)
  (B : At l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S)
  (C : Proper.TensorComparison l (NativeBaseChange.geometricMap k₀ p) R S O A B)
  (J : NativeProperSectionAdjunctionModels k₀ l p R S O)

private theorem binary_ext_of_representatives
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {I : Type w} (Q : I → C) (flat : I → Prop)
    (hQ : ∀ X : C, ∃ P, flat P ∧ Nonempty (Q P ≅ X))
    {F G : C × C ⥤ D} (α β : F ⟶ G)
    (h : ∀ P T, flat P → flat T → α.app (Q P, Q T) = β.app (Q P, Q T)) :
    α = β := by
  apply NatTrans.ext
  funext X
  obtain ⟨P, hP, ⟨e⟩⟩ := hQ X.1
  obtain ⟨T, hT, ⟨f⟩⟩ := hQ X.2
  let g : (Q P, Q T) ≅ X := Iso.prod e f
  apply (cancel_epi (F.map g.hom)).mp
  rw [α.naturality g.hom, β.naturality g.hom, h P T hP hT]

private theorem tensor_square_of_representatives
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {I : Type*} (Q : I → C) (flat : I → Prop)
    (hQ : ∀ X : C, ∃ P, flat P ∧ Nonempty (Q P ≅ X))
    (P : C ⥤ D) (U : D ⥤ H) (V : C ⥤ E) (L : E ⥤ H)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (TE : E × E ⥤ E) (TH : H × H ⥤ H)
    (mu : TC ⋙ P ≅ P.prod P ⋙ TD)
    (tZ : TD ⋙ U ≅ U.prod U ⋙ TH)
    (tY : TC ⋙ V ≅ V.prod V ⋙ TE)
    (pull : P ⋙ U ≅ V ⋙ L)
    (c : TE ⋙ L ≅ L.prod L ⋙ TH)
    (h : ∀ M N, flat M → flat N →
      U.map (mu.hom.app (Q M, Q N)) ≫
        tZ.hom.app (P.obj (Q M), P.obj (Q N)) ≫
        TH.map (Prod.mkHom (pull.hom.app (Q M)) (pull.hom.app (Q N))) =
      pull.hom.app (TC.obj (Q M, Q N)) ≫
        L.map (tY.hom.app (Q M, Q N)) ≫
        c.hom.app (V.obj (Q M), V.obj (Q N))) :
    ∀ M N,
      U.map (mu.hom.app (M, N)) ≫ tZ.hom.app (P.obj M, P.obj N) ≫
        TH.map (Prod.mkHom (pull.hom.app M) (pull.hom.app N)) =
      pull.hom.app (TC.obj (M, N)) ≫ L.map (tY.hom.app (M, N)) ≫
        c.hom.app (V.obj M, V.obj N) := by
  let α : TC ⋙ P ⋙ U ⟶ V.prod V ⋙ L.prod L ⋙ TH :=
    Functor.whiskerRight mu.hom U ≫ Functor.whiskerLeft (P.prod P) tZ.hom ≫
      Functor.whiskerRight (NatTrans.prod pull.hom pull.hom) TH
  let β : TC ⋙ P ⋙ U ⟶ V.prod V ⋙ L.prod L ⋙ TH :=
    Functor.whiskerLeft TC pull.hom ≫ Functor.whiskerRight tY.hom L ≫
      Functor.whiskerLeft (V.prod V) c.hom
  have hab : α = β := binary_ext_of_representatives Q flat hQ α β h
  intro M N
  exact congrArg (fun t ↦ t.app (M, N)) hab

private theorem models_of_kflat_tensor_square
    (hz : Nonempty (ProperSectionTensor k₀ l Z R A))
    (hy : Nonempty (ProperSectionTensor k₀ l Y S B))
    (hflat : ∀ (TZ : ProperSectionTensor k₀ l Z R A)
      (TY : ProperSectionTensor k₀ l Y S B),
      ∃ balanced : NativeProjectionTensorComparison k₀ l p,
      ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ),
      NativeIsKFlat k₀ l Y P → NativeIsKFlat k₀ l Y Q →
      (properSectionDerived k₀ l Z R).map
          (balanced.mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        TZ.tensor.hom.app
          ((nativeOpenPull k₀ l p).obj (DerivedCategory.Q.obj P),
            (nativeOpenPull k₀ l p).obj (DerivedCategory.Q.obj Q)) ≫
        A.closed.tensor.map (Prod.mkHom
          (J.pull.hom.app (DerivedCategory.Q.obj P))
          (J.pull.hom.app (DerivedCategory.Q.obj Q))) =
      J.pull.hom.app ((nativeDerivedTensor k₀ l Y).obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (ContinuousRational.derivedPull
          (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
            (TY.tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        C.tensor.hom.app
          ((properSectionDerived k₀ l Y S).obj (DerivedCategory.Q.obj P),
            (properSectionDerived k₀ l Y S).obj (DerivedCategory.Q.obj Q))) :
    ∃ (TZ : ProperSectionTensor k₀ l Z R A) (TY : ProperSectionTensor k₀ l Y S B)
      (balanced : NativeProjectionTensorComparison k₀ l p),
    ∀ M N,
    (properSectionDerived k₀ l Z R).map (balanced.mu.hom.app (M, N)) ≫
      TZ.tensor.hom.app
        ((nativeOpenPull k₀ l p).obj M, (nativeOpenPull k₀ l p).obj N) ≫
      A.closed.tensor.map (Prod.mkHom (J.pull.hom.app M) (J.pull.hom.app N)) =
    J.pull.hom.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      (ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          (TY.tensor.hom.app (M, N)) ≫
      C.tensor.hom.app
        ((properSectionDerived k₀ l Y S).obj M,
          (properSectionDerived k₀ l Y S).obj N) := by
  obtain ⟨TZ⟩ := hz
  obtain ⟨TY⟩ := hy
  obtain ⟨balanced, hb⟩ := hflat TZ TY
  refine ⟨TZ, TY, balanced, ?_⟩
  exact tensor_square_of_representatives
    (fun P ↦ DerivedCategory.Q.obj P) (NativeIsKFlat k₀ l Y)
    (native_two_sided_kflat_representatives k₀ l Y)
    (nativeOpenPull k₀ l p) (properSectionDerived k₀ l Z R)
    (properSectionDerived k₀ l Y S)
    (ContinuousRational.derivedPull (NativeBaseChange.geometricMap k₀ p) O.coefficient)
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
    B.closed.tensor A.closed.tensor balanced.mu TZ.tensor TY.tensor J.pull C.tensor hb

/-- The tensor part of the native proper-projection resolution calculation.
Source: Stacks 07A4, 0G7E and BS 6.8.14--6.8.15; native proper-projection model
proof, step 4 (blueprint: lem-sf-native-proper-section-tensor-models).

Proof: construct the section tensor comparison on sheaves from the identity on
underlying balanced tensors. For complexes, take the direct sum of these maps on
all (i,j) summands. Its generator formula is precisely ProperSectionTensor.generators;
both differentials are d tensor 1 plus (-1)^i 1 tensor d. The inverse is obtained
by the same underlying tensor universal property. The exact section equivalence
and the exact orbit-induction adjunction transfer both quasi-isomorphism tests for
K-flatness. Forgetting native K-flat complexes is K-flat: test against an ordinary
acyclic complex Q by its exact orbit induction, whose underlying complex is the
direct sum of all Frobenius translates of Q. The ordinary tensor with Q is the
split degree-zero summand of the forgotten acyclic total tensor. Thus it too is
acyclic. Apply the same argument in the other tensor variable. Tensor descent
therefore gives TZ and TY, with the stated representative equation on every
K-flat pair, by uniqueness of the tensor-Hom adjunction comparisons.

For p, use the balanced sheaf maps b tensor (x tensor y) maps to
(b tensor x) tensor (1 tensor y), and the inverse multiplies coefficients.
They commute with Frobenius by the coefficient precomposition equation. Their
termwise totalizations retain each summand insertion. For arbitrary K-flat inputs,
use the enough-points stalk criterion and
the inverse-image theorem for ringed sites with enough points; the small pro-etale
site has enough points. The flat-term preservation theorem applies separately to
the chosen flat-term resolutions. The ordinary section coordinates and exact
forgetting identify the required native K-flat tests. Localization constructs
balanced with its presentation, compatibility,
sheaf_forget and representative normalizations. Compute the square on simultaneous
K-flat resolutions. C.representative and TZ.representative and TY.representative
identify its four sides with these same balanced sheaf maps; no extra signs appear.
The pull in J is the canonical one: pushSections and pushRepresentative fix its
right comparison on K-injectives, and J.counit fixes its left adjoint mate. Thus it
is this localized sheaf pull comparison. The two insertion formulas agree on every
pure tensor, proving the square; localization and naturality give it for arbitrary
M and N. Empty sites, zero inputs and identity p use the same formulas. -/
theorem native_proper_section_tensor_models
    (hR : (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence)
    (hS : (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S).IsEquivalence) :
    ∃ (TZ : ProperSectionTensor k₀ l Z R A) (TY : ProperSectionTensor k₀ l Y S B)
      (balanced : NativeProjectionTensorComparison k₀ l p),
    ∀ M N,
    (properSectionDerived k₀ l Z R).map (balanced.mu.hom.app (M, N)) ≫
      TZ.tensor.hom.app
        ((nativeOpenPull k₀ l p).obj M, (nativeOpenPull k₀ l p).obj N) ≫
      A.closed.tensor.map (Prod.mkHom (J.pull.hom.app M) (J.pull.hom.app N)) =
    J.pull.hom.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      (ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          (TY.tensor.hom.app (M, N)) ≫
      C.tensor.hom.app
        ((properSectionDerived k₀ l Y S).obj M,
          (properSectionDerived k₀ l Y S).obj N) := by
  have hz : Nonempty (ProperSectionTensor k₀ l Z R A) := by
    obtain ⟨cochain, tensor, generators, representative⟩ :=
      native_proper_section_tensor_descent k₀ l Z R A hR
    exact ⟨{
      cochain := cochain
      generators := generators
      kflat := native_two_sided_kflat_sections k₀ l Z R
      tensor := tensor
      representative := representative }⟩
  have hy : Nonempty (ProperSectionTensor k₀ l Y S B) := by
    obtain ⟨cochain, tensor, generators, representative⟩ :=
      native_proper_section_tensor_descent k₀ l Y S B hS
    exact ⟨{
      cochain := cochain
      generators := generators
      kflat := native_two_sided_kflat_sections k₀ l Y S
      tensor := tensor
      representative := representative }⟩
  obtain ⟨rho, hrho⟩ := native_pull_sheaf_tensor k₀ l p
  exact models_of_kflat_tensor_square k₀ l p R S O A B C J hz hy
    (fun TZ TY ↦ native_proper_kflat_pull_tensor_square
      k₀ l p R S O A B C J hR hS rho hrho TZ TY)

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical pullback tensor comparisons commute with the specified square
comparison on the underlying condensed derived categories. For a Frobenius square,
this is the tensor compatibility used to put Weil structures on pullback and on the
projection composite.

Source: latest blueprint, lem-fix-weil-operations.proof.md, paragraph 2 and final
paragraph (blueprint: lem-sf-condensed-proper-section-tensor-models).
Proof: the pullback tensorators are the existing signed K-flat total comparisons.
Their compatibility with composition identifies each boundary with the tensorator
for the composite pullback. Equality transport across the commuting square respects
tensor. Cancel the two inverse compositors. This gives the square on all derived
objects, including zero objects and empty schemes, without section realizations. -/
theorem native_proper_section_tensor_models
    {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g)
    (M N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((p')^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ g).app M).app N) ≫
        ((leftDerivedUpperStarTensor Λ p').app _).app _ ≫
        ((pullbackSquareComparison Λ sq).hom.app M ⊗ₘ
          (pullbackSquareComparison Λ sq).hom.app N) =
      (pullbackSquareComparison Λ sq).hom.app (M ⊗ N) ≫
        L((g')^*⟦Λ⟧).map (((leftDerivedUpperStarTensor Λ p).app M).app N) ≫
        ((leftDerivedUpperStarTensor Λ g').app _).app _ := by
  exact pullbackSquareComparison_tensor Λ sq M N

end AlgebraicGeometry.ProEtale.CondensedRing
