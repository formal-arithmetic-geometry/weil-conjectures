/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison

/-!
# Explicit etale-origin witnesses under pullback and open extension

Source: Weil blueprint main-20261015, sec-trace-formula/sk-thm-trace-formula,
lem-trf-compactification-graph-operator.proof.md, step (3), first sentence;
Stacks Project, Tags 04JC, 03DJ and 015F (blueprint: lem-trf-witnessed-open-pullback).

The conclusion record retains the three natural comparisons and all three witnesses.
Its normalization fields specify the localization of the termwise sheaf comparisons.
Fixed-scalar modules are the presentation of the recorded FixedEtaleOriginWitness;
for A_{E,n} the coefficient ring is raised by ULift to the small sites' module universe.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The full conclusion of witness transport, including its canonical normalization.
The comparison maps are natural isomorphisms with bounded-below source. Equalities with
`mapDerivedCategoryNatIso`, conjugated by the exact composition comparisons, specify their
value on every representing complex: this construction is Localization.liftNatIso applied
to NatIso.mapHomologicalComplex. Its factorization equations and localization uniqueness
make the maps independent of the representative. The HEq fields retain the specified
isomorphisms after the accompanying equalities identify their antecedents.
Source: blueprint step (3), witness refinement; Stacks 015F, 09AF
(blueprint: lem-trf-witnessed-open-pullback). -/
structure WitnessedOpenPullbackData (A : Type (u + 1)) [CommRing A]
    {U X V Y : Scheme.{u}} (u : U ⟶ X) (j : X ⟶ Y) (i : U ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion i]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (w : Scheme.FixedEtaleOriginWitness X A K) where
  /-- The natural derived pullback comparison on D+. -/
  kappa :
    DerivedCategory.Plus.ι ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory
  /-- The natural derived open-extension comparison for j. -/
  deltaJ :
    DerivedCategory.Plus.ι ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  /-- The natural derived open-extension comparison for i. -/
  deltaI :
    DerivedCategory.Plus.ι ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory
  /-- Kappa is precisely the localization of the canonical inverse-image sheaf comparison. -/
  kappa_normalization : kappa = Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (@id
          (Etale.upperStar (ModuleCat.{u + 1} A) u ⋙
              ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
              ProEtale.upperStar (ModuleCat.{u + 1} A) u)
          (ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) u)) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
  /-- Delta_j is precisely the localization of the canonical open-extension comparison. -/
  deltaJ_normalization : deltaJ = Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (ProEtale.openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
  /-- Delta_i has the same termwise normalization. -/
  deltaI_normalization : deltaI = Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (ProEtale.openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) i) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
  /-- The retained witness for M = Lu* K. -/
  pulled : Scheme.FixedEtaleOriginWitness U A
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus.obj K)
  /-- Its antecedent is L_u = u_et^{-1} L. -/
  pulled_complex : pulled.complex =
    (Etale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus.obj w.complex
  /-- Its isomorphism is Lu* alpha after kappa_L, in categorical composition order. -/
  pulled_iso : HEq pulled.iso
    (kappa.app w.complex ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.mapIso w.iso)
  /-- The retained witness for j_! K. -/
  extendedJ : Scheme.FixedEtaleOriginWitness Y A
    ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj K)
  /-- Its antecedent is j_et! L. -/
  extendedJ_complex : extendedJ.complex =
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj
      w.complex
  /-- Its specified isomorphism is j_! alpha after delta_j,L. -/
  extendedJ_iso : HEq extendedJ.iso
    (deltaJ.app w.complex ≪≫
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.mapIso
        w.iso)
  /-- The retained witness for i_! M. -/
  extendedI : Scheme.FixedEtaleOriginWitness V A
    ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus.obj K))
  /-- Its antecedent is i_et! L_u. -/
  extendedI_complex : extendedI.complex =
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus.obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus.obj w.complex)
  /-- Its specified isomorphism is i_! alpha_u after delta_i,L_u. -/
  extendedI_iso : HEq extendedI.iso
    (deltaI.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus.obj w.complex) ≪≫
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory.mapIso
        (kappa.app w.complex ≪≫
          (ProEtale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.mapIso w.iso))

/-- Derived pullback and both open extensions transport the given explicit witness,
with their termwise normalization and all objects bounded below.
Source: blueprint lem-trf-compactification-graph-operator, proof (3), first sentence,
and its explicit derived/open-extension refinement; Stacks 04JC, 03DJ, 015F
(blueprint: lem-trf-witnessed-open-pullback).

Proof plan, following the node's seven steps:
1. Etale and comparison inverse images are exact on abelian sheaves by
   prop-weil-pbc-inverse-image-exact and lem-weil-pbc-site-pullback-abelian-exact.
   Apply them to scalar endomorphisms to obtain the fixed-A module inverse images.
   Kernels and sheafified cokernels give module exactness; the constant-ring
   coefficient identification in def-weil-pbc-proetale-operations identifies its
   exact pullback with this fixed-scalar presentation.
2. Both open extensions are exact, by lem-weil-pbc-extension-by-zero-exact and
   lem-weil-extension-by-zero-exact. The coefficient ring A_{E,n} is finite.
   The recorded intrinsic extension is the same fixed-scalar extension conjugated
   by sfIntrinsicModuleEquivalence.
3. Use lem-weil-pbc-exact-functor-derived-factorization to descend these exact
   functors termwise. By lem-weil-pbc-exact-functor-bounded-below their cohomology
   is the functor applied to the original cohomology, preserving every lower bound.
4. Naturality of the canonical sheaf pullback comparison in scalar maps and
   differentials makes its termwise components an A-linear chain isomorphism.
   Lem-weil-pbc-localization-universal-property gives kappa with that normalization;
   uniqueness makes it independent of representing complexes.
5. Apply the same argument to lem-cbc-proetale-extension-zero-comparison to obtain
   delta_j and delta_i. This is exactly mapDerivedCategoryNatIso with the
   composition identifications, restricted along DerivedCategory.Plus.ι.
6. Compose kappa_L with Lu* alpha. Its inverse is the reversed composite of the
   inverse isomorphisms. Retain L_u itself as the antecedent, giving pulled.
7. Compose delta_j,L with j_! alpha and delta_i,L_u with i_! alpha_u to give the
   other two specified witnesses. Every object lies in D+ by step 3; the minimum
   of the original two cohomological lower bounds is a common lower bound.
The argument includes the empty schemes, identity maps, and zero complexes. -/
theorem witnessed_open_pullback (T : TraceFormulaCoefficientConventions.{u})
    (U X V Y : Over (Spec (CommRingCat.of T.datum.k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (u : U ⟶ X) (j : X ⟶ Y) (i : U ⟶ V)
    [IsOpenImmersion j.left] [IsOpenImmersion i.left]
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X.left)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing))))
    (w : Scheme.FixedEtaleOriginWitness X.left (ULift.{u + 1, u} T.coefficientRing) K) :
    Nonempty (WitnessedOpenPullbackData (ULift.{u + 1, u} T.coefficientRing)
      u.left j.left i.left K w) := by
  suffices h : ∀ (A : Type (u + 1)) [CommRing A]
      (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X.left)
        (ModuleCat.{u + 1} A)))
      (w : Scheme.FixedEtaleOriginWitness X.left A K),
      Nonempty (WitnessedOpenPullbackData A u.left j.left i.left K w) by
    exact h (ULift.{u + 1, u} T.coefficientRing) K w
  intro A inst K w
  let B := ModuleCat.{u + 1} A
  let κ : DerivedCategory.Plus.ι ⋙ (Etale.upperStar B u.left).mapDerivedCategory ⋙
      (ProEtale.comparisonUpperStar B U.left).mapDerivedCategory ≅
    DerivedCategory.Plus.ι ⋙ (ProEtale.comparisonUpperStar B X.left).mapDerivedCategory ⋙
      (ProEtale.upperStar B u.left).mapDerivedCategory :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso (Etale.upperStar B u.left)
        (ProEtale.comparisonUpperStar B U.left)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (@id
            (Etale.upperStar B u.left ⋙ ProEtale.comparisonUpperStar B U.left ≅
              ProEtale.comparisonUpperStar B X.left ⋙ ProEtale.upperStar B u.left)
            (ProEtale.supportSiteComparisonCoefficientPullbackIso B u.left)) ≪≫
        Functor.mapDerivedCategoryCompIso (ProEtale.comparisonUpperStar B X.left)
          (ProEtale.upperStar B u.left))
  let δj : DerivedCategory.Plus.ι ⋙
      (Etale.openImmersionLowerShriek B j.left).mapDerivedCategory ⋙
      (ProEtale.comparisonUpperStar B Y.left).mapDerivedCategory ≅
    DerivedCategory.Plus.ι ⋙ (ProEtale.comparisonUpperStar B X.left).mapDerivedCategory ⋙
      (ProEtale.openImmersionLowerShriek B j.left).mapDerivedCategory :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso (Etale.openImmersionLowerShriek B j.left)
        (ProEtale.comparisonUpperStar B Y.left)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso B j.left) ≪≫
        Functor.mapDerivedCategoryCompIso (ProEtale.comparisonUpperStar B X.left)
          (ProEtale.openImmersionLowerShriek B j.left))
  let δi : DerivedCategory.Plus.ι ⋙
      (Etale.openImmersionLowerShriek B i.left).mapDerivedCategory ⋙
      (ProEtale.comparisonUpperStar B V.left).mapDerivedCategory ≅
    DerivedCategory.Plus.ι ⋙ (ProEtale.comparisonUpperStar B U.left).mapDerivedCategory ⋙
      (ProEtale.openImmersionLowerShriek B i.left).mapDerivedCategory :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso (Etale.openImmersionLowerShriek B i.left)
        (ProEtale.comparisonUpperStar B V.left)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso B i.left) ≪≫
        Functor.mapDerivedCategoryCompIso (ProEtale.comparisonUpperStar B U.left)
          (ProEtale.openImmersionLowerShriek B i.left))
  let γ : (ProEtale.comparisonUpperStar B U.left).mapDerivedCategory.obj
      ((Etale.upperStar B u.left).mapDerivedCategory.obj w.complex.obj) ≅
      (ProEtale.upperStar B u.left).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar B X.left).mapDerivedCategory.obj w.complex.obj) :=
    κ.app w.complex
  let β : (ProEtale.upperStar B u.left).mapDerivedCategory.obj
      ((ProEtale.comparisonUpperStar B X.left).mapDerivedCategory.obj w.complex.obj) ≅
      (ProEtale.upperStar B u.left).mapDerivedCategory.obj K.obj :=
    (ProEtale.upperStar B u.left).mapDerivedCategory.mapIso w.iso
  let αu : (ProEtale.comparisonUpperStar B U.left).mapDerivedCategory.obj
      ((Etale.upperStar B u.left).mapDerivedCategory.obj w.complex.obj) ≅
      (ProEtale.upperStar B u.left).mapDerivedCategory.obj K.obj :=
    Iso.trans (C := DerivedCategory (Sheaf (Scheme.ProEt.topology U.left) B))
      (X := (ProEtale.comparisonUpperStar B U.left).mapDerivedCategory.obj
        ((Etale.upperStar B u.left).mapDerivedCategory.obj w.complex.obj))
      (Y := (ProEtale.upperStar B u.left).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar B X.left).mapDerivedCategory.obj w.complex.obj))
      (Z := (ProEtale.upperStar B u.left).mapDerivedCategory.obj K.obj) γ β
  let γj : (ProEtale.comparisonUpperStar B Y.left).mapDerivedCategory.obj
      ((Etale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj w.complex.obj) ≅
      (ProEtale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar B X.left).mapDerivedCategory.obj w.complex.obj) :=
    δj.app w.complex
  let βj : (ProEtale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj
      ((ProEtale.comparisonUpperStar B X.left).mapDerivedCategory.obj w.complex.obj) ≅
      (ProEtale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj K.obj :=
    (ProEtale.openImmersionLowerShriek B j.left).mapDerivedCategory.mapIso w.iso
  let αj : (ProEtale.comparisonUpperStar B Y.left).mapDerivedCategory.obj
      ((Etale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj w.complex.obj) ≅
      (ProEtale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj K.obj :=
    Iso.trans (C := DerivedCategory (Sheaf (Scheme.ProEt.topology Y.left) B))
      (X := (ProEtale.comparisonUpperStar B Y.left).mapDerivedCategory.obj
        ((Etale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj w.complex.obj))
      (Y := (ProEtale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar B X.left).mapDerivedCategory.obj w.complex.obj))
      (Z := (ProEtale.openImmersionLowerShriek B j.left).mapDerivedCategory.obj K.obj) γj βj
  let Lu := (Etale.upperStar B u.left).mapDerivedCategoryPlus.obj w.complex
  let γi : (ProEtale.comparisonUpperStar B V.left).mapDerivedCategory.obj
      ((Etale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj Lu.obj) ≅
      (ProEtale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar B U.left).mapDerivedCategory.obj Lu.obj) :=
    δi.app Lu
  let βi : (ProEtale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj
      ((ProEtale.comparisonUpperStar B U.left).mapDerivedCategory.obj Lu.obj) ≅
      (ProEtale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj
        ((ProEtale.upperStar B u.left).mapDerivedCategory.obj K.obj) :=
    (ProEtale.openImmersionLowerShriek B i.left).mapDerivedCategory.mapIso αu
  let αi : (ProEtale.comparisonUpperStar B V.left).mapDerivedCategory.obj
      ((Etale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj Lu.obj) ≅
      (ProEtale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj
        ((ProEtale.upperStar B u.left).mapDerivedCategory.obj K.obj) :=
    Iso.trans (C := DerivedCategory (Sheaf (Scheme.ProEt.topology V.left) B))
      (X := (ProEtale.comparisonUpperStar B V.left).mapDerivedCategory.obj
        ((Etale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj Lu.obj))
      (Y := (ProEtale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar B U.left).mapDerivedCategory.obj Lu.obj))
      (Z := (ProEtale.openImmersionLowerShriek B i.left).mapDerivedCategory.obj
        ((ProEtale.upperStar B u.left).mapDerivedCategory.obj K.obj)) γi βi
  refine ⟨{
    kappa := κ
    deltaJ := δj
    deltaI := δi
    kappa_normalization := rfl
    deltaJ_normalization := rfl
    deltaI_normalization := rfl
    pulled := {
      complex := (Etale.upperStar B u.left).mapDerivedCategoryPlus.obj w.complex
      iso := αu }
    pulled_complex := rfl
    pulled_iso := HEq.rfl
    extendedJ := {
      complex := (Etale.openImmersionLowerShriek B j.left).mapDerivedCategoryPlus.obj
        w.complex
      iso := αj }
    extendedJ_complex := rfl
    extendedJ_iso := HEq.rfl
    extendedI := {
      complex := (Etale.openImmersionLowerShriek B i.left).mapDerivedCategoryPlus.obj
        ((Etale.upperStar B u.left).mapDerivedCategoryPlus.obj w.complex)
      iso := αi }
    extendedI_complex := rfl
    extendedI_iso := HEq.rfl }⟩

end WeilConjectures
