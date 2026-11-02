/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Ordinary condensed middle image and its canonical Weil structure

Source: latest blueprint, def-wf-middle-extension, ordinary direct-image and
zeroth-derived identification clauses (blueprint: def-wf-middle-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {U₀ C₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]

/-- The actual base change of the model open immersion to the fixed algebraic closure.
Source: latest blueprint, U and C (blueprint: def-wf-middle-extension). -/
abbrev geometricMap (j₀ : U₀ ⟶ C₀) :
    (D.geometricFiber U₀).left ⟶ (D.geometricFiber C₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left

/-- Model base change commutes with geometric Frobenius.
Source: latest blueprint, induced Weil-structure convention
(blueprint: def-wf-middle-extension).
Proof: compose both sides with the two fibre-product projections. On the model
projection both are j₀ after projection. On the coefficient projection both are
projection followed by inverse q-power Frobenius. Pullback uniqueness gives the square.
This records the canonical structural equality, not an extra assumption on the sheaf. -/
theorem frobeniusSquare (j₀ : U₀ ⟶ C₀) :
    CommSq (D.geometricFrobenius U₀).hom (geometricMap D j₀)
      (geometricMap D j₀) (D.geometricFrobenius C₀).hom := by
  constructor
  apply pullback.hom_ext
  · simp [geometricMap, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, AlgebraicGeometry.baseChangeMap,
      Category.assoc]
  · simp [geometricMap, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, AlgebraicGeometry.baseChangeMap,
      Category.assoc]

/-- The ordinary module direct image; for a lisse sheaf on a smooth curve it is j_*F.
Source: latest blueprint, displayed middle-extension definition
(blueprint: def-wf-middle-extension). -/
abbrev middleImage (j₀ : U₀ ⟶ C₀) :=
  CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D j₀)

/-- The canonical H⁰(Rj_*F[0]) identification for this same ordinary module direct image.
Source: latest blueprint, degree-zero identification (blueprint: def-wf-middle-extension). -/
def middleImageDegreeZeroIso (j₀ : U₀ ⟶ C₀) :
    DerivedCategory.singleFunctor _ 0 ⋙ (middleImage D l j₀).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ 0 ≅ middleImage D l j₀ :=
  (middleImage D l j₀).singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso

/-- Ordinary sheaf direct image put in degree zero and shifted by one.
Source: latest blueprint, final shift convention (blueprint: def-wf-middle-extension). -/
def shiftedMiddleImage (j₀ : U₀ ⟶ C₀) :=
  middleImage D l j₀ ⋙ DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)

/-- Ordinary middle extension of a lisse sheaf on a smooth curve is constructible.
Source: latest blueprint, constructibility sentence (blueprint: def-wf-middle-extension).
Proof: lissity gives constructibility on the single stratum U. The single sheaf in
D^b_c(U) is sent to D^b_c(C) by Rj_*. Take H⁰ and use middleImageDegreeZeroIso to
identify it with the ordinary module direct image. No positive-degree vanishing is used. -/
theorem middleImage_constructible (j₀ : U₀ ⟶ C₀)
    [IsSeparated C₀.hom] [SmoothOfRelativeDimension 1 C₀.hom]
    [IsOpenImmersion j₀.left] [IsDominant j₀.left] (_hl : l ≠ D.p)
    (M : NativeCondensedModule.Modules l (D.geometricFiber U₀).left)
    (_hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber C₀).left ((middleImage D l j₀).obj M) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have : Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩
  have : Fact (ringChar D.k ≠ l) := ⟨by rw [ringChar.eq D.k D.p]; exact _hl.symm⟩
  have : IsSeparated U₀.hom := by
    rw [← Over.w j₀]
    infer_instance
  let X := D.geometricFiber U₀
  let Y := D.geometricFiber C₀
  let f : X ⟶ Y :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀
  have : LocallyOfFiniteType X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsSeparated X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : LocallyOfFiniteType Y.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd C₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact Y.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd C₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsSeparated Y.hom :=
    inferInstanceAs (IsSeparated (pullback.snd C₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj l) X.left) M := by
    let S : Scheme.Stratification X.left :=
      { n := 1
        stratum := fun _ ↦ Set.univ
        isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
        isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
        iUnion_stratum_eq_univ := Set.iUnion_const _
        pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
        domain := fun _ ↦ X.left
        immersion := fun _ ↦ 𝟙 X.left
        range_immersion := fun _ ↦ Set.range_id' }
    exact ⟨S, fun _ ↦ localFinitePresentation_pullback (𝟙 X.left)
      (heart_lfp_of_lisse (Profinite.padicAlgClRingObj l) _hM)⟩
  have hsingle := CondensedRing.boundedConstructible_singleFunctor_obj
    (Profinite.padicAlgClRingObj l) X.left 0 M hM
  have hderived := CondensedRing.boundedConstructible_rightDerivedLowerStar_obj l f
    ⟨_, hsingle⟩
  have hpush : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y.left)
      ((middleImage D l j₀).obj M) :=
    _root_.constructible_of_iso ((middleImageDegreeZeroIso D l j₀).app M) (hderived.2 0)
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  exact (adicConstructibilityPredicateComparison l Y.left
    (Profinite.padicAlgClRingObj l) .algebraicClosure).1 _ |>.mp hpush

/-- Frobenius base change is invertible because both Frobenius arrows are isomorphisms.
Source: latest blueprint, the induced Weil structure (blueprint: def-wf-middle-extension).
Proof: use the module upper/lower-star base-change isomorphism for a commutative square
whose two horizontal Frobenius maps are isomorphisms. Its inverse is the mate for the
inverse Frobenius square; naturality and the two adjunction triangle identities show
that the two composites are identities. The existing isIso_lowerStarBaseChange_of_isIso
instance is precisely this natural-transformation statement. -/
theorem middleBaseChange_isIso (j₀ : U₀ ⟶ C₀) :
    IsIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
      (frobeniusSquare D j₀)) := by
  infer_instance

/-- The induced Weil structure is the canonical Frobenius base-change mate followed by
j_* of the given Weil structure. Invertibility uses the two Frobenius automorphisms.
Source: latest blueprint, ordinary middle image with its Weil structure
(blueprint: def-wf-middle-extension). -/
@[irreducible] def middleWeilImage (j₀ : U₀ ⟶ C₀) (M : WeilModule D l U₀) : WeilModule D l C₀ :=
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (@asIso _ _ _ _
      (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
        (frobeniusSquare D j₀)) (middleBaseChange_isIso D l j₀))).obj M

end WeilConjectures.NativeL2
