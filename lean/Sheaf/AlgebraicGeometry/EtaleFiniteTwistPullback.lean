/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistLocalBases
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistSignedCoherence
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistExponentLine
/-!
# Finite Tate sheaves and inverse image
Source: Stacks Project, Etale Cohomology, Tags 03PK and 03Q1; Modules on Sites,
Tags 03EK and 03EM; Cohomology on Sites, Tags 07A4 and 0G7E
(blueprint: lem-asd-etale-finite-twist-pullback).
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
open scoped ChangeOfRings

private noncomputable def finiteTwistRootsIso (m : ℕ) (hm : 0 < m)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))) :
    (Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
      T'.rootsOfUnitySheaf m := by
  letI : NeZero m := ⟨hm.ne'⟩
  haveI := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit m v hT
  exact asIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf m v)

private theorem finiteTwistRootsIso_normalization (m : ℕ) (hm : 0 < m)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))) :
    (Etale.upperStar AddCommGrpCat.{u + 1} v).map (kernel.ι (m • 𝟙 T.gmSheaf)) ≫
        upperStarGmSheafToGmSheaf v =
      (finiteTwistRootsIso m hm v hT).hom ≫ kernel.ι (m • 𝟙 T'.gmSheaf) :=
  (upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι m v).symm

private noncomputable def finiteTwistRootPower (m m' : ℕ) (hdiv : m ∣ m')
    (T : Scheme.{u}) : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m :=
  kernel.lift (m • 𝟙 T.gmSheaf) ((m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf)) (by
    have hz : m' • kernel.ι (m' • 𝟙 T.gmSheaf) = 0 := by
      simpa only [Preadditive.comp_nsmul, Category.comp_id] using
        kernel.condition (m' • 𝟙 T.gmSheaf)
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.comp_id,
      smul_smul, Nat.div_mul_cancel hdiv, hz])

private theorem finiteTwistRootPower_normalization (m m' : ℕ) (hdiv : m ∣ m')
    (T : Scheme.{u}) :
    finiteTwistRootPower m m' hdiv T ≫ kernel.ι (m • 𝟙 T.gmSheaf) =
      (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf) :=
  kernel.lift_ι _ _ _

private theorem finiteTwistDualEvaluation
    {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
    {X Y : C} (e : X ≅ Y) (U : C) :
    tensorHom e.hom (MonoidalClosed.ihomIsoOfIsoLeft e U).hom ≫ (ihom.ev Y).app U =
      (ihom.ev X).app U := by
  change tensorHom e.hom ((MonoidalClosed.pre e.inv).app U) ≫ _ = _
  rw [MonoidalCategory.tensorHom_def, Category.assoc, MonoidalClosed.id_tensor_pre_app_comp_ev,
    ← comp_whiskerRight_assoc, e.hom_inv_id, id_whiskerRight, Category.id_comp]

private noncomputable def finiteTwistNonnegativeIso
    (A : Type (u + 1)) [CommRing A] (m m' : ℕ) (T : Scheme.{u})
    (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (e : finiteEtaleTateLine T m' A hA' ≅ finiteEtaleTateLine T m A hA) :
    ∀ n : ℕ, finiteEtaleTateTwist T m' A hA' n ≅ finiteEtaleTateTwist T m A hA n
  | 0 => Iso.refl _
  | 1 => e
  | n + 2 => tensorIso (finiteTwistNonnegativeIso A m m' T hA hA' e (n + 1)) e

private noncomputable def finiteTwistSignedIso
    (A : Type (u + 1)) [CommRing A] (m m' : ℕ) (T : Scheme.{u})
    (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (e : finiteEtaleTateLine T m' A hA' ≅ finiteEtaleTateLine T m A hA) :
    ∀ a : ℤ, finiteEtaleTateSheaf A m' T hA' a ≅ finiteEtaleTateSheaf A m T hA a
  | .ofNat n => finiteTwistNonnegativeIso A m m' T hA hA' e n
  | .negSucc n => MonoidalClosed.ihomIsoOfIsoLeft
      (finiteTwistNonnegativeIso A m m' T hA hA' e (n + 1))
      (finiteEtaleTateSheaf A m T hA 0)

private theorem finiteTwistSignedIso_evaluation
    (A : Type (u + 1)) [CommRing A] (m m' : ℕ) (T : Scheme.{u})
    (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (e : finiteEtaleTateLine T m' A hA' ≅ finiteEtaleTateLine T m A hA) (n : ℕ) :
    tensorHom (finiteTwistSignedIso A m m' T hA hA' e (.ofNat (n + 1))).hom
        (finiteTwistSignedIso A m m' T hA hA' e (.negSucc n)).hom ≫
      (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
        (finiteEtaleTateSheaf A m T hA 0) =
      (ihom.ev (finiteEtaleTateSheaf A m' T hA' (.ofNat (n + 1)))).app
        (finiteEtaleTateSheaf A m' T hA' 0) :=
  finiteTwistDualEvaluation (finiteTwistNonnegativeIso A m m' T hA hA' e (n + 1)) _

private theorem finiteTwistDerivedComparison
    (A : Type (u + 1)) [CommRing A] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (F' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A))
    (e : (Etale.upperStar (ModuleCat.{u + 1} A) v).obj F ≅ F') (b : ℤ) :
    ∃ d : ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
        ((DerivedCategory.singleFunctor _ 0).obj F) ⋙ shiftFunctor _ b) ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ⋙
        Etale.derivedTensorRight (ModuleCat.{u + 1} A) T'
          ((DerivedCategory.singleFunctor _ 0).obj F') ⋙ shiftFunctor _ b),
      ∀ K : Etale.DerivedCategoryModule A T,
        d.app K =
          ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.commShiftIso b).app
            (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
              ((DerivedCategory.singleFunctor _ 0).obj F)) ≪≫
          (shiftFunctor _ b).mapIso
            (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v K
              ((DerivedCategory.singleFunctor _ 0).obj F) ≪≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) T').obj
              ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K)).mapIso
              ((Etale.singleFunctorCompLeftDerivedUpperStarIso
                (ModuleCat.{u + 1} A) v).app F ≪≫
              (DerivedCategory.singleFunctor _ 0).mapIso e)) := by
  let L := (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor
  let M := (DerivedCategory.singleFunctor _ 0).obj F
  let ee := (Etale.singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} A) v).app F ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e
  let d := Functor.isoWhiskerLeft (Etale.derivedTensorRight (ModuleCat.{u + 1} A) T M)
      (L.commShiftIso b) ≪≫
    Functor.isoWhiskerRight
      (Etale.derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v M)
      (shiftFunctor _ b) ≪≫
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight
      ((Etale.derivedTensorRightFunctor (ModuleCat.{u + 1} A) T').mapIso ee)
      (shiftFunctor _ b))
  refine ⟨d, ?_⟩
  intro K
  apply Iso.ext
  simp [d, Etale.derivedTensorRightCompLeftDerivedUpperStarIso,
    Etale.derivedTensorRightFunctor, Etale.derivedTensorRight, ee, L, M]

set_option synthInstance.maxSize 2048 in
/-- Finite Tate sheaves are locally free lines, with the normalized inverse-image
comparisons, their signed tensor products, and exponent-change comparisons.
Source: Stacks Project, Tags 03PK, 03Q1, 03EK, 03EM, 07A4 and 0G7E
(blueprint: lem-asd-etale-finite-twist-pullback).
Proof plan:
1. Apply `lem-asd-finite-etale-twist-line` to `ℤ/m` to trivialize the roots sheaf.
   Extend its cyclic basis to `A`. This uses only `m A = 0`, not finiteness or flatness
   of `A`. Tensor powers and the dual basis trivialize all signed powers on this cover.
2. Over an affine open represent `μ_m` by `Spec R[t]/(t^m-1)`. The root-splitting
   etaleness lemma makes this an object of the small etale site. The representable
   inverse-image and Yoneda lemmas identify its pullback with the same root functor.
   The adjunct sends each root to its restriction along the base-change projection.
3. Glue these affine comparisons using etale-cover detection of isomorphisms.
   The algebraic-structures and composition-unit lemmas identify the abelian
   adjuncts. Restriction preserves powers, giving the displayed normalization.
4. The left-exact site inverse-image tensor lemma and exact module inverse image
   preserve coefficient extension and positive powers. On pure tensors the map
   sends `a ⊗ z` to `a ⊗ v⁻¹z`, which is the generator equation below.
5. Pull back evaluation. On a local basis and its dual the comparison preserves
   evaluation and is invertible. This determines every negative comparison.
6. Concatenation and contraction on signed basis tensors give the product maps.
   Changes of basis multiply degree `a` by `u^a`, so the maps glue and satisfy
   associativity, symmetry, units, evaluation, identities, and composition.
7. Exact inverse image is its own left derived functor. The ringed-topos derived
   tensor comparison, computed on K-flat flat-term resolutions, gives the natural
   unbounded derived comparison; additive inverse image preserves shift signs.
   The derived comparison is the composite of these canonical maps, so its tensor
   and composition compatibilities follow termwise from those of steps 3--6.
8. For `m' = q m`, choose a local primitive `m'`-root `ζ`. Its power `ζ^q`
   trivializes `μ_m`. The power map is reduction in these bases and induces the
   identity on `A` after scalar extension. Tensor powers and inverse duals give
   all exponent-change comparisons. Power maps commute with pullback and compose.
-/
theorem etaleFiniteTwistPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) :
    ∃ (r : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) →
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
          T'.rootsOfUnitySheaf m))
      (c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) → IsUnit (m : Γ(T', ⊤)) → ∀ a : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
          finiteEtaleTateSheaf A m T' hA a)
      (p : ∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) → ∀ a b : ℤ,
        finiteEtaleTateSheaf A m T hA a ⊗ finiteEtaleTateSheaf A m T hA b ≅
          finiteEtaleTateSheaf A m T hA (a + b)),
    (∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) →
      ∃ U : Cover.{u} etalePrecoverage T, ∀ (i : U.I₀) (a : ℤ),
        Nonempty ((finiteEtaleTateSheaf A m T hA a).over (U.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (U.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))),
      (Etale.upperStar AddCommGrpCat.{u + 1} v).map (kernel.ι (m • 𝟙 T.gmSheaf)) ≫
          upperStarGmSheafToGmSheaf v =
        (r v hT).hom ≫ kernel.ι (m • 𝟙 T'.gmSheaf)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (W : T.Etaleᵒᵖ) (a : A)
        (z : (T.rootsOfUnitySheaf m).obj.obj W),
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
        (c v hT hT' 1).hom).hom.app W (finiteEtaleTateOneGenerator A m T hA W a z) =
      finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (r v hT).hom).hom.app W z)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))),
      c v hT hT' 0 = (upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      c v hT hT' (.ofNat (n + 2)) =
        asIso (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1))) (finiteEtaleTateLine T m A hA)) ≪≫
          tensorIso (c v hT hT' (.ofNat (n + 1))) (c v hT hT' 1)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map
          ((ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T hA 0)) ≫ (c v hT hT' 0).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))
          (finiteEtaleTateSheaf A m T hA (.negSucc n)) ≫
          tensorHom (c v hT hT' (.ofNat (n + 1))).hom (c v hT hT' (.negSucc n)).hom ≫
          (ihom.ev (finiteEtaleTateSheaf A m T' hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T' hA 0)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      c (𝟙 T) hT hT a = (Etale.upperStarId (ModuleCat.{u + 1} A) T).app
        (finiteEtaleTateSheaf A m T hA a)) ∧
    (∀ {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
        (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
        (hT'' : IsUnit (m : Γ(T'', ⊤))) (a : ℤ),
      c (w ≫ v) hT hT'' a =
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app
          (finiteEtaleTateSheaf A m T hA a) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
          c w hT' hT'' a) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT 0 a = λ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (zero_add a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT a 0 = ρ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (add_zero a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      p T hT (.ofNat (n + 1)) 1 = Iso.refl _) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b d : ℤ),
      (p T hT a b).hom ▷ finiteEtaleTateSheaf A m T hA d ≫ (p T hT (a + b) d).hom =
        (α_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)
          (finiteEtaleTateSheaf A m T hA d)).hom ≫
        finiteEtaleTateSheaf A m T hA a ◁ (p T hT b d).hom ≫
          (p T hT a (b + d)).hom ≫
            eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_assoc a b d).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b : ℤ),
      (β_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)).hom ≫
          (p T hT b a).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_comm b a)) =
        (p T hT a b).hom) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      (p T hT (.ofNat (n + 1)) (.negSucc n)).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
            (add_neg_cancel (Int.ofNat (n + 1)))) =
        (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
          (finiteEtaleTateSheaf A m T hA 0)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map (p T hT a b).hom ≫
          (c v hT hT' (a + b)).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b) ≫
        tensorHom (c v hT hT' a).hom (c v hT hT' b).hom ≫ (p T' hT' a b).hom) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      ∃ d : ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
          ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ⋙
          shiftFunctor _ b) ⋙ (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ≅
        (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ⋙
          Etale.derivedTensorRight (ModuleCat.{u + 1} A) T'
            ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T' hA a)) ⋙
              shiftFunctor _ b),
        ∀ K : Etale.DerivedCategoryModule A T,
          d.app K =
            ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.commShiftIso b).app
              (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a))) ≪≫
            (shiftFunctor _ b).mapIso
              (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v K
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ≪≫
              ((Etale.derivedTensor (ModuleCat.{u + 1} A) T').obj
                ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K)).mapIso
                ((Etale.singleFunctorCompLeftDerivedUpperStarIso
                  (ModuleCat.{u + 1} A) v).app (finiteEtaleTateSheaf A m T hA a) ≪≫
                (DerivedCategory.singleFunctor _ 0).mapIso (c v hT hT' a)))) ∧
    (∀ (m' : ℕ), 0 < m' → ∀ (hdiv : m ∣ m')
        (T : Scheme.{u}),
      IsUnit (m' : Γ(T, ⊤)) →
      ∃ (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
        (t : ∀ a : ℤ, finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) a ≅
          finiteEtaleTateSheaf A m T hA a),
      q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf) ∧
      (∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj W),
        (t 1).hom.hom.app W (finiteEtaleTateOneGenerator A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) W a z) =
          finiteEtaleTateOneGenerator A m T hA W a (q.hom.app W z)) ∧
      t 0 = Iso.refl _ ∧
      (∀ n : ℕ, t (.ofNat (n + 2)) =
        tensorIso (t (.ofNat (n + 1))) (t 1)) ∧
      (∀ n : ℕ,
        tensorHom (t (.ofNat (n + 1))).hom (t (.negSucc n)).hom ≫
            (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
              (finiteEtaleTateSheaf A m T hA 0) =
          (ihom.ev (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv))
            (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) 0))) := by
  rcases finiteEtaleTwistSignedCoherence A m hm hA with
    ⟨c, p, hgen, hzero, hpos, hneg, hid, hcomp, hleft, hright, hsucc, hassoc,
      hsymm, hev, htensor⟩
  refine ⟨fun v hT ↦ finiteTwistRootsIso m hm v hT, c, p,
    finiteEtaleTwistCommonLocalBases A m hm hA,
    fun v hT ↦ finiteTwistRootsIso_normalization m hm v hT,
    hgen, hzero, hpos, hneg, hid, hcomp, hleft, hright, hsucc, hassoc, hsymm, hev,
    htensor, ?_, ?_⟩
  · intro T T' v hT hT' a b
    exact finiteTwistDerivedComparison A v _ _ (c v hT hT' a) b
  · intro m' hm' hdiv T hT
    let hA' : (m' : A) = 0 := (CharP.cast_eq_zero_iff A (ringChar A) m').mpr
      (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)
    let q := finiteTwistRootPower m m' hdiv T
    have hq := finiteTwistRootPower_normalization m m' hdiv T
    obtain ⟨e, he⟩ := finiteEtaleTwistExponentLine A m m' hm hm' hdiv hA hA' T hT q hq
    refine ⟨q, finiteTwistSignedIso A m m' T hA hA' e, hq, he, rfl, ?_, ?_⟩
    · intro n
      rfl
    · exact finiteTwistSignedIso_evaluation A m m' T hA hA' e

end AlgebraicGeometry.Scheme
