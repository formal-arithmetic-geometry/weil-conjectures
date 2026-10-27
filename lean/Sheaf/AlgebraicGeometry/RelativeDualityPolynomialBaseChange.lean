/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDualityPolynomialChart
public import Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel
public import Sheaf.AlgebraicGeometry.RelativeDualizingPairBaseChange
public import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalSystem
public import Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentBaseChange
public import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.AlgebraicGeometry.RelativeDualizingPairOpenRigidity
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity
import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalClass
import Sheaf.TraceFormula.FlatPolynomialQuotientPerfect
import Sheaf.Paper.DerivedInternalHomRestrictOpen

/-! # Normalized polynomial relative-duality base change

Source: Stacks Project, duality.tex, 0E2Y, 0E2W, 0E2Z and 0E4P;
dualizing.tex, 0BZP, 0BZR, 0BZS and 0BZJ, with the ordered-volume normalization.
(blueprint: lem-sfb-relative-duality-polynomial-base-change).

## Main definitions

* `IsRelativeDualityBaseChange` tests preservation of the specified diagonal class.
* `IsPolynomialBaseChangeNormalizedChart` fixes the affine comparison on that class.
* `IsPolynomialBaseChangeTildeComparison` fixes tilde comparisons by the original counits.

## Main statements

* `relativeDualityPolynomialBaseChange_unique`, `_id`, `_comp` and `_isoNaturality`
  give intrinsic existence, uniqueness and coherence.
* `relativeDualityPolynomialBaseChange_affine`, `_model`, `_resolution`, `_restriction`
  and `_refinement` give the normalized polynomial formulas.
* `relativeDualityPolynomialBaseChange_proper` and `_homology` give the proper and
  locally free concentration identifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry

variable [∀ Z : RingedSpace.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The recorded tensor-pullback counit written on complexes.
Source: Stacks 06YJ (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangePullbackCounit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj E) ⟶
      DerivedCategory.Q.obj ((Scheme.Modules.tensorPullback f).mapHomologicalComplex
        (.up ℤ) |>.obj E) :=
  (derivedPullback f).map (DerivedCategory.quotientCompQhIso _ |>.inv.app E) ≫
    (recordedDerivedPullbackCounit f).app ((HomotopyCategory.quotient _ (.up ℤ)).obj E) ≫
    DerivedCategory.Qh.map ((Scheme.Modules.tensorPullback f).mapHomotopyCategoryFactors
      (.up ℤ) |>.hom.app E) ≫ (DerivedCategory.quotientCompQhIso _).hom.app _

/-- The K-flat scalar-extension counit on complexes, with its original normalization.
Source: Stacks 08DW (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeExtensionCounit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (E : CochainComplex (ModuleCat.{u} A) ℤ) :
    (relativeDualizingDerivedExtension φ).obj (DerivedCategory.Q.obj E) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars φ).mapHomologicalComplex
        (.up ℤ)).obj E) :=
  (relativeDualizingDerivedExtension φ).map
      ((DerivedCategory.quotientCompQhIso _).inv.app E) ≫
    (relativeDualizingExtensionCounit φ).app ((HomotopyCategory.quotient _ (.up ℤ)).obj E) ≫
    DerivedCategory.Qh.map ((ModuleCat.extendScalars φ).mapHomotopyCategoryFactors
      (.up ℤ) |>.hom.app E) ≫ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).hom.app
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj E)

/-- Tilde factors on complexes, using the shared sheaf localization universe.
Source: Stacks 06Z0 (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeTildeFactors (A : Type u) [CommRing A] :
    DerivedCategory.Q ⋙ polynomialAffineTilde A ≅
      (tilde.functor (.of A)).mapHomologicalComplex (.up ℤ) ⋙
      (DerivedCategory.Q (C := SheafOfModules.{u}
        (moduleRings (Spec (.of A)).toRingedSpace))) := by
  letI : HasDerivedCategory.{w} (Spec (.of A)).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)))
  exact Functor.mapDerivedCategoryFactors.{u, w} (tilde.functor (.of A))

/-- Tilde on degree-zero modules, with the same localization as the scheme category.
Source: Stacks 06Z0 (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeTildeSingle (A : Type u) [CommRing A] :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙ polynomialAffineTilde A ≅
      tilde.functor (.of A) ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0 := by
  letI : HasDerivedCategory.{w} (Spec (.of A)).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)))
  exact Functor.mapDerivedCategorySingleFunctor.{u, w} (tilde.functor (.of A)) 0

/-- The unique ordinary affine pullback comparison normalized by the two adjunction units.
Source: Stacks 01I9 (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
@[irreducible] def polynomialBaseChangeOrdinaryTilde {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    tilde.functor (.of A) ⋙ Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φ)) ≅ ModuleCat.extendScalars φ ⋙ tilde.functor (.of B) :=
  Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ))

/-- The affine pullback comparison is fixed on every complex by the ordinary
unit-normalized tilde comparison and the two universal derived counits.
Source: Stacks 08DW, 01I9
(blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def IsPolynomialBaseChangeTildeComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (τ : polynomialAffineTilde A ⋙ derivedPullback (Spec.map (CommRingCat.ofHom φ)) ≅
      relativeDualizingDerivedExtension φ ⋙ polynomialAffineTilde B) : Prop :=
  haveI := recordedPullbackData_additive (Spec.map (CommRingCat.ofHom φ))
  ∀ E : CochainComplex (ModuleCat.{u} A) ℤ,
    τ.hom.app (DerivedCategory.Q.obj E) ≫
        (polynomialAffineTilde B).map (polynomialBaseChangeExtensionCounit φ E) ≫
        (polynomialBaseChangeTildeFactors B).hom.app _ =
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map
          ((polynomialBaseChangeTildeFactors A).hom.app E) ≫
        polynomialBaseChangePullbackCounit (Spec.map (CommRingCat.ofHom φ))
          (((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).obj E) ≫
        DerivedCategory.Q.map
          (((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).hom.app E) ≫
            (NatIso.mapHomologicalComplex (polynomialBaseChangeOrdinaryTilde φ)
              (.up ℤ)).hom.app E ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).inv.app E)

/-- The normalized ordinary diagonal associated-sheaf map, obtained from the
actual tilde/Gamma adjunction and the pushforward/global-sections comparison.
Source: Stacks 01I7, 0E2U
(blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeDiagonalTildeMap (R B : Type u)
    [CommRing R] [CommRing B] [Algebra R B] :
    tilde ((ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).obj
      (ModuleCat.of B B)) ⟶
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := B)).toRingHom))).obj
        (SheafOfModules.unit (moduleRings (Spec (.of B)).toRingedSpace)) :=
  (tilde.adjunction (R := .of (B ⊗[R] B))).homEquiv _ _ |>.symm
    ((ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).map
        ((tilde.adjunction (R := .of B)).unit.app (ModuleCat.of B B)) ≫
      (Scheme.Modules.pushforwardSpecMapCompΓIso
        (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := B)).toRingHom)).inv.app
          (tilde (ModuleCat.of B B)))

/-- The affine diagonal in the sheaf derived category, with its normalized tilde map.
Source: Stacks 0E2U (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeDiagonalTilde (R B : Type u)
    [CommRing R] [CommRing B] [Algebra R B] :
    (polynomialAffineTilde (B ⊗[R] B)).obj (relativeDualizingModuleDiagonal R B) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := B)).toRingHom))).obj
            (SheafOfModules.unit (moduleRings (Spec (.of B)).toRingedSpace))) :=
  (polynomialAffineTilde (B ⊗[R] B)).map
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} (B ⊗[R] B)) 0).inv.app
        ((ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).obj
          (ModuleCat.of B B))) ≫
    (polynomialBaseChangeTildeSingle (B ⊗[R] B)).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map (polynomialBaseChangeDiagonalTildeMap R B)

/-- The actual diagonal square for an affine chart, by the two projection equations.
Source: Stacks 0E2U (blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: both projections are jB, since multiplication composed with either
coprojection is the identity. Apply the universal property of the fibre product. -/
theorem polynomialBaseChangeDiagonalSquare {X S : Scheme.{u}} (f : X ⟶ S)
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (jB : Spec (.of B) ⟶ X) (jR : Spec (.of R) ⟶ S)
    (h : jB ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jR) :
    jB ≫ pullback.diagonal f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := B)).toRingHom) ≫
        relativeDualizingProductChart f R B jB jR h := by
  sorry

/-- The affine diagonal augmentation uses ordinary base change and the structure-sheaf
map after the original left-derived counit. It is not a freely chosen identification.
Source: Stacks 0E2U (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeAffineDiagonal {X S : Scheme.{u}} (f : X ⟶ S)
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (jB : Spec (.of B) ⟶ X) (jR : Spec (.of R) ⟶ S)
    (h : jB ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jR) :
    (derivedPullback (relativeDualizingProductChart f R B jB jR h)).obj
        (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := B)).toRingHom))).obj
            (SheafOfModules.unit (moduleRings (Spec (.of B)).toRingedSpace))) :=
  polynomialBaseChangePullbackCounit (relativeDualizingProductChart f R B jB jR h)
      (relativeDualizingDiagonalComplex f) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback (relativeDualizingProductChart f R B jB jR h))
          (.up ℤ) 0).hom.app (relativeDualizingDiagonalModule f)) ≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map
      (Scheme.Modules.moduleBaseChangeMap (pullback.diagonal f)
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := B)).toRingHom))
          (relativeDualizingProductChart f R B jB jR h) jB
          (polynomialBaseChangeDiagonalSquare f R B jB jR h)
          (SheafOfModules.unit (moduleRings X.toRingedSpace)) ≫
        (Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := B)).toRingHom))).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit jB))

/-- First projections commute on an affine chart; this is the recorded composition map.
Source: Stacks 0E2U, 0D5S
(blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeAffineTarget {X S : Scheme.{u}} (f : X ⟶ S)
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (jB : Spec (.of B) ⟶ X) (jR : Spec (.of R) ⟶ S)
    (h : jB ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jR) :
    derivedPullback (pullback.fst f f) ⋙
        derivedPullback (relativeDualizingProductChart f R B jB jR h) ≅
      derivedPullback jB ⋙ derivedPullback
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom)) :=
  recordedDerivedPullbackComposition (relativeDualizingProductChart f R B jB jR h)
      (pullback.fst f f) ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (by
        simp only [relativeDualizingProductChart, Category.assoc, pullback.lift_fst,
          pullbackSpecIso_inv_fst_assoc]
        congr 2)) ≪≫
    (recordedDerivedPullbackComposition
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom)) jB).symm

/-- An affine identification preserves the specified graph-normalized diagonal class.
The auxiliary eta is determined by the canonical diagonal tilde map; both equations
have independently defined sides. No diagonal or first-projection isomorphism is free.
Source: Stacks 0E2U, 0E2E
(blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def IsPolynomialBaseChangeNormalizedChart {X S : Scheme.{u}} (f : X ⟶ S)
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (jB : Spec (.of B) ⟶ X) (jR : Spec (.of R) ⟶ S)
    (h : jB ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jR)
    (C : PolynomialKoszulChart R B) (κ : C.diagonalHom ≅ koszulDiagonalUnit B)
    (e : (derivedPullback jB).obj K ≅ (polynomialAffineTilde B).obj C.model)
    (τ : polynomialAffineTilde B ⋙ derivedPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom)) ≅
        relativeDualizingDerivedExtension
          (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom ⋙
          polynomialAffineTilde (B ⊗[R] B)) : Prop :=
  IsPolynomialBaseChangeTildeComparison
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom τ ∧
    ∃ η : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of (B ⊗[R] B))).toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := B)).toRingHom))).obj
            (SheafOfModules.unit (moduleRings (Spec (.of B)).toRingedSpace))) ⟶
        (polynomialAffineTilde (B ⊗[R] B)).obj C.firstPullback,
      polynomialBaseChangeDiagonalTilde R B ≫ η =
        (polynomialAffineTilde (B ⊗[R] B)).map (C.diagonalClass κ) ∧
      (derivedPullback (relativeDualizingProductChart f R B jB jR h)).map ξ ≫
          (polynomialBaseChangeAffineTarget f R B jB jR h).hom.app K ≫
          (derivedPullback (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom))).map e.hom ≫
          τ.hom.app C.model = polynomialBaseChangeAffineDiagonal f R B jB jR h ≫ η

/-- Transport a base-change pair using the fixed diagonal augmentation and pullback
composition. The equation tests the specified classes, and imposes no chart choices.
Source: Stacks 0E2Y (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def IsRelativeDualityBaseChange {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S')
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f]
    (a : S' ⟶ S) (b : X' ⟶ X) (sq : IsPullback b f' f a)
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (L : schemeDerivedCategory X')
    (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj L)
    (β : (derivedPullback b).obj K ≅ L) : Prop :=
  relativeDualizingBaseChangeClass f f' a b sq.w
      (relativeDualizingDiagonalBaseChangeMap_isIso f f' a b sq) K ξ ≫
    (derivedPullback (pullback.fst f' f')).map β.hom = η

/-- Unique class-preserving base change, with coherent identities and composition.
Source: Stacks 0E2Y, 0E2W, 0E4P
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: pull back the supplied pair by 0E2Y, using Tor independence of the diagonal.
Both it and the supplied target are coherent relative dualizing pairs. Rigidity 0E2W
therefore gives exactly one class-preserving isomorphism. The diagonal augmentation
and recorded pullback composition give the identity and composition laws on classes.
Apply uniqueness to the identity and to the composite isomorphism. The same argument
for an invertible family map gives naturality under isomorphisms of families. Empty
schemes are included because rigidity there is uniqueness between zero objects. -/
theorem relativeDualityPolynomialBaseChange_unique
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    [IsSeparated f'] [Flat f'] [LocallyOfFinitePresentation f'] [IsLocallyNoetherian S']
    (a : S' ⟶ S) (b : X' ⟶ X) (sq : IsPullback b f' f a)
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (L : schemeDerivedCategory X')
    (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj L)
    (hL : IsCoherentRelativeDualizingPair f' L η) :
    ∃! β : (derivedPullback b).obj K ≅ L,
      IsRelativeDualityBaseChange f f' a b sq K ξ L η β := by
  sorry

/-- The normalized identity law, also for the empty family.
Source: Stacks 0E2W, 0E2Y
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: the identity pullback unit preserves the class by the recorded identity
law for the diagonal augmentation. Rigidity identifies every marked comparison with it. -/
theorem relativeDualityPolynomialBaseChange_id
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (β : (derivedPullback (𝟙 X)).obj K ≅ K)
    (hβ : IsRelativeDualityBaseChange f f (𝟙 S) (𝟙 X)
      (IsPullback.id_horiz f) K ξ K ξ β) :
    β = (relativeDualizingPullbackId X).app K := by
  sorry

/-- The cocycle for arbitrary successive base changes, with the fixed pullback associator.
Source: Stacks 0E2W, 0E4P
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: the recorded composition law identifies the twice-pulled class with the
once-pulled class. The composite of the two marked comparisons preserves it.
The direct comparison is marked as well, so uniqueness gives the displayed equality. -/
theorem relativeDualityPolynomialBaseChange_comp
    {X S X' S' X'' S'' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (f'' : X'' ⟶ S'')
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    [IsSeparated f'] [Flat f'] [LocallyOfFinitePresentation f'] [IsLocallyNoetherian S']
    [IsSeparated f''] [Flat f''] [LocallyOfFinitePresentation f'']
    [IsLocallyNoetherian S'']
    (a : S' ⟶ S) (b : X' ⟶ X) (sq : IsPullback b f' f a)
    (a' : S'' ⟶ S') (b' : X'' ⟶ X') (sq' : IsPullback b' f'' f' a')
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (L : schemeDerivedCategory X')
    (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj L)
    (hL : IsCoherentRelativeDualizingPair f' L η)
    (M : schemeDerivedCategory X'')
    (ζ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f'') ⟶
      (derivedPullback (pullback.fst f'' f'')).obj M)
    (hM : IsCoherentRelativeDualizingPair f'' M ζ)
    (β : (derivedPullback b).obj K ≅ L)
    (β' : (derivedPullback b').obj L ≅ M)
    (β'' : (derivedPullback (b' ≫ b)).obj K ≅ M)
    (hβ : IsRelativeDualityBaseChange f f' a b sq K ξ L η β)
    (hβ' : IsRelativeDualityBaseChange f' f'' a' b' sq' L η M ζ β')
    (hβ'' : IsRelativeDualityBaseChange f f'' (a' ≫ a) (b' ≫ b)
      (sq'.paste_horiz sq) K ξ M ζ β'') :
    (derivedPullback b').map β.hom ≫ β'.hom =
      (recordedDerivedPullbackComposition b' b).hom.app K ≫ β''.hom := by
  sorry

/-- The canonical affine comparison exists with its all-complex counit equation.
Source: Stacks 08DW, 01I9
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: derive the unit-normalized ordinary tilde pullback comparison. Tilde is exact
and sends K-flat module complexes to K-flat sheaf complexes. Both universal counits
are therefore invertible on resolving objects. The universal property of localization
gives a unique natural comparison on the derived categories and the stated equation.
Its components on resolving objects are isomorphisms, hence so are all its components. -/
theorem exists_polynomialBaseChangeTildeComparison
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∃ τ : polynomialAffineTilde A ⋙ derivedPullback (Spec.map (CommRingCat.ofHom φ)) ≅
        relativeDualizingDerivedExtension φ ⋙ polynomialAffineTilde B,
      IsPolynomialBaseChangeTildeComparison φ τ := by
  sorry

/-- Every supplied pair has graph-normalized identifications on every polynomial chart.
This pins the formerly underlying-object chart comparison to the supplied diagonal class.
Source: Stacks 0E2U, 0E2W, 0E2X and dualizing.tex 0E2E
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: translate the supplied pair by the affine comparison. Polynomial perfection
and the chart theorem give the pseudo-coherence and relative Tor bounds of C.model.
The graph-normalized kappa supplies its diagonal class and the invertibility of
multiplication. Realize it through exact tilde and the canonical diagonal augmentation.
Rigidity gives the unique class-preserving identification with the restricted pair.
The tilde pullback comparison has the counit equation above. Substitution gives the
two displayed squares. This works for localized presentations as well, by the
localized graph resolution. Empty charts and the empty graph wedge are included. -/
theorem exists_polynomialBaseChangeNormalizedChart
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (jB : Spec (.of B) ⟶ X) (jR : Spec (.of R) ⟶ S)
    [IsOpenImmersion jB] [IsOpenImmersion jR]
    (h : jB ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jR)
    (C : PolynomialKoszulChart R B) (κ : C.diagonalHom ≅ koszulDiagonalUnit B)
    (hκ : IsKoszulDiagonalNormalization C κ) :
    ∃ (e : (derivedPullback jB).obj K ≅ (polynomialAffineTilde B).obj C.model)
      (τ : polynomialAffineTilde B ⋙ derivedPullback
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom)) ≅
        relativeDualizingDerivedExtension
          (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom ⋙
          polynomialAffineTilde (B ⊗[R] B)),
      IsPolynomialBaseChangeNormalizedChart f K ξ R B jB jR h C κ e τ := by
  sorry

/-- The canonical comparison between the two pullbacks around a commuting chart square.
Source: Stacks 0D5S (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeChartSquare {X X' : Scheme.{u}} (b : X' ⟶ X)
    {B D : Type u} [CommRing B] [CommRing D] (jB : Spec (.of B) ⟶ X)
    (jD : Spec (.of D) ⟶ X') (g : B →+* D)
    (h : jD ≫ b = Spec.map (CommRingCat.ofHom g) ≫ jB) :
    derivedPullback b ⋙ derivedPullback jD ≅
      derivedPullback jB ⋙ derivedPullback (Spec.map (CommRingCat.ofHom g)) :=
  recordedDerivedPullbackComposition jD b ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h) ≪≫
    (recordedDerivedPullbackComposition (Spec.map (CommRingCat.ofHom g)) jB).symm

/-- Under normalized affine chart comparisons, the intrinsic marked base-change map
is precisely the counit-defined derived-Hom scalar exchange with its natural B'-action.
The chart rings are presented as pushouts, so this includes B'=B tensor_R R' and
P'=P tensor_R R'; no flatness of the map R to R' is imposed.
Source: Stacks 0E2Y, dualizing.tex 0BZP, 0BZR, 0BZS, 0E2E and 0BZJ
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof, following the node:
1. On the affine charts R to B is flat of finite presentation and R is Noetherian.
Polynomial quotient perfection gives a bounded finite-projective P-resolution F of B.
2. P' and B are Tor independent over P: tensor a free R-resolution of R' with P
and then B, which is R-flat. Perfect coinduction exchange is therefore invertible.
3. Its adjunct is extended evaluation at one. On F the underlying map is exactly
(h tensor r')(z tensor s')=r's'(h(z) tensor 1); the shift by n changes no coefficient.
4. The ordered graph Koszul trace commutes with this counit mate. Thus the exchange
sends the derived extension of the normalized diagonal class to the new class.
Equivalently, the scalar-natural polynomial-diagonal adjunction sends the new class
to the identity, since the old class was sent to the identity.
5. The two class-normalized affine identifications transport the intrinsic beta to
this exchange. Rigidity equates the two marked isomorphisms, giving the equation.
6. Localization applies the same fraction maps to evaluation. An extra coordinate
uses the two-term resolution on t-u; its trace sends dual(t-u) tensor d(t-u) to 1.
Ordered iterates retain the exterior and cohomological tensor signs. Both comparisons
preserve the same classes, so their restrictions, refinements and cocycles agree.
No affine-intersection descent or local-complete-intersection assumption is used. -/
theorem relativeDualityPolynomialBaseChange_affine
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    [IsSeparated f'] [Flat f'] [LocallyOfFinitePresentation f'] [IsLocallyNoetherian S']
    (a : S' ⟶ S) (b : X' ⟶ X) (sq : IsPullback b f' f a)
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (L : schemeDerivedCategory X')
    (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj L)
    (hL : IsCoherentRelativeDualizingPair f' L η)
    (β : (derivedPullback b).obj K ≅ L)
    (hβ : IsRelativeDualityBaseChange f f' a b sq K ξ L η β)
    (R B T D : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [CommRing T] [CommRing D] [Algebra T D]
    (jB : Spec (.of B) ⟶ X) (jR : Spec (.of R) ⟶ S)
    (jD : Spec (.of D) ⟶ X') (jT : Spec (.of T) ⟶ S')
    [IsOpenImmersion jB] [IsOpenImmersion jR]
    [IsOpenImmersion jD] [IsOpenImmersion jT]
    (h : jB ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ jR)
    (h' : jD ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap T D)) ≫ jT)
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart T D)
    (κ : C.diagonalHom ≅ koszulDiagonalUnit B)
    (κ' : E.diagonalHom ≅ koszulDiagonalUnit D)
    (hκ : IsKoszulDiagonalNormalization C κ)
    (hκ' : IsKoszulDiagonalNormalization E κ')
    (e : (derivedPullback jB).obj K ≅ (polynomialAffineTilde B).obj C.model)
    (e' : (derivedPullback jD).obj L ≅ (polynomialAffineTilde D).obj E.model)
    (τB : polynomialAffineTilde B ⋙ derivedPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom)) ≅
      relativeDualizingDerivedExtension
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom ⋙
        polynomialAffineTilde (B ⊗[R] B))
    (τD : polynomialAffineTilde D ⋙ derivedPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : D →ₐ[T] D ⊗[T] D).toRingHom)) ≅
      relativeDualizingDerivedExtension
        (Algebra.TensorProduct.includeLeft : D →ₐ[T] D ⊗[T] D).toRingHom ⋙
        polynomialAffineTilde (D ⊗[T] D))
    (he : IsPolynomialBaseChangeNormalizedChart f K ξ R B jB jR h C κ e τB)
    (he' : IsPolynomialBaseChangeNormalizedChart f' L η T D jD jT h' E κ' e' τD)
    (F : KoszulDiagonalChartChange C E)
    (hF : F.IsAdmissible)
    (hjR : jT ≫ a = Spec.map (CommRingCat.ofHom F.base) ≫ jR)
    (hjB : jD ≫ b = Spec.map (CommRingCat.ofHom F.ring) ≫ jB)
    (c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model)
    (hc : F.IsComparison c)
    (τ : polynomialAffineTilde B ⋙ derivedPullback (Spec.map (CommRingCat.ofHom F.ring)) ≅
      relativeDualizingDerivedExtension F.ring ⋙ polynomialAffineTilde D)
    (hτ : IsPolynomialBaseChangeTildeComparison F.ring τ) :
    (derivedPullback jD).map β.hom ≫ e'.hom =
      (polynomialBaseChangeChartSquare b jB jD F.ring hjB).hom.app K ≫
        (derivedPullback (Spec.map (CommRingCat.ofHom F.ring))).map e.hom ≫
        τ.hom.app C.model ≫ (polynomialAffineTilde D).map c.hom := by
  sorry

/-- Every base change or simultaneous open localization of polynomial models has
its specified evaluation-counit comparison, not merely an underlying-object isomorphism.
Source: Stacks 0BZP, 0BZR, 0BZS and 0E2E
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: a bounded finite-projective polynomial resolution exists because B/R is flat
of finite presentation. It remains a resolution under base change by R-flatness;
localization is exact. Thus the counit-mate perfect exchange is invertible. The top
coefficient is finite free on the ordered differential volume, so its canonical
scalar-extension map is invertible. The resulting map satisfies IsComparison by
its defining adjunction equation. This includes zero rings and zero variables. -/
theorem relativeDualityPolynomialBaseChange_model
    (R B T D : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [CommRing T] [CommRing D] [Algebra T D]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    [IsNoetherianRing T] [Module.Flat T D] [Algebra.FinitePresentation T D]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart T D)
    (F : KoszulDiagonalChartChange C E) (hF : F.IsAdmissible) :
    ∃ c : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model,
      F.IsComparison c := by
  sorry

/-- The counit comparisons commute with open restrictions and successive scalar changes.
Each of F, G and H can be a base change or a simultaneous localization. Thus the
square obtained by restricting a base-change comparison is the same comparison on
the smaller charts; the associator is fixed by the scalar-extension adjunctions.
Source: Stacks 0BZR, 0BZS, 0E2E
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: take adjuncts under scalar extension and coinduction. Both composites become
the same evaluation counit, by associativity of tensor products. The ordered-volume
maps compose because both send each ordered wedge to the wedge of its images.
Adjunction is injective on Hom sets, so the displayed maps agree. This applies to
principal localizations; arbitrary open restrictions follow on their affine cover. -/
theorem relativeDualityPolynomialBaseChange_restriction
    (R B T D V H : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [CommRing T] [CommRing D] [Algebra T D]
    [CommRing V] [CommRing H] [Algebra V H]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    [IsNoetherianRing T] [Module.Flat T D] [Algebra.FinitePresentation T D]
    [IsNoetherianRing V] [Module.Flat V H] [Algebra.FinitePresentation V H]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart T D)
    (J : PolynomialKoszulChart V H)
    (F : KoszulDiagonalChartChange C E) (G : KoszulDiagonalChartChange E J)
    (I : KoszulDiagonalChartChange C J)
    (hF : F.IsAdmissible) (hG : G.IsAdmissible) (hI : I.IsAdmissible)
    (hbase : I.base = G.base.comp F.base)
    (hring : I.ring = G.ring.comp F.ring)
    (hambient : I.ambient = G.ambient.comp F.ambient)
    (cF : (relativeDualizingDerivedExtension F.ring).obj C.model ≅ E.model)
    (cG : (relativeDualizingDerivedExtension G.ring).obj E.model ≅ J.model)
    (cI : (relativeDualizingDerivedExtension I.ring).obj C.model ≅ J.model)
    (hcF : F.IsComparison cF) (hcG : G.IsComparison cG) (hcI : I.IsComparison cI) :
    (relativeDualizingDerivedExtension G.ring).map cF.hom ≫ cG.hom =
      (koszulDiagonalExtensionComp F.ring G.ring I.ring hring).hom.app C.model ≫
        cI.hom := by
  sorry

/-- Base change and open localization commute with normalized ordered refinements.
The contraction predicates impose dual(t-u) tensor d(t-u) to 1 through the actual
boundary map. New coordinates are last; ordered iterates carry the Koszul signs.
Source: Stacks 0BZJ, its top-differential footnote, and 0E2E
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: evaluate the counit mates on a finite-projective resolution. Localization
and scalar extension send h evaluated on z to the localized or extended h(z).
For one extra equation the graph resolution has differential t-u, and its extended
trace evaluates the dual relation against d(t-u) to 1. The two counit-pasting routes
therefore agree. Tensoring ordered graph blocks preserves both exterior and total
cohomological signs. Induct on the number of blocks; common refinements compare
any two presentations, and rigidity gives independence of the refinement lifts. -/
theorem relativeDualityPolynomialBaseChange_refinement
    (R B T D : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [CommRing T] [CommRing D] [Algebra T D]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    [IsNoetherianRing T] [Module.Flat T D] [Algebra.FinitePresentation T D]
    (C E : PolynomialKoszulChart R B) (C' E' : PolynomialKoszulChart T D)
    (F : KoszulDiagonalRefinement C E) (G : KoszulDiagonalRefinement C' E')
    (b : B →+* D) (H : KoszulDiagonalChartChange C C')
    (J : KoszulDiagonalChartChange E E') (hH : H.ring = b) (hJ : J.ring = b)
    (hbase : H.base = J.base)
    (hp : H.ambient.comp F.evaluation.toRingHom =
      G.evaluation.toRingHom.comp J.ambient)
    (e : (ModuleCat.derivedCoinduction F.evaluation.toRingHom).obj E.coefficient ≅
      C.coefficient)
    (e' : (ModuleCat.derivedCoinduction G.evaluation.toRingHom).obj E'.coefficient ≅
      C'.coefficient)
    (cH : (relativeDualizingDerivedExtension b).obj C.model ≅ C'.model)
    (cJ : (relativeDualizingDerivedExtension b).obj E.model ≅ E'.model)
    (hHa : H.IsAdmissible) (hJa : J.IsAdmissible)
    (he : F.IsContraction e) (he' : G.IsContraction e')
    (hcH : H.IsComparison (eqToIso (congrArg
      (fun t : B →+* D ↦ (relativeDualizingDerivedExtension t).obj C.model) hH) ≪≫ cH))
    (hcJ : J.IsComparison (eqToIso (congrArg
      (fun t : B →+* D ↦ (relativeDualizingDerivedExtension t).obj E.model) hJ) ≪≫ cJ)) :
    (relativeDualizingDerivedExtension b).map (F.modelMap e) ≫ cH.hom =
      cJ.hom ≫ G.modelMap e' := by
  sorry

/-- The affine comparison on every bounded finite-projective resolution. The coefficient
is the single complex in degree -n, so this is exactly Hom(F,Omega^n)[n], with no
independent shift sign. Both Hom identifications are fixed by K-injective comparison.
Source: Stacks dualizing.tex, 0BZP, 0BZR and 0BZS
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: Tor independence makes the extended augmentation a resolution. The coefficient
line is finite free, so its extension computes derived extension. The coinduction
counit is evaluation at one and the scalar mate is balanced tensor associativity.
On a finite-projective source resolve Hom using the shared K-injective comparison.
Extending a functional gives (h tensor r')(z tensor s')=r's'(h(z) tensor 1).
This calculation in every homogeneous degree is CoinductionHomScalarFormula.
The same evaluation identifies the localized chain map with the specified derived
coinduction comparison, giving the final equation. It is valid for every resolution,
and maps of augmented resolutions commute with precomposition. -/
theorem relativeDualityPolynomialBaseChange_resolution
    (R B T D : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [CommRing T] [CommRing D] [Algebra T D]
    [IsNoetherianRing R] [Module.Flat R B] [Algebra.FinitePresentation R B]
    [IsNoetherianRing T] [Module.Flat T D] [Algebra.FinitePresentation T D]
    (C : PolynomialKoszulChart R B) (E : PolynomialKoszulChart T D)
    (G : KoszulDiagonalChartChange C E) (hG : G.IsAdmissible)
    (c : (relativeDualizingDerivedExtension G.ring).obj C.model ≅ E.model)
    (hc : G.IsComparison c)
    (F : CochainComplex (ModuleCat.{u} C.P) ℤ)
    (s : F ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars C.quotient.toRingHom).obj (ModuleCat.of B B)))
    (hs : QuasiIso s) (hbounded : ∃ i j : ℤ, F.IsStrictlyGE i ∧ F.IsStrictlyLE j)
    (hprojective : ∀ i : ℤ, Module.Finite C.P (F.X i) ∧ Module.Projective C.P (F.X i)) :
    ∃ (sT : ((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj F ⟶
        (CochainComplex.singleFunctor _ 0).obj
          ((ModuleCat.restrictScalars E.quotient.toRingHom).obj (ModuleCat.of D D)))
      (χ : ((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.moduleHomComplex F
            ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top)) ⟶
        CochainComplex.moduleHomComplex
          (((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj F)
          (((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top)))
      (eP : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex F
          ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top)) ≅
        (ModuleCat.restrictScalars C.quotient.toRingHom).mapDerivedCategory.obj C.model)
      (eP' : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex
          (((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj F)
          (((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top))) ≅
        (ModuleCat.restrictScalars E.quotient.toRingHom).mapDerivedCategory.obj
          ((ModuleCat.derivedCoinduction E.quotient.toRingHom).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj
                ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top)))))
      (v : DerivedCategory.Q.obj
        (((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top)) ≅ E.coefficient),
      QuasiIso sT ∧
      (∀ (t : E.P) (x : F.X 0),
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((ModuleCat.restrictScalars E.quotient.toRingHom).obj (ModuleCat.of D D))).hom
            (sT.f 0 (t ⊗ₜ[C.P,G.ambient] x)) =
          E.quotient t * G.ring ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
            ((ModuleCat.restrictScalars C.quotient.toRingHom).obj
              (ModuleCat.of B B))).hom (s.f 0 x))) ∧
      ModuleCat.CoinductionHomScalarFormula G.ambient F
        ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top) χ ∧
      ModuleCat.CoinductionHomModel C.quotient.toRingHom F
        ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top) s eP ∧
      ModuleCat.CoinductionHomModel E.quotient.toRingHom
        (((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj F)
        (((ModuleCat.extendScalars G.ambient).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top)) sT eP' ∧
      polynomialBaseChangeExtensionCounit G.ambient
          ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top) ≫ v.hom =
        G.coefficientMap ∧
      (relativeDualizingDerivedExtension G.ambient).map eP.hom ≫
          koszulDiagonalScalarMate C.quotient.toRingHom G.ambient G.ring
            E.quotient.toRingHom G.quotient_comm C.model ≫
          (ModuleCat.restrictScalars E.quotient.toRingHom).mapDerivedCategory.map c.hom =
        polynomialBaseChangeExtensionCounit G.ambient
            (CochainComplex.moduleHomComplex F
              ((CochainComplex.singleFunctor _ (-(C.n : ℤ))).obj C.top)) ≫
          DerivedCategory.Q.map χ ≫ eP'.hom ≫
          (ModuleCat.restrictScalars E.quotient.toRingHom).mapDerivedCategory.map
            ((ModuleCat.derivedCoinduction E.quotient.toRingHom).map v.hom) := by
  sorry

/-- Naturality under isomorphisms of S-families, with the independently specified
class-preserving comparisons on both families and on their base changes.
Source: Stacks 0E2W, 0E4P
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: an isomorphism of families transports the diagonal, multiplication and first
projection. The two routes preserve the same pulled class. Recorded pullback
associativity identifies their sources, and rigidity equates the two routes. -/
theorem relativeDualityPolynomialBaseChange_isoNaturality
    {X Y S X' Y' S' : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    [IsSeparated g] [Flat g] [LocallyOfFinitePresentation g]
    [IsSeparated f'] [Flat f'] [LocallyOfFinitePresentation f'] [IsLocallyNoetherian S']
    [IsSeparated g'] [Flat g'] [LocallyOfFinitePresentation g']
    (a : S' ⟶ S) (b : X' ⟶ X) (c : Y' ⟶ Y)
    (sf : IsPullback b f' f a) (sg : IsPullback c g' g a)
    (e : Y ≅ X) (e' : Y' ≅ X')
    (se : IsPullback e.hom g f (𝟙 S)) (se' : IsPullback e'.hom g' f' (𝟙 S'))
    (h : e'.hom ≫ b = c ≫ e.hom)
    (K : schemeDerivedCategory X) (M : schemeDerivedCategory Y)
    (K' : schemeDerivedCategory X') (M' : schemeDerivedCategory Y')
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (ζ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex g) ⟶
      (derivedPullback (pullback.fst g g)).obj M)
    (ξ' : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj K')
    (ζ' : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex g') ⟶
      (derivedPullback (pullback.fst g' g')).obj M')
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (hM : IsCoherentRelativeDualizingPair g M ζ)
    (hK' : IsCoherentRelativeDualizingPair f' K' ξ')
    (hM' : IsCoherentRelativeDualizingPair g' M' ζ')
    (β : (derivedPullback b).obj K ≅ K') (γ : (derivedPullback c).obj M ≅ M')
    (α : (derivedPullback e.hom).obj K ≅ M)
    (α' : (derivedPullback e'.hom).obj K' ≅ M')
    (hβ : IsRelativeDualityBaseChange f f' a b sf K ξ K' ξ' β)
    (hγ : IsRelativeDualityBaseChange g g' a c sg M ζ M' ζ' γ)
    (hα : IsRelativeDualityBaseChange f g (𝟙 S) e.hom se K ξ M ζ α)
    (hα' : IsRelativeDualityBaseChange f' g' (𝟙 S') e'.hom se' K' ξ' M' ζ' α') :
    (derivedPullback e'.hom).map β.hom ≫ α'.hom =
      (recordedDerivedPullbackComposition e'.hom b ≪≫
        eqToIso (congrArg (fun k ↦ derivedPullback k) h) ≪≫
        (recordedDerivedPullbackComposition c e.hom).symm).hom.app K ≫
          (derivedPullback c).map α.hom ≫ γ.hom := by
  sorry

/-- Under the intrinsic proper-duality pair identifications the two comparisons agree.
The two right adjunctions are on the unbounded categories with quasi-coherent cohomology.
Source: Stacks 0E2Z, 0E4P and the intrinsic polynomial-model identification
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: the proper-flat polynomial-model theorem supplies the coherent pairs on the
values of the right adjoints at the structure sheaves. Transport the supplied pairs
along their marked identifications. The transported beta is a marked comparison.
Rigidity gives the unique proper-pair comparison and identifies it with this transport.
Its affine formula is the same counit mate already computed, so no unit or sign enters. -/
theorem relativeDualityPolynomialBaseChange_proper
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    [IsProper f'] [Flat f'] [LocallyOfFinitePresentation f'] [IsLocallyNoetherian S']
    (a : S' ⟶ S) (b : X' ⟶ X) (sq : IsPullback b f' f a)
    (hO : schemeDerivedQCohProperty S (𝟙_ (schemeDerivedCategory S)))
    (hO' : schemeDerivedQCohProperty S' (𝟙_ (schemeDerivedCategory S')))
    (hpres : ∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty S ((schemeDerivedDirectImage f).obj E))
    (hpres' : ∀ E : schemeDerivedCategory X', schemeDerivedQCohProperty X' E →
      schemeDerivedQCohProperty S' ((schemeDerivedDirectImage f').obj E))
    (fshriek : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (fshriek' : schemeDerivedQCohCategory S' ⥤ schemeDerivedQCohCategory X')
    (adj : ((schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ hpres E.obj E.property)) ⊣ fshriek)
    (adj' : ((schemeDerivedQCohProperty S').lift
      ((schemeDerivedQCohProperty X').ι ⋙ schemeDerivedDirectImage f')
      (fun E ↦ hpres' E.obj E.property)) ⊣ fshriek')
    (P : schemeDerivedQCohCategory X) (P' : schemeDerivedQCohCategory X')
    (hP : P = fshriek.obj ⟨𝟙_ (schemeDerivedCategory S), hO⟩)
    (hP' : P' = fshriek'.obj ⟨𝟙_ (schemeDerivedCategory S'), hO'⟩)
    (K : schemeDerivedCategory X) (L : schemeDerivedCategory X')
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj L)
    (ζ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj P.obj)
    (ζ' : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj P'.obj)
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (hL : IsCoherentRelativeDualizingPair f' L η)
    (hζ : IsCoherentRelativeDualizingPair f P.obj ζ)
    (hζ' : IsCoherentRelativeDualizingPair f' P'.obj ζ')
    (α : K ≅ P.obj) (α' : L ≅ P'.obj)
    (hα : ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = ζ)
    (hα' : η ≫ (derivedPullback (pullback.fst f' f')).map α'.hom = ζ')
    (β : (derivedPullback b).obj K ≅ L)
    (hβ : IsRelativeDualityBaseChange f f' a b sq K ξ L η β) :
    ∃! γ : (derivedPullback b).obj P.obj ≅ P'.obj,
      IsRelativeDualityBaseChange f f' a b sq P.obj ζ P'.obj ζ' γ ∧
      (derivedPullback b).map α.hom ≫ γ.hom = β.hom ≫ α'.hom := by
  sorry

/-- The canonical comparison to ordinary pullback of a single module. Its counit is
computed on the actual single complex; no concentrated-object choice occurs.
Source: Stacks 08DW (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeSingleMap {X X' : Scheme.{u}} (b : X' ⟶ X)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) :
    (derivedPullback b).obj ((DerivedCategory.singleFunctor _ i).obj M) ⟶
      (DerivedCategory.singleFunctor _ i).obj ((Scheme.Modules.tensorPullback b).obj M) :=
  (derivedPullback b).map ((DerivedCategory.singleFunctorIsoCompQ _ i).hom.app M) ≫
    polynomialBaseChangePullbackCounit b ((CochainComplex.singleFunctor _ i).obj M) ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback b) (.up ℤ) i).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ _ i).inv.app _

/-- Locally free modules compute derived pullback in their single degree.
Source: Stacks 08DW, the degree-zero flat calculation
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: trivialize M by a finite free module near each point. Its single complex is
K-flat and the recorded derived counit is an isomorphism. Ordinary pullback preserves
the local trivialization. Thus this canonical map is an isomorphism locally, hence
globally by the vanishing of the cohomology of its cone. No condition on b is needed. -/
@[instance] theorem polynomialBaseChangeSingleMap_isIso {X X' : Scheme.{u}}
    (b : X' ⟶ X) (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [M.IsFiniteLocallyFree] (i : ℤ) : IsIso (polynomialBaseChangeSingleMap b M i) := by
  sorry

/-- The canonical H^i identification of derived pullback of a single locally free module.
Source: Stacks 08DW (blueprint: lem-sfb-relative-duality-polynomial-base-change). -/
def polynomialBaseChangeSingleHomology {X X' : Scheme.{u}} (b : X' ⟶ X)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [M.IsFiniteLocallyFree]
    (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj
        ((derivedPullback b).obj ((DerivedCategory.singleFunctor _ i).obj M)) ≅
      (Scheme.Modules.tensorPullback b).obj M :=
  (DerivedCategory.homologyFunctor _ i).mapIso (asIso (polynomialBaseChangeSingleMap b M i)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app _

/-- The ordinary dualizing-module map is H^{-d} of the intrinsic pair comparison.
The two normalization equations pin concentration isomorphisms to the stated cohomology
modules, so changing a trivialization cannot alter the result.
Source: Stacks 0E4P and functoriality of cohomology
(blueprint: lem-sfb-relative-duality-polynomial-base-change).
Proof: local finite freeness makes the displayed single-pullback map invertible.
Take H^{-d} of the proper-pair comparison equality. The single-homology unit identifies
the output with omega and the source with ordinary pullback of omega. Both sides act
on local transition matrices by the same ring map, so the identification is canonical.
Functoriality gives exactly the displayed commuting square and its isomorphism. -/
theorem relativeDualityPolynomialBaseChange_homology
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    [IsProper f'] [Flat f'] [LocallyOfFinitePresentation f'] [IsLocallyNoetherian S']
    (a : S' ⟶ S) (b : X' ⟶ X) (sq : IsPullback b f' f a)
    (K : schemeDerivedCategory X) (L : schemeDerivedCategory X')
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f') ⟶
      (derivedPullback (pullback.fst f' f')).obj L)
    (hK : IsCoherentRelativeDualizingPair f K ξ)
    (hL : IsCoherentRelativeDualizingPair f' L η)
    (β : (derivedPullback b).obj K ≅ L)
    (hβ : IsRelativeDualityBaseChange f f' a b sq K ξ L η β)
    (d : ℤ)
    (ω : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (ω' : SheafOfModules.{u} (moduleRings X'.toRingedSpace))
    [ω.IsFiniteLocallyFree] [ω'.IsFiniteLocallyFree]
    (e : K ≅ (DerivedCategory.singleFunctor _ (-d)).obj ω)
    (e' : L ≅ (DerivedCategory.singleFunctor _ (-d)).obj ω')
    (q : (DerivedCategory.homologyFunctor _ (-d)).obj K ≅ ω)
    (q' : (DerivedCategory.homologyFunctor _ (-d)).obj L ≅ ω')
    (hq : q = (DerivedCategory.homologyFunctor _ (-d)).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-d)).app ω)
    (hq' : q' = (DerivedCategory.homologyFunctor _ (-d)).mapIso e' ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-d)).app ω') :
    ∃! γ : (Scheme.Modules.tensorPullback b).obj ω ≅ ω',
      (DerivedCategory.homologyFunctor _ (-d)).map
          ((derivedPullback b).map e.hom) ≫
          (polynomialBaseChangeSingleHomology b ω (-d)).hom ≫ γ.hom =
        (DerivedCategory.homologyFunctor _ (-d)).map β.hom ≫ q'.hom := by
  sorry

end AlgebraicGeometry
