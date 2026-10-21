/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.IntegralTensorShriek
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.IntegralConstructibleHeart
import Sheaf.Paper.IntegralModels

/-!
# Integral inverse image and completed inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-tensor,
`det-lem-int-tensor-pullback.md` and its proof; Stacks Tags 099I and 099N(2),(5)
(blueprint: det-lem-int-tensor-pullback).

The comparison is constructed on a strict reduction tower, with the quotient
augmentation and zero shifted coordinate. Constant scalar restriction retains a
separate coefficient category. Positive exponent n+1 is indexed by n : ℕ.

## Main definitions

* `comparison`: the quotient-augmented strict tower after integral inverse image.
* `constantComparison`: the Stacks completion unit over constant integral scalars.
* `restrictionPullback`: the scalar comparison normalized on tensor generators.

## Main statement

* `preserves_and_completed`: preservation of bounded constructibility and the
  unit-compatible identification with completed inverse image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u a b
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback

section Augmentation
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The strict augmentation has zero composite with 1 minus shift.
Source: blueprint comparison paragraph; Stacks 08TC
(blueprint: det-lem-int-tensor-pullback).
Proof: compose with each product projection. Compatibility of the consecutive
legs gives gamma_n minus gamma_(n+1) t_n = 0. The differential of the zero
homotopy is zero, giving the displayed cocone-lift condition. -/
theorem augmentation_condition (P : CochainComplex A ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain P
        (∏ᶜ fun n : ℕ ↦ T.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift (fun n ↦ γ.app (op n)) ≫
          towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
            (WeilConjectures.integralOperationsTowerStep T)) = 0 := by
  sorry

/-- The strict map to the Roos complex, with quotient legs and zero homotopy.
Source: blueprint comparison paragraph; Stacks 099N(5)
(blueprint: det-lem-int-tensor-pullback). -/
def augmentation (P : CochainComplex A ℤ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    P ⟶ WeilConjectures.integralOperationsRoos T :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
            (WeilConjectures.integralOperationsTowerStep T))
    (Pi.lift (fun n ↦ γ.app (op n))) 0 (augmentation_condition P T γ)
end Augmentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing constant condensed ring on the point, for the integer scalar ring.
Source: blueprint scalar-restriction paragraph; Stacks 099I
(blueprint: det-lem-int-tensor-pullback). -/
abbrev constantRing :=
  (sfbPointConstantRing.{u}.obj
    (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).X

/-- Constant scalar coefficients are commutative.
Source: Stacks 099I (blueprint: det-lem-int-tensor-pullback).
Proof: the constant presheaf ring has pointwise commutative multiplication. Monoidal
sheafification sends that multiplication to the constant ring's multiplication and
preserves the braiding, so its commutativity identity remains valid. -/
theorem constantRing_isCommMonObj : IsCommMonObj (constantRing l E) := by
  sorry
attribute [instance] constantRing_isCommMonObj

/-- The constant scalar map sends a scalar to its constant continuous function.
It is the actual sheafification-adjunction map, in the common coefficient universe.
Source: blueprint scalar-restriction paragraph; Stacks 099I
(blueprint: det-lem-int-tensor-pullback). -/
def constantToIntegral : constantRing l E ⟶ DerivedNakayama.integerRing l E :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv _ _).symm
    { app S := AddCommGrpCat.ofHom
        { toFun := fun x ↦ ULift.up (ContinuousMap.const S.unop x.down)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

/-- The constant-function map preserves the coefficient unit and multiplication.
Source: blueprint scalar-restriction paragraph; Stacks 099I
(blueprint: det-lem-int-tensor-pullback).
Proof: constant functions preserve 1 and multiplication pointwise. The monoidal
sheafification adjunction carries these two identities to the sheaf map. -/
theorem constantToIntegral_isMonHom : IsMonHom (constantToIntegral l E) := by
  sorry
attribute [instance] constantToIntegral_isMonHom

/-- Restrict an internal continuous integral module to its constant integral scalars.
This uses the recorded restriction-of-scalars operation on module objects.
Source: blueprint scalar-restriction paragraph; Stacks 099I
(blueprint: det-lem-int-tensor-pullback). -/
abbrev restriction (X : Scheme.{u}) :
    AdicCompletion.Modules l E X ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (constantRing l E) X) :=
  Mod.comap ((upperStarFromPoint X).map (constantToIntegral l E))

/-- Constant-coefficient modules remain a distinct category from completed coefficients.
Source: blueprint scalar-restriction paragraph (blueprint: det-lem-int-tensor-pullback). -/
abbrev ConstantModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (constantRing l E) X)

/-- The strict integral reduction tower before applying inverse image.
Source: blueprint comparison paragraph (blueprint: det-lem-int-tensor-pullback). -/
def tower (Y : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (AdicCompletion.Modules l E Y) ℤ :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ (AdicCompletion.level l E Y n).obj P)
    (AdicCompletion.levelStep l E Y P)

/-- The quotient maps are a strict compatible augmentation of the reduction tower.
Source: blueprint comparison paragraph (blueprint: det-lem-int-tensor-pullback).
Proof: at each degree these maps send p to p tensor 1. Consecutive quotient maps
preserve 1; their composite with the higher quotient is the lower quotient.
Thus the two tensor-unit maps coincide, giving compatibility. -/
theorem towerUnit_compatible (Y : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj P).map (homOfLE (Nat.le_succ n)).op ≫
        AdicCompletion.levelUnit l E Y P n =
      AdicCompletion.levelUnit l E Y P (n + 1) ≫
        (tower l E Y P).map (homOfLE (Nat.le_succ n)).op := by
  sorry

/-- The strict quotient augmentation, before inverse image.
Source: blueprint comparison paragraph (blueprint: det-lem-int-tensor-pullback). -/
def towerUnit (Y : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    (Functor.const ℕᵒᵖ).obj P ⟶ tower l E Y P :=
  NatTrans.ofOpSequence (AdicCompletion.levelUnit l E Y P) (towerUnit_compatible l E Y P)

/-- Apply exact inverse image to the whole strict reduction tower.
Source: blueprint displayed target of c_K (blueprint: det-lem-int-tensor-pullback). -/
def pulledTower {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :=
  tower l E Y P ⋙
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex (.up ℤ)

/-- The canonical comparison on a K-flat representative, using the strict quotient
augmentation and zero shifted coordinate, rather than a triangulated cone lift.
Source: blueprint displayed c_K; Stacks 099N(5)
(blueprint: det-lem-int-tensor-pullback). -/
def comparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :=
  augmentation
    (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
      (.up ℤ)).obj P)
    (pulledTower l E g P)
    ((Functor.constComp ℕᵒᵖ P
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
        (.up ℤ))).inv ≫
      Functor.whiskerRight (towerUnit l E Y P)
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
          (.up ℤ)))

/-- The coefficient inclusion is linear as a map from the constant regular module
into the restricted integral regular module.
Source: blueprint scalar-restriction paragraph (blueprint: det-lem-int-tensor-pullback).
Proof: the multiplication-preservation identity for constantToIntegral says exactly
that a times b maps to the image of a acting on the image of b. Pullback preserves
this equation; the transported regular-module actions are the ring multiplications. -/
theorem constantUnit_linear (X : Scheme.{u}) :
    Mod.act (𝟙_ (ConstantModules l E X)).X ≫
        (upperStarFromPoint X).map (constantToIntegral l E) =
      condensedRingObj (constantRing l E) X ◁
          (upperStarFromPoint X).map (constantToIntegral l E) ≫
        Mod.act ((restriction l E X).obj (𝟙_ (AdicCompletion.Modules l E X))).X := by
  sorry

/-- The canonical inclusion of the constant coefficient unit into the integral unit.
Source: blueprint scalar-restriction paragraph (blueprint: det-lem-int-tensor-pullback). -/
def constantUnit (X : Scheme.{u}) :
    𝟙_ (ConstantModules l E X) ⟶
      (restriction l E X).obj (𝟙_ (AdicCompletion.Modules l E X)) :=
  Mod.homMk ((upperStarFromPoint X).map (constantToIntegral l E)) (constantUnit_linear l E X)

/-- The same finite constant quotient, now with its constant integral scalar action.
Finite continuous coefficients are constant; only the integral scalar action changes.
Source: blueprint scalar-restriction paragraph; Stacks 099N(5)
(blueprint: det-lem-int-tensor-pullback). -/
abbrev constantFinite (X : Scheme.{u}) (n : ℕ) :=
  (restriction l E X).obj (AdicCompletion.finiteModule l E X n)

/-- Derived reduction over constant integral coefficients, computed on a K-flat complex.
Source: Stacks 099N(5) (blueprint: det-lem-int-tensor-pullback). -/
abbrev constantLevel (X : Scheme.{u}) (n : ℕ) :=
  (tensorRight (constantFinite l E X n)).mapHomologicalComplex (.up ℤ)

/-- The transitions in the constant scalar reduction tower are the same quotient maps.
Source: Stacks 099N(5) (blueprint: det-lem-int-tensor-pullback). -/
def constantStep (X : Scheme.{u}) (Q : CochainComplex (ConstantModules l E X) ℤ) (n : ℕ) :
    (constantLevel l E X (n + 1)).obj Q ⟶ (constantLevel l E X n).obj Q :=
  (NatTrans.mapHomologicalComplex
    ((tensoringRight (ConstantModules l E X)).map
      ((restriction l E X).map
        ((DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n))))
    (.up ℤ)).app Q

/-- Tensoring with the actual quotient of the constant coefficient unit.
Source: Stacks 099N(5) (blueprint: det-lem-int-tensor-pullback). -/
def constantLevelUnit (X : Scheme.{u})
    (Q : CochainComplex (ConstantModules l E X) ℤ) (n : ℕ) :
    Q ⟶ (constantLevel l E X n).obj Q :=
  (NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso (ConstantModules l E X)).inv ≫
      (tensoringRight (ConstantModules l E X)).map
        (constantUnit l E X ≫ (restriction l E X).map (AdicCompletion.finiteUnit l E X n)))
    (.up ℤ)).app Q

/-- The strict constant scalar reduction tower.
Source: Stacks 099N(5) (blueprint: det-lem-int-tensor-pullback). -/
def constantTower (X : Scheme.{u}) (Q : CochainComplex (ConstantModules l E X) ℤ) :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ (constantLevel l E X n).obj Q)
    (constantStep l E X Q)

/-- Quotient augmentations commute with the constant scalar transitions.
Source: Stacks 099N(5) (blueprint: det-lem-int-tensor-pullback).
Proof: the scalar inclusion followed by consecutive quotient reductions equals its
direct reduction. Tensoring this equality with Q and applying the unitor gives
compatibility, term by term in the complex. -/
theorem constantTowerUnit_compatible (X : Scheme.{u})
    (Q : CochainComplex (ConstantModules l E X) ℤ) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj Q).map (homOfLE (Nat.le_succ n)).op ≫
        constantLevelUnit l E X Q n =
      constantLevelUnit l E X Q (n + 1) ≫
        (constantTower l E X Q).map (homOfLE (Nat.le_succ n)).op := by
  sorry

/-- The strict constant scalar quotient augmentation.
Source: Stacks 099N(5) (blueprint: det-lem-int-tensor-pullback). -/
def constantTowerUnit (X : Scheme.{u}) (Q : CochainComplex (ConstantModules l E X) ℤ) :
    (Functor.const ℕᵒᵖ).obj Q ⟶ constantTower l E X Q :=
  NatTrans.ofOpSequence (constantLevelUnit l E X Q) (constantTowerUnit_compatible l E X Q)

/-- The exact constant coefficient inverse image applied to the whole reduction tower.
Source: Stacks 099N(5) (blueprint: det-lem-int-tensor-pullback). -/
def constantPulledTower {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Q : CochainComplex (ConstantModules l E Y) ℤ) :=
  constantTower l E Y Q ⋙
    (CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)

/-- The Stacks completed inverse-image unit on a constant-coefficient K-flat model.
The target is the Roos model of Rlim of the pulled-back constant reductions.
Source: Stacks 099N(2),(5) (blueprint: det-lem-int-tensor-pullback). -/
def constantComparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Q : CochainComplex (ConstantModules l E Y) ℤ) :=
  augmentation
    (((CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)).obj Q)
    (constantPulledTower l E g Q)
    ((Functor.constComp ℕᵒᵖ Q
      ((CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ))).inv ≫
      Functor.whiskerRight (constantTowerUnit l E Y Q)
        ((CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)))

/-- Scalar restriction commutes with inverse image. The normalization fixes its
underlying map on the canonical scalar-extension generators.
Source: blueprint scalar-restriction paragraph (blueprint: det-lem-int-tensor-pullback).
Proof: naturality of alpha_g for the constant-function coefficient map makes the
coefficient square commute. Replace extension along each invertible alpha_g by
restriction along its inverse, use mapModComapIso, and compose restrictions. The
underlying map sends each constant scalar tensor generator to the same generator.
Local generation by these tensors and faithfulness prove uniqueness. -/
theorem restrictionPullback_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! e : CondensedRing.upperStar (DerivedNakayama.integerRing l E) g ⋙ restriction l E X ≅
        restriction l E Y ⋙ CondensedRing.upperStar (constantRing l E) g,
      ∀ M : AdicCompletion.Modules l E Y,
        ((upperStarFromPoint X).map (constantToIntegral l E) ▷
            (upperStar Ab.{u + 1} g).obj M.X) ≫
          Mod.extendπ (condensedPullbackHom (DerivedNakayama.integerRing l E) g)
            (((upperStar Ab.{u + 1} g).mapMod _).obj M) ≫ (e.hom.app M).hom =
          Mod.extendπ (condensedPullbackHom (constantRing l E) g)
            (((upperStar Ab.{u + 1} g).mapMod _).obj ((restriction l E Y).obj M)) := by
  sorry

/-- The canonical coefficient-restriction comparison, fixed by its underlying map.
Source: blueprint scalar-restriction paragraph (blueprint: det-lem-int-tensor-pullback). -/
def restrictionPullback {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (restrictionPullback_existsUnique l E g).exists.choose

/-- Termwise restriction and inverse image commute by the same normalized comparison.
Source: blueprint scalar-restriction paragraph (blueprint: det-lem-int-tensor-pullback). -/
def restrictionPullbackComplex {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :=
  (NatIso.mapHomologicalComplex (restrictionPullback l E g) (.up ℤ)).app P

/-- The natural completion comparison is invertible on bounded constructible inputs,
and its scalar restriction is the Stacks completed inverse image with the same unit.
All K-flat representatives are allowed; they merely compute the fixed derived objects.
Source: blueprint det-lem-int-tensor-pullback, clauses (1),(2); Stacks 099I, 099N(2),(5)
(blueprint: det-lem-int-tensor-pullback).

Proof, following the nine steps of the DAG:
1. Cartesian coefficients identify module pullback with exact inverse image. It
commutes with homology and preserves cohomological bounds and distinguished triangles.
2. Base change each finite constructible stratification and its pro-etale model
cover. Exact inverse image pulls its scalar finite presentation to the same matrix.
3. For an open immersion construct the base-change map using adjunction. Its open
restriction is identity and its closed restriction is zero. The localization triangle
of its bounded cone proves it invertible, since the opens are quasi-compact.
4. The closed-immersion unit gives the analogous comparison; its restrictions are
identity and zero. Exact closed direct image keeps the cone bounded. Combine open
and closed comparisons for a locally closed immersion.
5. Apply these comparisons to each generator a_!M of det-lem-int-tensor-shriek.
The pulled-back scalar local models and their cohomology are still constructible.
6. The class preserved by inverse image is closed under isomorphisms and all
three two-out-of-three operations on triangles, by sk-lem-int-integral-heart.
The finite-stratum generation assertion therefore proves clause (1).
7. The integral criterion sk-lem-integral-models (2) says that K and g^*K are
derived complete. Only the criterion is used, not its pullback-preservation clause.
8. The canonical tensor-pullback comparison identifies every quotient level and
transition, and the quotient augmentation, with the reduction tower of g^*K.
Thus the explicit strict-tower comparison, including its zero homotopy, is invertible.
9. Identify the integral ring with its finite constant limit. Constant-to-completed
restriction is flat and has the canonical finite reduction comparisons. Consequently
a restricted K-flat model computes the constant derived reductions. The comparisons
respect the entire pulled-back tower, quotient augmentations and both Roos coordinates.
Their Roos isomorphism is precisely the displayed scalar identification. The source
identification is restrictionPullbackComplex. This is the Stacks completed pullback,
whose unit is constantComparison, so the displayed equality retains its canonical unit.
The zero complex, empty schemes and identity morphism require no exclusions. -/
theorem preserves_and_completed
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    (K : DerivedCategory (AdicCompletion.Modules l E Y))
    (_hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Y K) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X
      (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapDerivedCategory).obj K) ∧
    ∀ (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ)
      (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Y) (.up ℤ)).kFlat P)
      (_eP : DerivedCategory.Q.obj P ≅ K),
      IsIso (DerivedCategory.Q.map (comparison l E g P)) ∧
      ∃ e : DerivedCategory.Q.obj
          (((restriction l E X).mapHomologicalComplex (.up ℤ)).obj
            (WeilConjectures.integralOperationsRoos (pulledTower l E g P))) ≅
          DerivedCategory.Q.obj (WeilConjectures.integralOperationsRoos
            (constantPulledTower l E g
              (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P))),
        DerivedCategory.Q.map
            (((restriction l E X).mapHomologicalComplex (.up ℤ)).map (comparison l E g P)) ≫
            e.hom =
          DerivedCategory.Q.map (restrictionPullbackComplex l E g P).hom ≫
            DerivedCategory.Q.map (constantComparison l E g
              (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
