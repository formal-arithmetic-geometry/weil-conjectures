/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

-- The high-priority successor-universe sheafification instance gets stuck on coefficient-universe goals.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-! # Supplied coherent relative dualizing pairs

Source: Stacks Project, duality.tex, Definition 0E2T, with W = X ×_S X.
(blueprint: def-trf-coherent-relative-dualizing-pair).
The diagonal algebra is the ordinary direct image in degree zero. Its multiplication
is fixed on pure tensors, and its derived multiplication is induced by the canonical
lax monoidal localization. No relative dualizing complex is chosen or assumed to exist.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

noncomputable section
namespace AlgebraicGeometry

/-- The diagonal algebra as an ordinary module sheaf.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingDiagonalModule {X S : Scheme.{u}} (f : X ⟶ S) :
    SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace) :=
  (SheafOfModules.pushforward (pullback.diagonal f).toRingCatSheafHom).obj
    (SheafOfModules.unit (moduleRings X.toRingedSpace))

/-- The diagonal algebra in degree zero, before localization.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingDiagonalComplex {X S : Scheme.{u}} (f : X ⟶ S) :
    CochainComplex (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj (relativeDualizingDiagonalModule f)

/-- The ordinary total tensor of the two degree-zero diagonal complexes.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingDiagonalTensorComplex {X S : Scheme.{u}} (f : X ⟶ S) :
    CochainComplex (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) ℤ :=
  pullbackTensorTotal (pullback f f)
    (relativeDualizingDiagonalComplex f) (relativeDualizingDiagonalComplex f)

/-- Multiplication of diagonal sections characterizes the chain multiplication uniquely.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def IsRelativeDualizingDiagonalMultiplication {X S : Scheme.{u}} (f : X ⟶ S)
    (t : relativeDualizingDiagonalTensorComplex f ⟶ relativeDualizingDiagonalComplex f) :
    Prop :=
  letI := SheafOfModules.monoidalCategory (pullback f f).sheaf
  ∀ (U : (pullback f f).Opens)
    (a b : ((relativeDualizingDiagonalComplex f).X 0).val.obj (op U)),
    ((HomologicalComplex.ιMapBifunctor
        (relativeDualizingDiagonalComplex f) (relativeDualizingDiagonalComplex f)
        (curriedTensor _) (.up ℤ) 0 0 0 (by decide) ≫ t.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (relativeDualizingDiagonalModule f)).hom).val.app (op U))
      ((SheafOfModules.tensorObjIsoSheafification (R := (pullback f f).sheaf)
        ((relativeDualizingDiagonalComplex f).X 0)
        ((relativeDualizingDiagonalComplex f).X 0)).inv.val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (moduleRings (pullback f f).toRingedSpace).obj)).unit.app
          (((relativeDualizingDiagonalComplex f).X 0).val ⊗
            ((relativeDualizingDiagonalComplex f).X 0).val)).app (op U) (a ⊗ₜ b))) =
      (@id (X.presheaf.obj (op ((pullback.diagonal f) ⁻¹ᵁ U)))
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (relativeDualizingDiagonalModule f)).hom.val.app (op U) a)) *
      (@id (X.presheaf.obj (op ((pullback.diagonal f) ⁻¹ᵁ U)))
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (relativeDualizingDiagonalModule f)).hom.val.app (op U) b))

/-- The multiplication is uniquely specified by the ordinary diagonal algebra.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair).
Proof: the total tensor of two complexes supported in degree zero is supported in
 degree zero. Multiply sections in O_X on the inverse image of each open of X ×_S X.
These bilinear maps commute with restrictions and hence factor uniquely through
module sheafification of the sectionwise tensor. They define the degree-zero
component, with zero components elsewhere. The differentials vanish. Pure tensors
and the total-tensor summand inclusions determine every component, proving uniqueness. -/
theorem existsUnique_relativeDualizingDiagonalMultiplication
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ∃! t : relativeDualizingDiagonalTensorComplex f ⟶ relativeDualizingDiagonalComplex f,
      IsRelativeDualizingDiagonalMultiplication f t := by
  sorry

/-- The canonical derived multiplication of Δ_* O_X, from its actual algebra multiplication.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingDiagonalMultiplication {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))] :
    DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⊗
      DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
        DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) :=
  pullbackTensorModelMap (pullback f f)
      (relativeDualizingDiagonalComplex f) (relativeDualizingDiagonalComplex f) ≫
    DerivedCategory.Q.map
      (Classical.choose (existsUnique_relativeDualizingDiagonalMultiplication f).exists)

/-- The scalar map, the canonical transpose of the left unit action.
Source: Stacks 0E2V (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingScalarMap (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) :
    𝟙_ (schemeDerivedCategory X) ⟶
      (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op K, K) :=
  (schemeDerivedTensorHomEquiv X _ K K).symm (λ_ K).hom

/-- Multiplication by a diagonal class, transposed under the canonical tensor-Hom bijection.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def relativeDualizingClassMap {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))]
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K) :
    DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedInternalHom (Opens.grothendieckTopology (pullback f f : Scheme.{u}))
        (pullback f f).sheaf).obj
          (op (DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)),
            (derivedPullback (pullback.fst f f)).obj K) :=
  (schemeDerivedTensorHomEquiv (pullback f f : Scheme.{u}) _ _ _).symm
    (relativeDualizingDiagonalMultiplication f ≫ ξ)

/-- A supplied coherent relative dualizing pair: pseudo-coherence, locally finite
Tor amplitude over S, and invertibility of multiplication by its specified diagonal class.
Source: Stacks 0E2T (blueprint: def-trf-coherent-relative-dualizing-pair). -/
def IsCoherentRelativeDualizingPair
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K) : Prop :=
  Scheme.IsPseudoCoherent X K ∧
    (∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Scheme.HasFiniteTorDimensionOver (U.ι ≫ f) ((derivedPullback U.ι).obj K)) ∧
    IsIso (relativeDualizingClassMap f K ξ)

end AlgebraicGeometry
