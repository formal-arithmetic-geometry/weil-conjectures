/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceCotangentRingMap
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import WeilConjectures.CategoryTheory.SheafPolynomialCotangentComparison

/-! # The naive cotangent complex of an algebraic-space morphism

Source: Stacks Project, More on Morphisms of Spaces, Tag 0D0V; Modules on Sites,
Tags 08TW and 08U0 (blueprint: def-sfb-space-naive-cotangent-complex).

We retain the existing small affine site, actual regular functions and original module
universe. The conormal quotient is constructed as B ⊗_P I. Its canonical quotient map
has locally the kernel I², identifying it with the sheaf quotient I/I². Only the proofs
of the quotient and differential universal properties are postponed, never their data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings ZeroObject

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The canonical polynomial presentation of the actual inverse-image structural map.
Source: Stacks 0D0V, 08TW, 08U0
(blueprint: def-sfb-space-naive-cotangent-complex). -/
abbrev cotangentPresentation (f : X ⟶ Y) :=
  SheafPolynomialCotangent.canonical (cotangentRingMap f)

/-- The conormal sheaf, constructed by the existing sheaf tensor and scalar extension.
The canonical map from I has kernel locally I², as recorded below.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex). -/
def cotangentConormal (f : X ⟶ Y) : X.SmallModules :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u, u, u}
    (SheafPolynomialCotangent.evaluation (cotangentRingMap f)
      (cotangentPresentation f).values)
    (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).module

/-- The actual class b ⊗ g in the sheafified conormal module.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex). -/
def cotangentConormalTensor (f : X ⟶ Y) (U : X.SmallEtaleModelᵒᵖ)
    (b : X.smallStructureSheaf.obj.obj U)
    (g : (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).sections U.unop) :
    (cotangentConormal f).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.smallStructureRings.obj)).unit.app
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u, u, u}
      (SheafPolynomialCotangent.evaluation (cotangentRingMap f)
        (cotangentPresentation f).values)
      (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).module)).app U)
    (b ⊗ₜ[_, ((SheafPolynomialCotangent.evaluation (cotangentRingMap f)
      (cotangentPresentation f).values).hom.app U).hom] g)

/-- The class of g is the tensor 1 ⊗ g, with no choice of representatives.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex). -/
def cotangentConormalClass (f : X ⟶ Y) (U : X.SmallEtaleModelᵒᵖ)
    (g : (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).sections U.unop) :
    (cotangentConormal f).val.obj U :=
  cotangentConormalTensor f U 1 g

/-- The quotient classes respect addition, the evaluation-induced scalar action and
restriction. Source: Stacks 08TW
(blueprint: def-sfb-space-naive-cotangent-complex).
Proof: the tensor relations give additivity and balancing, and the sheafification unit
is linear. The tensor restriction formula sends 1 ⊗ g to 1 ⊗ g restricted; naturality
of the sheafification unit gives the last equality. -/
theorem cotangentConormalClass_relations (f : X ⟶ Y) :
    (∀ (U : X.SmallEtaleModelᵒᵖ)
      (g h : (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).sections U.unop),
      cotangentConormalClass f U (g + h) =
        cotangentConormalClass f U g + cotangentConormalClass f U h) ∧
    (∀ (U : X.SmallEtaleModelᵒᵖ)
      (p : (SheafPolynomialCotangent.polynomialSheaf
        ((cotangentRingInverse f).obj Y.smallStructureSheaf)
        (cotangentPresentation f).generators).obj.obj U)
      (g : (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).sections U.unop),
      cotangentConormalClass f U (p • g) =
        (SheafPolynomialCotangent.evaluation (cotangentRingMap f)
          (cotangentPresentation f).values).hom.app U p • cotangentConormalClass f U g) ∧
    (∀ (U V : X.SmallEtaleModelᵒᵖ) (r : U ⟶ V)
      (g : (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).sections U.unop),
      (cotangentConormal f).val.map r (cotangentConormalClass f U g) =
        cotangentConormalClass f V
          ((SheafPolynomialCotangent.kernelIdeal
            (cotangentPresentation f)).module.val.map r g)) := by
  sorry

/-- The actual P-linear quotient map I → B ⊗_P I, restricted along evaluation.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex). -/
def cotangentConormalQuotient (f : X ⟶ Y) :
    (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).module ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose X.smallEtaleModelTopology (forget₂ CommRingCat RingCat)).map
          (SheafPolynomialCotangent.evaluation (cotangentRingMap f)
            (cotangentPresentation f).values))).obj (cotangentConormal f) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (SheafPolynomialCotangent.kernelIdeal
          (cotangentPresentation f)).module.val.obj U)
        (Y := ((SheafOfModules.restrictScalars
          ((sheafCompose X.smallEtaleModelTopology (forget₂ CommRingCat RingCat)).map
            (SheafPolynomialCotangent.evaluation (cotangentRingMap f)
              (cotangentPresentation f).values))).obj (cotangentConormal f)).val.obj U)
        { toFun := cotangentConormalClass f U
          map_add' := (cotangentConormalClass_relations f).1 U
          map_smul' := (cotangentConormalClass_relations f).2.1 U }
      naturality := fun {U V} r ↦ ModuleCat.hom_ext
        (LinearMap.ext (fun g ↦ ((cotangentConormalClass_relations f).2.2 U V r g).symm)) }

/-- This is exactly the sheaf quotient I/I², with its evaluation-induced B action.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex).
Proof: evaluation is sheaf-surjective, so locally B=P/I. Tensoring I with P/I gives
I/I². The tensor quotient is therefore locally surjective and its kernel consists of
sections locally in I². Sheafification detects precisely this local kernel. Balancing
gives b[g]=[pg] for any local lift p of b; differences of lifts lie in I and hence
change the product by I². This also covers changing g by I². -/
theorem cotangentConormalQuotient_properties (f : X ⟶ Y) :
    Presheaf.IsLocallySurjective X.smallEtaleModelTopology
      ((PresheafOfModules.toPresheaf _).map (cotangentConormalQuotient f).val) ∧
    (∀ (U : X.SmallEtaleModelᵒᵖ)
      (g : (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).sections U.unop),
      cotangentConormalClass f U g = 0 ↔
        SheafPolynomialCotangent.LocallyInKernelSquare (cotangentPresentation f) U g) := by
  sorry

/-- There is a unique B-linear differential with the prescribed value on every kernel
class. Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex).
Proof: the Leibniz rule gives d(gh)⊗1=0 when g,h lie in I, so the derivation factors
through the sheaf quotient I/I². For p in P, d(pg)⊗1=p dg⊗1 since g evaluates to zero;
thus the factor is B-linear. Restriction commutes with the derivation and tensor units,
so these maps glue. The locally surjective quotient map proves uniqueness. -/
theorem cotangentDifferential_existsUnique (f : X ⟶ Y) :
    ∃! d : cotangentConormal f ⟶
        SheafPolynomialCotangent.differentialTerm (cotangentPresentation f),
      ∀ (U : X.SmallEtaleModelᵒᵖ)
        (g : (SheafPolynomialCotangent.kernelIdeal (cotangentPresentation f)).sections U.unop),
        d.val.app U (cotangentConormalClass f U g) =
          SheafPolynomialCotangent.tensorD (cotangentPresentation f) U 1 g := by
  sorry

/-- The uniquely determined differential [g] ↦ dg ⊗ 1.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex). -/
def cotangentDifferential (f : X ⟶ Y) : cotangentConormal f ⟶
    SheafPolynomialCotangent.differentialTerm (cotangentPresentation f) :=
  (cotangentDifferential_existsUnique f).choose

/-- Terms in degrees -1 and 0, with actual zero objects in every other degree.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex). -/
def naiveCotangentTerm (f : X ⟶ Y) (i : ℤ) : X.SmallModules :=
  if i = -1 then cotangentConormal f
  else if i = 0 then SheafPolynomialCotangent.differentialTerm (cotangentPresentation f)
  else 0

/-- Identification of the two nonzero terms.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex).
Proof: evaluate the two conditionals at -1 and at 0, respectively. -/
theorem naiveCotangentTerm_degrees (f : X ⟶ Y) :
    naiveCotangentTerm f (-1) = cotangentConormal f ∧
    naiveCotangentTerm f 0 =
      SheafPolynomialCotangent.differentialTerm (cotangentPresentation f) := by
  sorry

/-- The conormal differential in degree -1 and zero differentials elsewhere.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex). -/
def naiveCotangentBoundary (f : X ⟶ Y) (i : ℤ) :
    naiveCotangentTerm f i ⟶ naiveCotangentTerm f (i + 1) :=
  if h : i = -1 then
    eqToHom (congrArg (naiveCotangentTerm f) h) ≫
      eqToHom (naiveCotangentTerm_degrees f).1 ≫ cotangentDifferential f ≫
      eqToHom (naiveCotangentTerm_degrees f).2.symm ≫
      eqToHom (congrArg (naiveCotangentTerm f) (congrArg (· + 1) h).symm)
  else 0

/-- Consecutive differentials have zero composite.
Source: Stacks 08TW (blueprint: def-sfb-space-naive-cotangent-complex).
Proof: the only potentially nonzero boundary starts in degree -1, so each consecutive
pair contains a zero boundary. Composition with zero is zero. -/
theorem naiveCotangentBoundary_comp (f : X ⟶ Y) (i : ℤ) :
    naiveCotangentBoundary f i ≫ naiveCotangentBoundary f (i + 1) = 0 := by
  sorry

/-- The naive cotangent complex of f on the existing small affine ringed model.
Source: Stacks 0D0V, 08TW, 08U0
(blueprint: def-sfb-space-naive-cotangent-complex). -/
def naiveCotangentComplex (f : X ⟶ Y) : CochainComplex X.SmallModules ℤ :=
  CochainComplex.of (naiveCotangentTerm f) (naiveCotangentBoundary f)
    (naiveCotangentBoundary_comp f)

/-- Its image in the same unbounded derived module category, at arbitrary localization size.
Source: Stacks 0D0V, 08TW (blueprint: def-sfb-space-naive-cotangent-complex). -/
def naiveCotangent (f : X ⟶ Y) [HasDerivedCategory.{w} X.SmallModules] :
    X.DerivedModules :=
  DerivedCategory.Q.obj (naiveCotangentComplex f)

/-- Ext means Hom into the shifted second argument in the existing derived category.
Source: Stacks 0D0V (blueprint: def-sfb-space-naive-cotangent-complex). -/
abbrev derivedExt (X : AlgebraicSpace S) [HasDerivedCategory.{w} X.SmallModules]
    (E F : X.DerivedModules) (n : ℤ) := E ⟶ F⟦n⟧

/-- A coefficient module sheaf viewed in degree zero for the preceding Ext convention.
Source: Stacks 0D0V (blueprint: def-sfb-space-naive-cotangent-complex). -/
def cotangentCoefficient (X : AlgebraicSpace S) [HasDerivedCategory.{w} X.SmallModules]
    (F : X.SmallModules) : X.DerivedModules :=
  (DerivedCategory.singleFunctor X.SmallModules 0).obj F

end AlgebraicGeometry.AlgebraicSpace
