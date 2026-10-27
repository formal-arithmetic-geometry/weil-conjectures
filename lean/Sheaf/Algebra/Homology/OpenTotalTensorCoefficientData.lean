module

public import Sheaf.CategoryTheory.SliceTensorGeneratorCoherence
public import Sheaf.CategoryTheory.RingedSliceTensorGenerators
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import Mathlib.Algebra.Homology.Functor

/-! # Strict coefficient interchange for open total tensor

Source: Stacks Project, Modules on Sites, Tag 0E8I, and Cohomology on Sites,
Tag 0GL1; agent coefficient refinement
(blueprint: def-sf-open-total-tensor-coefficient-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


attribute [local irreducible] SheafOfModules.monoidalCategory

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
namespace SheafOfModules.OpenTotalTensorCoefficient

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- A transparent presentation of the existing Complex construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
abbrev Complex (A : Sheaf J CommRingCat.{max c v r}) :=
  CochainComplex (Modules.{c, v, r} A) ℤ

/-- A transparent presentation of the existing slice construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
abbrev slice (A : Under R) := (sliceAlgebras.{c, v, r} R V).obj A

/-- A transparent presentation of the existing extension construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def extension : Complex.{max c v, v, r} (R.over V) ⥤ Complex.{c, v, r} R :=
  letI := localizedSystemExtensionAdditive.{c, v, r} R V
  (localizedSystemExtension.{c, v, r} R V).mapHomologicalComplex (.up ℤ)
/-- A transparent presentation of the existing restriction construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def restriction : Complex.{c, v, r} R ⥤ Complex.{max c v, v, r} (R.over V) :=
  letI := localizedSystemRestrictionAdditive.{c, v, r} R V
  (localizedSystemRestriction.{c, v, r} R V).mapHomologicalComplex (.up ℤ)

/-- A transparent presentation of the existing change construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def change {A B : Sheaf J CommRingCat.{max c v r}} (a : A ⟶ B) :
    Complex.{c, v, r} A ⥤ Complex.{c, v, r} B :=
  CategoryTheory.CochainPullback.extend.{max c v r, c, v} a

/-- A transparent presentation of the existing forget construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def forget {A B : Sheaf J CommRingCat.{max c v r}} (a : A ⟶ B) :
    Complex.{c, v, r} B ⥤ Complex.{c, v, r} A :=
  CategoryTheory.CochainPullback.restrictComplex.{max c v r, c, v} a

/-- A transparent presentation of the existing total construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def total (P Q : Complex.{c, v, r} R) : Complex.{c, v, r} R :=
  P ⊗ Q

/-- A transparent presentation of the existing totalSection construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def totalSection (P Q : Complex.{c, v, r} R) (p q n : ℤ) (h : p + q = n)
    (W : Cᵒᵖ) (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W) :=
  (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules.{c, v, r} R)) p q n h).val.app W
    (SheafOfModules.LocalizedStrictTensor.pure.{c, v, r} R _ _ W x y)

/-- A transparent presentation of the existing extendedTotal construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def extendedTotal
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    Complex.{c, v, r} R :=
  total.{c, v, r} R ((extension.{c, v, r} R V).obj Q) F

/-- A transparent presentation of the existing sliceTotal construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def sliceTotal
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    Complex.{max c v, v, r} (R.over V) :=
  total.{max c v, v, r} (R.over V) Q ((restriction.{c, v, r} R V).obj F)

/-- A transparent presentation of the existing source construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def source (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    Complex.{c, v, r} A.right :=
  (change.{c, v, r} A.hom).obj (extendedTotal.{c, v, r} R V Q F)

/-- A transparent presentation of the existing intermediate construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def intermediate (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    Complex.{c, v, r} A.right :=
  total.{c, v, r} A.right
    ((change.{c, v, r} A.hom).obj ((extension.{c, v, r} R V).obj Q))
    ((change.{c, v, r} A.hom).obj F)

/-- A transparent presentation of the existing sliceTarget construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def sliceTarget (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    Complex.{max c v, v, r} (A.right.over V) :=
  sliceTotal.{c, v, r} A.right V
    ((change.{max c v, v, r} (slice.{c, v, r} R V A).hom).obj Q)
    ((change.{c, v, r} A.hom).obj F)

/-- A transparent presentation of the existing target construction.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def target (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    Complex.{c, v, r} A.right :=
  (extension.{c, v, r} A.right V).obj (sliceTarget.{c, v, r} R V A Q F)

/-- The scalar-extension generator of the source total complex.
Source: Stacks 03EK and 0E8I
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def sourceSection (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
    (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
    (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
    (a : A.right.obj.obj (op W)) :
    ((source.{c, v, r} R V A Q F).X n).val.obj (op W) :=
  CategoryTheory.CochainPullback.extensionTmul.{max c v r, c, v} A.hom _ (op W) a
    (totalSection.{c, v, r} R _ F p q n h (op W)
      (extensionSection.{c, v, r} R V (Q.X p) W f x) y)

/-- A target generator with two independent coefficient entries.
Source: Stacks 03EK and 0E8I
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
def targetSection (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R)
    (p q n : ℤ) (h : p + q = n) (W : C) (f : W ⟶ V)
    (x : (Q.X p).val.obj (op (Over.mk f))) (y : (F.X q).val.obj (op W))
    (a b : A.right.obj.obj (op W)) :
    ((target.{c, v, r} R V A Q F).X n).val.obj (op W) :=
  extensionSection.{c, v, r} A.right V _ W f
    (totalSection.{max c v, v, r} (A.right.over V)
        ((change.{max c v, v, r} (slice.{c, v, r} R V A).hom).obj Q)
        ((restriction.{c, v, r} A.right V).obj ((change.{c, v, r} A.hom).obj F))
        p q n h (op (Over.mk f))
      (CategoryTheory.CochainPullback.extensionTmul.{max c v r, max c v, v}
        (slice.{c, v, r} R V A).hom (Q.X p) (op (Over.mk f)) a x)
      (CategoryTheory.CochainPullback.extensionTmul.{max c v r, c, v}
        A.hom (F.X q) (op W) b y))

/-- The ordinary normalized comparisons, with actual scalar-linear sources and targets.
Source: Stacks 0E8I and 03EL
(blueprint: def-sf-open-total-tensor-coefficient-data). -/
structure Comparisons where
  gamma : ∀ (B : Sheaf J CommRingCat.{max c v r})
    (Q : Complex.{max c v, v, r} (B.over V)) (F : Complex.{c, v, r} B),
    extendedTotal.{c, v, r} B V Q F ≅
      (extension.{c, v, r} B V).obj (sliceTotal.{c, v, r} B V Q F)
  linear : ∀ (A : Under R) (Q : Complex.{max c v, v, r} (R.over V)),
    (change.{c, v, r} A.hom).obj ((extension.{c, v, r} R V).obj Q) ≅
      (extension.{c, v, r} A.right V).obj
        ((change.{max c v, v, r} (slice.{c, v, r} R V A).hom).obj Q)
  restrictionCoefficient : ∀ (A : Under R) (F : Complex.{c, v, r} R),
    (change.{max c v, v, r} (slice.{c, v, r} R V A).hom).obj
        ((restriction.{c, v, r} R V).obj F) ≅
      (restriction.{c, v, r} A.right V).obj ((change.{c, v, r} A.hom).obj F)

/-- The balanced coefficient comparison is exactly the existing normalized epsilon.
Source: Stacks 03EL (blueprint: def-sf-open-total-tensor-coefficient-data). -/
def Comparisons.baseBalanced (_e : Comparisons.{c, v, r} R V) (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    source.{c, v, r} R V A Q F ≅ intermediate.{c, v, r} R V A Q F :=
  CategoryTheory.CochainPullback.epsilon A.hom ((extension.{c, v, r} R V).obj Q) F

/-- The slice epsilon is followed by the normalized restriction-tensor identification.
Source: Stacks 03EL (blueprint: def-sf-open-total-tensor-coefficient-data). -/
def Comparisons.sliceBalanced (e : Comparisons.{c, v, r} R V) (A : Under R)
    (Q : Complex.{max c v, v, r} (R.over V)) (F : Complex.{c, v, r} R) :
    (change.{max c v, v, r} (slice.{c, v, r} R V A).hom).obj
        (sliceTotal.{c, v, r} R V Q F) ≅ sliceTarget.{c, v, r} R V A Q F :=
  CategoryTheory.CochainPullback.epsilon (slice.{c, v, r} R V A).hom Q
      ((restriction.{c, v, r} R V).obj F) ≪≫
    (tensorLeft ((change.{max c v, v, r} (slice.{c, v, r} R V A).hom).obj Q)).mapIso
      (e.restrictionCoefficient A F)


end SheafOfModules.OpenTotalTensorCoefficient
