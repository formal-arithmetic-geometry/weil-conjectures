/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import Mathlib.CategoryTheory.Products.Basic
public import WeilConjectures.SecSmoothPurity.NormalizedCoefficientDiagram

/-! # Definition interface for simultaneous strict coefficient comparisons

Source: Stacks 03EL and 07A4; the agent calculations in the eight proof steps of
lem-pur-strict-coefficient-comparison-calculus
(blueprint: lem-pur-strict-coefficient-comparison-calculus).

The product index records coefficient changes and all inverse-sequence arrows.
Semilinear arrows are written in their scalar-extension adjoint form. Thus they
are arbitrary chain maps out of scalar extension, including zero maps, rather
than only the scalar-extension units. All tensors are the existing sheafified
module tensor and its signed direct-sum total complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] CategoryTheory.CochainPullback.extensionAdjunction
attribute [local irreducible] CategoryTheory.CochainPullback.extensionFunctor
attribute [local irreducible] SheafOfModules.systemScalarRestrictionComposition
attribute [local irreducible] SheafOfModules.systemScalarRestrictionUnit
set_option maxErrors 1
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace CategoryTheory.CochainPullback.StrictCoefficient

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The existing tensor isomorphism on total complexes, with instances fixed once.
Source: Stacks 07A4 (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
abbrev totalIso {R : Sheaf J CommRingCat.{w}} {P Q P' Q' : Complex R}
    (f : P ≅ P') (g : Q ≅ Q') : total P Q ≅ total P' Q' :=
  @MonoidalCategory.tensorIso (Complex R) _ inferInstance P P' Q Q' f g

attribute [instance] Diagram.additive

variable (d : Diagram (J := J) (K := K))

/-- The recorded ringed pullback at a coefficient and sequence level.
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Diagram.ringed (i : Index) : RingedPullback (d.R.obj i) (d.S.obj i) where
  uInv := d.inverse
  uPush := d.direct
  adj := d.adj
  finiteLimits := d.finiteLimits
  RI := d.RI.obj i
  I := d.algebraic i
  coefficient := d.phi.app i
  L := d.L i
  hobj := d.hobj i
  hmap := d.hmap i
  V := d.V i
  moduleAdj := d.moduleAdj i
  additive := d.additive i

/-- Cochain scalar-extension composition, using the existing identity-on-sections
restriction comparison and adjoint uniqueness; no arbitrary associator is chosen.
Source: Stacks 03CY, 03EL
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def scalarComp {A B H : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (c : A ⟶ H) (hc : c = a ≫ b) :
    extend a ⋙ extend b ≅ extend c :=
  Functor.mapHomologicalComplexCompIso
    (F := extensionFunctor a) (G := extensionFunctor b) (H := extensionFunctor c)
    (Adjunction.leftAdjointUniq
      (F := extensionFunctor a ⋙ extensionFunctor b) (F' := extensionFunctor c)
      (G := restrictionFunctor c)
      (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
        (SheafOfModules.systemScalarRestrictionComposition a b c hc))
      (extensionAdjunction c)) (.up ℤ)

/-- Cochain action unit for scalar extension along an identity ring map.
Source: Stacks 03CY, 03EL
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def scalarUnit (A : Sheaf J CommRingCat.{w}) : extend (𝟙 A) ≅ 𝟭 (Complex A) :=
  NatIso.mapHomologicalComplex
    (Adjunction.leftAdjointUniq (F := extensionFunctor (𝟙 A))
      (F' := 𝟭 (Modules A)) (G := 𝟭 (Modules A))
      ((extensionAdjunction (𝟙 A)).ofNatIsoRight
        (SheafOfModules.systemScalarRestrictionUnit (𝟙 A) rfl)) Adjunction.id) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (Modules A) (.up ℤ)

attribute [local irreducible] scalarComp scalarUnit

/-- Canonical associator along two arrows of a ring diagram.
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def diagramComp (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k : Index} (a : i ⟶ j) (b : j ⟶ k) :
    extend (B.map a) ⋙ extend (B.map b) ≅ extend (B.map (a ≫ b)) :=
  scalarComp (B.map a) (B.map b) (B.map (a ≫ b)) (B.map_comp a b)

/-- Simultaneous module comparisons. Each sigma is the existing normalized
comparison type: its naturality and generalized pure-tensor formula are fields.
Kappa is a natural isomorphism; its generator normalization is stated separately.
Source: Stacks 03EL (blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
structure Comparisons where
  kappa : ∀ {i j : Index} (t : i ⟶ j),
    d.L i ⋙ extensionFunctor (d.S.map t) ≅ extensionFunctor (d.R.map t) ⋙ d.L j
  sigmaR : ∀ {i j : Index} (t : i ⟶ j), Comparison (extensionPullback (d.R.map t))
  sigmaS : ∀ {i j : Index} (t : i ⟶ j), Comparison (extensionPullback (d.S.map t))

variable {d}

/-- The termwise cochain lift of kappa, retaining the underlying natural isomorphism.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.kappaC (e : Comparisons d) {i j : Index} (t : i ⟶ j)
    (P : Complex (d.R.obj i)) :
    (extend (d.S.map t)).obj ((pull (d.ringed i)).obj P) ≅
      (pull (d.ringed j)).obj ((extend (d.R.map t)).obj P) :=
  (NatIso.mapHomologicalComplex (e.kappa t) (.up ℤ)).app P

/-- The actual induced pullback of an arbitrary semilinear chain map, expressed
by its scalar-extension adjoint. This permits every strict-system transition,
including zero transitions and maps not invertible after scalar extension.
Source: Stacks 03CY and 03EL
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def Comparisons.pullArrow (e : Comparisons d) {i j : Index} (t : i ⟶ j)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj j))
    (f : (extend (d.R.map t)).obj P ⟶ Q) :
    (extend (d.S.map t)).obj ((pull (d.ringed i)).obj P) ⟶
      (pull (d.ringed j)).obj Q :=
  (e.kappaC t P).hom ≫ (pull (d.ringed j)).map f

/-- Transport an arbitrary semilinear transition across a commuting square of
coefficient and sequence arrows, using the canonical scalar associators.
Source: Stacks 03CY, 03EL, and the item's proof step 5
(blueprint: lem-pur-strict-coefficient-comparison-calculus). -/
def squareArrow (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P : Complex (B.obj i)) (Q : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ Q) :
    (extend (B.map s)).obj ((extend (B.map a)).obj P) ⟶
      (extend (B.map b)).obj Q :=
  (diagramComp B a s).hom.app P ≫
    eqToHom (congrArg (fun t ↦ (extend (B.map t)).obj P) h) ≫
      (diagramComp B r b).inv.app P ≫ (extend (B.map b)).map f

end CategoryTheory.CochainPullback.StrictCoefficient
