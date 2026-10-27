/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.CategoryTheory.SliceTensorGeneratorCoherence
public import Sheaf.CategoryTheory.RingedSliceTensorGenerators
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Localization.Construction
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Data for strict scalar-unit augmentation of the open total tensor

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor;
Cohomology on Sites, Tag 0GL1, and the agent's strict scalar-unit refinement.
(blueprint: def-sf-open-tensor-scalar-unit-data).

## Main definitions

* `SheafOfModules.OpenTensorAugmentation.StrictTotals` fixes the total towers and transitions.
* `SheafOfModules.OpenTensorAugmentation.Augmentation` fixes the normalized augmentation square.

## Main statements

* `SheafOfModules.OpenTensorAugmentation.Augmentation` records the normalized square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor SheafOfModules.SliceTensorGenerator
namespace SheafOfModules.OpenTensorAugmentation
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- Additivity transported from the existing ordinary scalar-extension presentation.
Only its prescribed ordinary functor and additivity are used; no derived computation
or K-flatness assumption is introduced.
Source: Stacks 03EK (blueprint: def-sf-open-tensor-scalar-unit-data). -/
instance extensionAdditive {R A : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ A) :
    (extend.{c, v, r} a).Additive :=
  let m := (nonempty_derivedChangeOfRingsCochainModel.{c, v, max c v r,
    max c v (max c v r + 1), max c v (max c v r + 1)} a).some
  Functor.additive_of_iso (F := m.E)
    (NatIso.ofComponents (fun M ↦ eqToIso (m.obj_eq M)) (by
      intro M N f
      change m.E.map f ≫ eqToHom (m.obj_eq N) =
        eqToHom (m.obj_eq M) ≫ changeOfRingsHomOfUniverses a M f
      rw [m.map_eq]
      simp
      rfl))

/-- The actual scalar-extension functor applied termwise, with no derived tensor.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def scalarComplex {R A : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ A) :=
  letI := extensionAdditive.{c, v, r} a
  (extend.{c, v, r} a).mapHomologicalComplex (.up ℤ)

/-- The existing coefficient restriction applied termwise.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def scalarRestriction (R : Sheaf J CommRingCat.{max c v r}) (A : Under R) :=
  (scalars.{c, v, r} R A).mapHomologicalComplex (.up ℤ)

/-- Pairs of arbitrary unbounded complexes, with both chain maps as morphisms.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
abbrev Inputs (R : Sheaf J CommRingCat.{max c v r}) (V : C) :=
  CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ ×
    CochainComplex (Modules.{c, v, r} R) ℤ

/-- The ordinary source G = Tot(j!Q tensor F), functorial in Q and F.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def source (R : Sheaf J CommRingCat.{max c v r}) (V : C) :
    Inputs.{c, v, r} R V ⥤ CochainComplex (Modules.{c, v, r} R) ℤ :=
  ((ringedOpenExtensionOnComplexes.{c, v, r} R V).prod (𝟭 _)) ⋙
    Functor.uncurry.obj (ringedOpenTotalTensor.{c, v, r} R)

/-- The ordinary slice source G_V = Tot(Q tensor j*F), functorial in both inputs.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def sliceSource (R : Sheaf J CommRingCat.{max c v r}) (V : C) :
    Inputs.{c, v, r} R V ⥤ CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ :=
  ((𝟭 _).prod (ringedOpenRestrictionOnComplexes.{c, v, r} R V)) ⋙
    Functor.uncurry.obj (ringedOpenTotalTensor.{max c v, v, r} (R.over V))

/-- The specified coefficient-linear total T_n, followed by scalar restriction.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def targetLevel (R : Sheaf J CommRingCat.{max c v r}) (V : C) (A : Under R) :
    Inputs.{c, v, r} R V ⥤ CochainComplex (Modules.{c, v, r} R) ℤ :=
  ((ringedOpenExtensionOnComplexes.{c, v, r} R V ⋙ scalarComplex.{c, v, r} A.hom).prod
      (scalarComplex.{c, v, r} A.hom)) ⋙
    Functor.uncurry.obj (ringedOpenTotalTensor.{c, v, r} A.right) ⋙ scalarRestriction.{c, v, r} R A

/-- The specified slice total S_n over A restricted to V, followed by scalar restriction.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def sliceTargetLevel (R : Sheaf J CommRingCat.{max c v r}) (V : C)
    [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}] (A : Under R) :
    Inputs.{c, v, r} R V ⥤ CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ :=
  ((scalarComplex.{max c v, v, r} ((sliceAlgebras.{c, v, r} R V).obj A).hom).prod
      (scalarComplex.{c, v, r} A.hom ⋙
        ringedOpenRestrictionOnComplexes.{c, v, r} A.right V)) ⋙
    Functor.uncurry.obj (ringedOpenTotalTensor.{max c v, v, r} (A.right.over V)) ⋙
      scalarRestriction.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A)

/-- Termwise extension J_B on strict towers of unbounded complexes.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def extendTower (R : Sheaf J CommRingCat.{max c v r}) (V : C) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (ringedOpenExtensionOnComplexes.{c, v, r} R V)

/-- A homogeneous pure tensor followed by the direct-sum insertion into the total.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def totalSection (R : Sheaf J CommRingCat.{max c v r})
    (P F : CochainComplex (Modules.{c, v, r} R) ℤ)
    (p q d : ℤ) (h : p + q = d) (W : Cᵒᵖ)
    (x : (P.X p).val.obj W) (y : (F.X q).val.obj W) :
    ((((ringedOpenTotalTensor.{c, v, r} R).obj P).obj F).X d).val.obj W :=
  (ringedOpenTensorι.{c, v, r} R P F p q d h).val.app W
    (SheafOfModules.LocalizedStrictTensor.pure.{c, v, r} R (P.X p) (F.X q) W x y)

/-- The original extension generator followed by the signed total-tensor insertion.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def sourceSection (R : Sheaf J CommRingCat.{max c v r}) (V : C)
    (Z : Inputs.{c, v, r} R V) (p q d : ℤ) (h : p + q = d)
    (W : C) (f : W ⟶ V) (x : (Z.1.X p).val.obj (op (Over.mk f)))
    (y : (Z.2.X q).val.obj (op W)) : (((source.{c, v, r} R V).obj Z).X d).val.obj (op W) :=
  totalSection.{c, v, r} R ((ringedOpenExtensionOnComplexes.{c, v, r} R V).obj Z.1)
    Z.2 p q d h (op W) (extensionSection.{c, v, r} R V (Z.1.X p) W f x) y

/-- A homogeneous generator of T_n, using the actual scalar-extension sheafification units.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def targetSection (R : Sheaf J CommRingCat.{max c v r}) (V : C)
    (A : Under R) (Z : Inputs.{c, v, r} R V) (p q d : ℤ) (h : p + q = d)
    (W : C) (x : (((ringedOpenExtensionOnComplexes.{c, v, r} R V).obj Z.1).X p).val.obj
      (op W)) (y : (Z.2.X q).val.obj (op W))
    (a b : A.right.obj.obj (op W)) :
    (((targetLevel.{c, v, r} R V A).obj Z).X d).val.obj (op W) :=
  totalSection.{c, v, r} A.right
    ((scalarComplex.{c, v, r} A.hom).obj
      ((ringedOpenExtensionOnComplexes.{c, v, r} R V).obj Z.1))
    ((scalarComplex.{c, v, r} A.hom).obj Z.2) p q d h (op W)
    (scalarExtensionSection.{c, v, max c v r, max c v r} A.hom _ (op W) a x)
    (scalarExtensionSection.{c, v, max c v r, max c v r} A.hom _ (op W) b y)

/-- A homogeneous generator of S_n; restriction keeps the original sections.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def sliceTargetSection (R : Sheaf J CommRingCat.{max c v r}) (V : C)
    [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (A : Under R) (Z : Inputs.{c, v, r} R V) (p q d : ℤ) (h : p + q = d)
    (W : Over V) (x : (Z.1.X p).val.obj (op W))
    (y : (Z.2.X q).val.obj (op W.left)) (a b : A.right.obj.obj (op W.left)) :
    (((sliceTargetLevel.{c, v, r} R V A).obj Z).X d).val.obj (op W) :=
  totalSection.{max c v, v, r} (A.right.over V)
    ((scalarComplex.{max c v, v, r} ((sliceAlgebras.{c, v, r} R V).obj A).hom).obj Z.1)
    ((ringedOpenRestrictionOnComplexes.{c, v, r} A.right V).obj
      ((scalarComplex.{c, v, r} A.hom).obj Z.2)) p q d h (op W)
    (scalarExtensionSection.{max c v, v, max c v r, max c v r}
      ((sliceAlgebras.{c, v, r} R V).obj A).hom _ (op W) a x)
    (scalarExtensionSection.{c, v, max c v r, max c v r} A.hom _ (op W.left) b y)

/-- The slice generator in G_V, before termwise extension.
Source: Stacks 03EK, 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def sliceSourceSection (R : Sheaf J CommRingCat.{max c v r}) (V : C)
    [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (Z : Inputs.{c, v, r} R V) (p q d : ℤ) (h : p + q = d)
    (W : Over V) (x : (Z.1.X p).val.obj (op W))
    (y : (Z.2.X q).val.obj (op W.left)) :
    (((sliceSource.{c, v, r} R V).obj Z).X d).val.obj (op W) :=
  totalSection.{max c v, v, r} (R.over V) Z.1
    ((ringedOpenRestrictionOnComplexes.{c, v, r} R V).obj Z.2) p q d h (op W) x y

variable (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The actual total tensor towers, with their transitions characterized on sheafified
presheaf generators. A map acts on both inserted coefficients through the same algebra
map. Identity and composition laws are strict; each transition is a chain map and is
natural in both input complexes. These fields are conclusions of the existence theorem,
not extra hypotheses on the site, coefficients or complexes.
Source: Stacks 03EK and 0E8I, strict refinement
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
structure StrictTotals (A : AlgebraTowers.{c, v, r} R) where
  /-- Coefficient transition in T, on the prescribed objects. -/
  t : ∀ {m n : ℕᵒᵖ}, (m ⟶ n) →
    (targetLevel.{c, v, r} R V (A.obj m) ⟶ targetLevel.{c, v, r} R V (A.obj n))
  /-- T has identity transitions. -/
  t_id : ∀ n, t (𝟙 n) = 𝟙 _
  /-- T has compositional transitions. -/
  t_comp : ∀ {l m n} (a : l ⟶ m) (b : m ⟶ n), t (a ≫ b) = t a ≫ t b
  /-- Coefficient transition in S, on the prescribed objects. -/
  s : ∀ {m n : ℕᵒᵖ}, (m ⟶ n) →
    (sliceTargetLevel.{c, v, r} R V (A.obj m) ⟶ sliceTargetLevel.{c, v, r} R V (A.obj n))
  /-- S has identity transitions. -/
  s_id : ∀ n, s (𝟙 n) = 𝟙 _
  /-- S has compositional transitions. -/
  s_comp : ∀ {l m n} (a : l ⟶ m) (b : m ⟶ n), s (a ≫ b) = s a ≫ s b
  /-- Both scalar factors in T are mapped by the unital algebra transition. -/
  t_generator : ∀ {m n} (g : m ⟶ n) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : C)
    (x : (((ringedOpenExtensionOnComplexes.{c, v, r} R V).obj Z.1).X p).val.obj (op W))
    (y : (Z.2.X q).val.obj (op W)) (a b : (A.obj m).right.obj.obj (op W)),
    (((t g).app Z).f d).val.app (op W)
        (targetSection.{c, v, r} R V (A.obj m) Z p q d h W x y a b) =
      targetSection.{c, v, r} R V (A.obj n) Z p q d h W x y
        ((A.map g).right.hom.app (op W) a) ((A.map g).right.hom.app (op W) b)
  /-- The same two coefficient transitions on the slice. -/
  s_generator : ∀ {m n} (g : m ⟶ n) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : Over V)
    (x : (Z.1.X p).val.obj (op W)) (y : (Z.2.X q).val.obj (op W.left))
    (a b : (A.obj m).right.obj.obj (op W.left)),
    (((s g).app Z).f d).val.app (op W)
        (sliceTargetSection.{c, v, r} R V (A.obj m) Z p q d h W x y a b) =
      sliceTargetSection.{c, v, r} R V (A.obj n) Z p q d h W x y
        ((A.map g).right.hom.app (op W.left) a) ((A.map g).right.hom.app (op W.left) b)

/-- Assemble the actual T transitions into the strict functor of both inputs.
Source: Stacks 03EK (blueprint: def-sf-open-tensor-scalar-unit-data). -/
def StrictTotals.T {A : AlgebraTowers.{c, v, r} R} (e : StrictTotals.{c, v, r} R V A) :
    ℕᵒᵖ ⥤ Inputs.{c, v, r} R V ⥤ CochainComplex (Modules.{c, v, r} R) ℤ where
  obj n := targetLevel.{c, v, r} R V (A.obj n)
  map g := e.t g
  map_id := e.t_id
  map_comp := e.t_comp

/-- Assemble the actual S transitions into the strict functor of both inputs.
Source: Stacks 03EK (blueprint: def-sf-open-tensor-scalar-unit-data). -/
def StrictTotals.S {A : AlgebraTowers.{c, v, r} R} (e : StrictTotals.{c, v, r} R V A) :
    ℕᵒᵖ ⥤ Inputs.{c, v, r} R V ⥤
      CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ where
  obj n := sliceTargetLevel.{c, v, r} R V (A.obj n)
  map g := e.s g
  map_id := e.s_id
  map_comp := e.s_comp

/-- Apply actual termwise extension to a functor of both input complexes.
Source: Stacks 03DI (blueprint: def-sf-open-tensor-scalar-unit-data). -/
def extendInputs :=
  (Functor.whiskeringRight (Inputs.{c, v, r} R V) _ _).obj
    (ringedOpenExtensionOnComplexes.{c, v, r} R V)

/-- The lower-then-right augmentation route, including the canonical constant-functor
identification. This names exactly Delta(gammaBase) followed by J(cS).
Source: Stacks 0E8I and 0GL1
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def lowerRoute {A : AlgebraTowers.{c, v, r} R} (e : StrictTotals.{c, v, r} R V A)
    (b : source.{c, v, r} R V ≅
      sliceSource.{c, v, r} R V ⋙ ringedOpenExtensionOnComplexes.{c, v, r} R V)
    (a : (Functor.const ℕᵒᵖ).obj (sliceSource.{c, v, r} R V) ⟶ e.S R V) :
    (Functor.const ℕᵒᵖ).obj (source.{c, v, r} R V) ⟶
      e.S R V ⋙ extendInputs.{c, v, r} R V :=
  (Functor.const ℕᵒᵖ).map b.hom ≫
    (Functor.constComp ℕᵒᵖ (sliceSource.{c, v, r} R V)
      (extendInputs.{c, v, r} R V)).inv ≫
    Functor.whiskerRight a (extendInputs.{c, v, r} R V)

/-- Evaluation at both input complexes leaves a genuine map of strict complex systems.
Source: Stacks 03EK and the inverse-system convention
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
def atInput
    {F G : ℕᵒᵖ ⥤ Inputs.{c, v, r} R V ⥤ CochainComplex (Modules.{c, v, r} R) ℤ}
    (a : F ⟶ G) (Z : Inputs.{c, v, r} R V) : F.flip.obj Z ⟶ G.flip.obj Z :=
  ((CategoryTheory.flipFunctor _ _ _).map a).app Z

/-- The scalar-unit augmentation square as strict, natural chain maps. All maps are
fixed by their values on original extension and tensor presheaf generators. The formula
for gamma is precisely the composite of the normalized coefficient-linear r comparison
with the normalized slice tensor isomorphism and identity-on-summands scalar restriction.
Source: Stacks 0E8I, 0GL1, strict scalar-unit refinement
(blueprint: def-sf-open-tensor-scalar-unit-data). -/
structure Augmentation (A : AlgebraTowers.{c, v, r} R) where
  /-- Strict coefficient totals, including all transition formulas. -/
  totals : StrictTotals.{c, v, r} R V A
  /-- The ordinary slice total-tensor isomorphism. -/
  gammaBase : source.{c, v, r} R V ≅
    sliceSource.{c, v, r} R V ⋙ ringedOpenExtensionOnComplexes.{c, v, r} R V
  /-- Generator normalization fixes the actual ordinary slice comparison. -/
  base_generator : ∀ (Z : Inputs.{c, v, r} R V) (p q d : ℤ) (h : p + q = d)
    (W : C) (f : W ⟶ V) (x : (Z.1.X p).val.obj (op (Over.mk f)))
    (y : (Z.2.X q).val.obj (op W)),
    ((gammaBase.hom.app Z).f d).val.app (op W)
        (sourceSection.{c, v, r} R V Z p q d h W f x y) =
      extensionSection.{c, v, r} R V _ W f
        (sliceSourceSection.{c, v, r} R V Z p q d h (Over.mk f) x y)
  /-- The chain isomorphism of strict towers, natural in Q and F. -/
  gamma : totals.T R V ≅ totals.S R V ⋙ extendInputs.{c, v, r} R V
  /-- This is the generator formula for gamma^{A_n} composed with Tot(r tensor 1). -/
  gamma_generator : ∀ (n : ℕᵒᵖ) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : C) (f : W ⟶ V)
    (x : (Z.1.X p).val.obj (op (Over.mk f))) (y : (Z.2.X q).val.obj (op W))
    (a b : (A.obj n).right.obj.obj (op W)),
    (((gamma.hom.app n).app Z).f d).val.app (op W)
        (targetSection.{c, v, r} R V (A.obj n) Z p q d h W
          (extensionSection.{c, v, r} R V (Z.1.X p) W f x) y a b) =
      extensionSection.{c, v, r} R V _ W f
        (sliceTargetSection.{c, v, r} R V (A.obj n) Z p q d h (Over.mk f) x y a b)
  /-- The source augmentation is a natural map from the constant strict tower. -/
  cT : (Functor.const ℕᵒᵖ).obj (source.{c, v, r} R V) ⟶ totals.T R V
  /-- It inserts 1 into both scalar tensor factors on homogeneous generators. -/
  cT_generator : ∀ (n : ℕᵒᵖ) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : C) (f : W ⟶ V)
    (x : (Z.1.X p).val.obj (op (Over.mk f))) (y : (Z.2.X q).val.obj (op W)),
    (((cT.app n).app Z).f d).val.app (op W)
        (sourceSection.{c, v, r} R V Z p q d h W f x y) =
      targetSection.{c, v, r} R V (A.obj n) Z p q d h W
        (extensionSection.{c, v, r} R V (Z.1.X p) W f x) y 1 1
  /-- The slice augmentation is also a strict, natural chain map. -/
  cS : (Functor.const ℕᵒᵖ).obj (sliceSource.{c, v, r} R V) ⟶ totals.S R V
  /-- Its formula on the actual tensor presheaf generators. -/
  cS_generator : ∀ (n : ℕᵒᵖ) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : Over V)
    (x : (Z.1.X p).val.obj (op W)) (y : (Z.2.X q).val.obj (op W.left)),
    (((cS.app n).app Z).f d).val.app (op W)
        (sliceSourceSection.{c, v, r} R V Z p q d h W x y) =
      sliceTargetSection.{c, v, r} R V (A.obj n) Z p q d h W x y 1 1
  /-- The augmentation square is an equality before any localization. -/
  square : cT ≫ gamma.hom = lowerRoute.{c, v, r} R V totals gammaBase cS
  /-- Both routes have this same value on every homogeneous extension generator. -/
  common_value : ∀ (n : ℕᵒᵖ) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : C) (f : W ⟶ V)
    (x : (Z.1.X p).val.obj (op (Over.mk f))) (y : (Z.2.X q).val.obj (op W)),
    ((((cT ≫ gamma.hom).app n).app Z).f d).val.app (op W)
        (sourceSection.{c, v, r} R V Z p q d h W f x y) =
      extensionSection.{c, v, r} R V _ W f
        (sliceTargetSection.{c, v, r} R V (A.obj n) Z p q d h (Over.mk f) x y 1 1)
  /-- Localization of strict complex systems preserves the augmentation equality.
  In particular one may invert all levelwise quasi-isomorphisms. -/
  localized_square : ∀ (Z : Inputs.{c, v, r} R V)
    (W : MorphismProperty (ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, r} R) ℤ)),
    W.Q.map (atInput.{c, v, r} R V (cT ≫ gamma.hom) Z) =
      W.Q.map (atInput.{c, v, r} R V (lowerRoute.{c, v, r} R V totals gammaBase cS) Z)

end SheafOfModules.OpenTensorAugmentation
