/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Sheaf.CategoryTheory.SiteCoveringAxioms
/-! # Flat degree-zero scalar extension in two conventions

Source: Stacks Project, Modules on Sites, Tags 03EK and 03ER(3), Cohomology on
Sites, Tags 06YQ and 06YY, and blueprint `sk-def-sfb-change-of-scalars`(2)
and `sk-def-sfb-derived-categories` (blueprint: lem-sfb-flat-single-scalar-conventions).

The identifications below retain the given underlying module actions. The monoid-side
extension is the recorded `Mod.extendScalars`, including its coequalizer projection.
The section-side extension is the prescribed sheafified `changeOfRings`, as recorded
by `DerivedChangeOfRingsCochainModel`. No flatness of the target ring is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r wR wB

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped ChangeOfRings

namespace SheafOfModules.FlatSingleScalar

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The existing module-sheaf category, without a change in coefficient universe.
Source: Stacks 03EK (blueprint: lem-sfb-flat-single-scalar-conventions). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

variable {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)

/-- The target ring as an R-module, with its given scalar action through φ.
Source: Stacks 03EK (blueprint: lem-sfb-flat-single-scalar-conventions). -/
abbrev scalarAlgebra : Modules R :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

/-- A local pure tensor in the existing localization tensor, via sheafification.
Source: Stacks 03EK (blueprint: lem-sfb-flat-single-scalar-conventions). -/
def tensorSection (M N : Modules R) (U : Cᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app U (m ⊗ₜ[R.obj.obj U] n))

/-- Presentations of precisely the two action-preserving identifications in the node.
The monoid unit is φ, its multiplication is that of B, and the module equivalence
intertwines the given B-actions on all local pure tensors. The unit-module equivalence
is identified with the identity on underlying R-modules; unitality forces its action.
These are presentations of the prescribed notions, not additional assumptions.
Source: Stacks 03EK and blueprint change of scalars (2)
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
structure Identifications where
  /-- B with its actual multiplication as an R-algebra object. -/
  [monoid : MonObj (scalarAlgebra φ)]
  /-- Commutativity of the given ring multiplication. -/
  [commutative : IsCommMonObj (scalarAlgebra φ)]
  /-- Its unit is a monoid homomorphism from the tensor unit. -/
  [unitHom : IsMonHom (η[scalarAlgebra φ])]
  /-- The monoid unit is exactly the given ring morphism. -/
  one_sections : ∀ (U : Cᵒᵖ) (a : R.obj.obj U),
    (η[scalarAlgebra φ]).val.app U a = (φ.hom.app U) a
  /-- The monoid multiplication is the local ring multiplication. -/
  mul_sections : ∀ (U : Cᵒᵖ) (b b' : B.obj.obj U),
    (μ[scalarAlgebra φ]).val.app U
      (tensorSection (scalarAlgebra φ) (scalarAlgebra φ) U b b') = b * b'
  /-- Modules over the unit monoid are R-module sheaves. -/
  unitModules : Modules R ≌ Mod (Modules R) (𝟙_ (Modules R))
  /-- This identification retains the underlying module. -/
  unitUnderlying : unitModules.functor ⋙ Mod.forget (𝟙_ (Modules R)) ≅ 𝟭 (Modules R)
  /-- Modules over B internally are sheaves of B-modules. -/
  modules : Modules B ≌ Mod (Modules R) (scalarAlgebra φ)
  /-- This identification retains the underlying R-module. -/
  underlying : modules.functor ⋙ Mod.forget (scalarAlgebra φ) ≅
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  /-- The internal module action is exactly its given sectionwise B-action. -/
  action_sections : ∀ (N : Modules B) (U : Cᵒᵖ) (b : B.obj.obj U)
      (n : (modules.functor.obj N).X.val.obj U),
    (underlying.hom.app N).val.app U
      ((ModObj.smul (M := scalarAlgebra φ) (X := (modules.functor.obj N).X)).val.app U
        (tensorSection (scalarAlgebra φ) (modules.functor.obj N).X U b n)) =
      b • (@id (N.val.obj U) ((underlying.hom.app N).val.app U n))
  /-- The transported ordinary extension is additive. -/
  [additive : (unitModules.functor ⋙ Mod.extendScalars (η[scalarAlgebra φ]) ⋙
    modules.inverse).Additive]

/-- The actual coequalizer extension, transported along the action identifications.
Source: blueprint change of scalars (2)
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
abbrev monExtension (d : Identifications φ) : Modules R ⥤ Modules B :=
  letI := d.monoid
  letI := d.unitHom
  d.unitModules.functor ⋙ Mod.extendScalars (η[scalarAlgebra φ]) ⋙ d.modules.inverse

/-- Additivity retained from the ordinary action identification.
Source: Stacks 03EK (blueprint: lem-sfb-flat-single-scalar-conventions). -/
instance monExtension_additive (d : Identifications φ) : (monExtension φ d).Additive :=
  d.additive

/-- The balancing-coequalizer projection on underlying R-modules. The factors are
only the specified underlying identifications and the actual `Mod.extendπ`.
Source: blueprint change of scalars (2)
(blueprint: lem-sfb-flat-single-scalar-conventions). -/
def projection (d : Identifications φ) (M : Modules R) :
    scalarAlgebra φ ⊗ M ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        ((monExtension φ d).obj M) :=
  letI := d.monoid
  letI := d.unitHom
  scalarAlgebra φ ◁ (d.unitUnderlying.app M).inv ≫
    Mod.extendπ (η[scalarAlgebra φ]) (d.unitModules.functor.obj M) ≫
    (d.modules.counitIso.app
      ((Mod.extendScalars (η[scalarAlgebra φ])).obj (d.unitModules.functor.obj M))).inv.hom ≫
    (d.underlying.app ((monExtension φ d).obj M)).hom

end SheafOfModules.FlatSingleScalar
