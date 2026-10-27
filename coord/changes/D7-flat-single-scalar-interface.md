# FlatSingleScalar ordinary interface location

## Reason

The ordinary action comparison is a separate mathematical result, needed before
flatness or derived-category arguments. Move its definitions into a shared interface
so its module and the assigned theorem can both import them without a cycle.
The assigned module publicly imports the interface. Declaration names, signatures,
values, visibility, instances and universes are unchanged. This is dependency
separation; no compiler performance limit motivates it.

## Old

These declarations occurred in Sheaf.Paper.FlatSingleScalarConventions:

```lean
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

```

## New

Exactly the declarations above occur verbatim in
Sheaf.Paper.FlatSingleScalarInterface. The assigned module has:

```lean
public import Sheaf.Paper.FlatSingleScalarInterface
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FlatSingleScalarConventions | D7 | Publicly reexports the identical interface. |
| Sheaf.Paper.QcqsLatticeTreeReconstruction | unclaimed | Its existing proof import resolves the same declarations; no edit. |

The source scan with tools/downstream.py found only the latter downstream module.
Its textual hits for Modules refer to unrelated module categories; it uses none
of the moved qualified declarations.
No target statement or definition value changes.

## Status

landed 20261023T104910-L-3455684 2026-10-23 (merge of deliver/D7/Sheaf.Paper.FlatSingleScalarConventions)
