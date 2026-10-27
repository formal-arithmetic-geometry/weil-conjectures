# Profinite.TameInertiaScalarMate

## Reason

Extract the scalar tensor and normalized derived-adjunction data into a module shared
by the ordinary and derived computation lemmas. This avoids an import cycle when the
item proves its theorem from those two smaller statements. Every existing definition,
its binders, fields and body remains identical. The item publicly reexports the new
module and keeps Computes and scalar_mate_isomorphism unchanged in signature. No target
statement or mathematical definition changes.

## Old

The following block was declared in Sheaf.Paper.TameInertiaScalarMate:

```lean
variable (E Ω : Type u) [NormedField E] [NormedField Ω] [Algebra E Ω]
  (h : Continuous (algebraMap E Ω))

/-- The actual balanced internal scalar tensor, using the existing coequalizer.
Source: C_Omega tensor_{C_E} -
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
abbrev tensor : CondensedAction.Modules (ring E) ⥤ CondensedAction.Modules (ring Ω) :=
  Mod.extendScalars (coefficientMap E Ω h).hom

/-- The section represented by z tensor x. The ordinary scalar unit is literally
`Mod.extendUnit`, so this generator belongs to the existing balanced tensor object.
Source: the displayed degreewise representative
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def tensorGenerator (A : CondensedAction.Modules (ring E)) (S : Profinite.{u})
    (z : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (ring Ω).X).obj (op S))
    (x : CondensedAction.sectionModule (ring E) A S) :
    CondensedAction.sectionModule (ring Ω) ((tensor E Ω h).obj A) S :=
  z • (show CondensedAction.sectionModule (ring Ω) ((tensor E Ω h).obj A) S from
    (((Mod.extendUnit (coefficientMap E Ω h).hom A).hom.hom.app (op S)).hom x))

variable [(coefficientRestriction E Ω h).Additive]
  [PreservesFiniteLimits (coefficientRestriction E Ω h)]
  [PreservesFiniteColimits (coefficientRestriction E Ω h)]

/-- A universal left derived pair for the existing scalar tensor and its unit-normalized
adjunction to exact scalar restriction. This specifies the transported adjunction of
`SheafOfModules.sheafRingDerivedCoefficientAdjunction`, not an arbitrary adjunction.
The unit equation holds after the canonical comparison on every complex, and thus
fixes the derived adjunction, including its scalar unit.
Source: Stacks 07A6, as used in steps 4-5 of the scalar-mate calculation
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
structure DerivedTensor where
  /-- Ordinary unbounded total left derived scalar extension. -/
  functor : DerivedCategory (CondensedAction.Modules (ring E)) ⥤
    DerivedCategory (CondensedAction.Modules (ring Ω))
  /-- Its canonical computation comparison, directed from derived to ordinary tensor. -/
  comparison : DerivedCategory.Qh ⋙ functor ⟶
    (tensor E Ω h).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  /-- The universal property at all quasi-isomorphisms. -/
  universal : functor.IsLeftDerivedFunctor comparison
    (HomotopyCategory.quasiIso (CondensedAction.Modules (ring E)) (.up ℤ))
  /-- Adjunction to the actual termwise scalar restriction. -/
  adjunction : functor ⊣ (coefficientRestriction E Ω h).mapDerivedCategory
  /-- The actual scalar unit, with exact-functor transports displayed. -/
  unit : ∀ P : HomotopyCategory (CondensedAction.Modules (ring E)) (.up ℤ),
    adjunction.unit.app (DerivedCategory.Qh.obj P) ≫
      (coefficientRestriction E Ω h).mapDerivedCategory.map (comparison.app P) ≫
      (coefficientRestriction E Ω h).mapDerivedCategoryFactorsh.hom.app
        (((tensor E Ω h).mapHomotopyCategory (.up ℤ)).obj P) =
    DerivedCategory.Qh.map
      (((Mod.extendRestrictAdjunction (coefficientMap E Ω h).hom).mapHomotopyCategory
        (.up ℤ)).unit.app P)

variable (p ℓ r : ℕ) [ActionAbelianData p r E] [ActionAbelianData p r Ω]
  [Context p r E] [Context p r Ω] [ScalarRestriction E p r Ω h]
  [RestrictionUniversal E p r Ω h]
  (dE : Realization E p ℓ r E) (dΩ : Realization E p ℓ r Ω)
  (m : CoefficientMaps E p ℓ r Ω h dE dΩ)

/-- The chain map adjunct to the literal coefficient inclusion. Thus neither the chain
map nor its source is an arbitrary isomorphic replacement.
Source: t in step 3 (blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def tensorMap (M : Inputs E p ℓ r) :
    ((tensor E Ω h).mapHomologicalComplex (.up ℤ)).obj (dE.koszul.obj M) ⟶
      dΩ.koszul.obj M :=
  (((Mod.extendRestrictAdjunction (coefficientMap E Ω h).hom).mapHomologicalComplex
    (.up ℤ)).homEquiv _ _).symm (m.koszul.app M)

/-- The actual derived scalar-adjunction adjunct of the recorded coefficient unit
followed by the invariant/scalar-restriction comparison.
Source: sigma_M in the statement
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def mate (s : DerivedTensor E Ω h) (M : Inputs E p ℓ r) :
    s.functor.obj ((derivedInvariants E p ℓ r E dE).obj M) ⟶
      (derivedInvariants E p ℓ r Ω dΩ).obj M :=
  (s.adjunction.homEquiv _ _).symm
    (representationCoefficient E p ℓ r Ω h dE dΩ m M)

```

## New

The identical block is declared in Sheaf.Paper.TameInertiaScalarMateData:

```lean
variable (E Ω : Type u) [NormedField E] [NormedField Ω] [Algebra E Ω]
  (h : Continuous (algebraMap E Ω))

/-- The actual balanced internal scalar tensor, using the existing coequalizer.
Source: C_Omega tensor_{C_E} -
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
abbrev tensor : CondensedAction.Modules (ring E) ⥤ CondensedAction.Modules (ring Ω) :=
  Mod.extendScalars (coefficientMap E Ω h).hom

/-- The section represented by z tensor x. The ordinary scalar unit is literally
`Mod.extendUnit`, so this generator belongs to the existing balanced tensor object.
Source: the displayed degreewise representative
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def tensorGenerator (A : CondensedAction.Modules (ring E)) (S : Profinite.{u})
    (z : (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) (ring Ω).X).obj (op S))
    (x : CondensedAction.sectionModule (ring E) A S) :
    CondensedAction.sectionModule (ring Ω) ((tensor E Ω h).obj A) S :=
  z • (show CondensedAction.sectionModule (ring Ω) ((tensor E Ω h).obj A) S from
    (((Mod.extendUnit (coefficientMap E Ω h).hom A).hom.hom.app (op S)).hom x))

variable [(coefficientRestriction E Ω h).Additive]
  [PreservesFiniteLimits (coefficientRestriction E Ω h)]
  [PreservesFiniteColimits (coefficientRestriction E Ω h)]

/-- A universal left derived pair for the existing scalar tensor and its unit-normalized
adjunction to exact scalar restriction. This specifies the transported adjunction of
`SheafOfModules.sheafRingDerivedCoefficientAdjunction`, not an arbitrary adjunction.
The unit equation holds after the canonical comparison on every complex, and thus
fixes the derived adjunction, including its scalar unit.
Source: Stacks 07A6, as used in steps 4-5 of the scalar-mate calculation
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
structure DerivedTensor where
  /-- Ordinary unbounded total left derived scalar extension. -/
  functor : DerivedCategory (CondensedAction.Modules (ring E)) ⥤
    DerivedCategory (CondensedAction.Modules (ring Ω))
  /-- Its canonical computation comparison, directed from derived to ordinary tensor. -/
  comparison : DerivedCategory.Qh ⋙ functor ⟶
    (tensor E Ω h).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  /-- The universal property at all quasi-isomorphisms. -/
  universal : functor.IsLeftDerivedFunctor comparison
    (HomotopyCategory.quasiIso (CondensedAction.Modules (ring E)) (.up ℤ))
  /-- Adjunction to the actual termwise scalar restriction. -/
  adjunction : functor ⊣ (coefficientRestriction E Ω h).mapDerivedCategory
  /-- The actual scalar unit, with exact-functor transports displayed. -/
  unit : ∀ P : HomotopyCategory (CondensedAction.Modules (ring E)) (.up ℤ),
    adjunction.unit.app (DerivedCategory.Qh.obj P) ≫
      (coefficientRestriction E Ω h).mapDerivedCategory.map (comparison.app P) ≫
      (coefficientRestriction E Ω h).mapDerivedCategoryFactorsh.hom.app
        (((tensor E Ω h).mapHomotopyCategory (.up ℤ)).obj P) =
    DerivedCategory.Qh.map
      (((Mod.extendRestrictAdjunction (coefficientMap E Ω h).hom).mapHomotopyCategory
        (.up ℤ)).unit.app P)

variable (p ℓ r : ℕ) [ActionAbelianData p r E] [ActionAbelianData p r Ω]
  [Context p r E] [Context p r Ω] [ScalarRestriction E p r Ω h]
  [RestrictionUniversal E p r Ω h]
  (dE : Realization E p ℓ r E) (dΩ : Realization E p ℓ r Ω)
  (m : CoefficientMaps E p ℓ r Ω h dE dΩ)

/-- The chain map adjunct to the literal coefficient inclusion. Thus neither the chain
map nor its source is an arbitrary isomorphic replacement.
Source: t in step 3 (blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def tensorMap (M : Inputs E p ℓ r) :
    ((tensor E Ω h).mapHomologicalComplex (.up ℤ)).obj (dE.koszul.obj M) ⟶
      dΩ.koszul.obj M :=
  (((Mod.extendRestrictAdjunction (coefficientMap E Ω h).hom).mapHomologicalComplex
    (.up ℤ)).homEquiv _ _).symm (m.koszul.app M)

/-- The actual derived scalar-adjunction adjunct of the recorded coefficient unit
followed by the invariant/scalar-restriction comparison.
Source: sigma_M in the statement
(blueprint: lem-sfb-tame-inertia-scalar-mate-isomorphism). -/
def mate (s : DerivedTensor E Ω h) (M : Inputs E p ℓ r) :
    s.functor.obj ((derivedInvariants E p ℓ r E dE).obj M) ⟶
      (derivedInvariants E p ℓ r Ω dΩ).obj M :=
  (s.adjunction.homEquiv _ _).symm
    (representationCoefficient E p ℓ r Ω h dE dΩ m M)

```

Sheaf.Paper.TameInertiaScalarMate has this replacement public import:

```lean
public import Sheaf.Paper.TameInertiaScalarMateData
```

The data module retains every original public import, so these imports and the moved
names remain available through the item. The new modules add only the two named
computation theorems. Their proof dependencies are private imports.

## Users

The source scan with tools/downstream.py and a direct import scan found zero existing
Lean importers of the item. The parent DAG use remains attached to the item and its
unchanged theorem. The delivery contains all three new consumers of the data module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TameInertiaScalarMate | C6 | Public reexport preserves all moved names. |
| Sheaf.Paper.TameInertiaDerivedTensorComputation | new in this delivery | Uses unchanged data. |
| Sheaf.Paper.TameInertiaScalarTensorComputation | new in this delivery | Uses unchanged data. |

No existing consumer requires adaptation; all delivered modules are compiled together.
There is no change to the mathematical meanings used by target statements.

## Status

landed 20261026T081251-L-1904281 2026-10-26 (merge of deliver/C6/Sheaf.Paper.TameInertiaScalarMate)
