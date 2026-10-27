# WeilConjectures.CompactSupportQuotientModuleSpec

## Reason

Profiling the original definition after relocation identified 47--52 seconds in
kernel type checking and another 50--54 seconds in the private-module linter.
The definition repeatedly expands concrete coefficient/module carrier conversions.
The new body factors its two forall-section equations through generic, reducible
formula abbreviations. The first compares the restricted section carrier to the
canonically identical unrestricted carrier using HEq, avoiding repeated kernel
normalization of those concrete presentations. As the carriers are definitionally
the same, HEq is equivalent to the original equality. No
mathematical statement, scalar action, tensor map, or target meaning changes.
The eight declarations are publicly re-exported from their new data module.

## Old

```lean
def CompactSupportQuotientModuleSpec (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m)
    (M : scalarReductionSource.{u, u} l E W)
    (Mm : scalarReductionTarget.{u, u} l E W m)
    (Mn : scalarReductionTarget.{u, u} l E W n)
    (em : (scalarReductionExtension.{u, u} l E W m).obj M ≅ Mm)
    (en : (scalarReductionExtension.{u, u} l E W n).obj M ≅ Mn)
    (a : Mm ⟶ (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)).obj Mn)
    (b : (pbcExtend (compactSupportLevelSheafQuotient l E W m n h)).obj Mm ⟶ Mn) : Prop :=
  (∀ (U : W.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf.{u, u} l E W m).obj.obj U)
      (x : M.val.obj U),
    a.val.app U
      ((em.hom : (scalarReductionExtension.{u, u} l E W m).obj M ⟶ Mm).val.app U
        (compactSupportQuotientTensor l E W m M U s x)) =
      (en.hom : (scalarReductionExtension.{u, u} l E W n).obj M ⟶ Mn).val.app U
        (compactSupportQuotientTensor l E W n M U
        ((compactSupportLevelSheafQuotient l E W m n h).hom.app U s) x)) ∧
  (∀ (U : W.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf.{u, u} l E W m).obj.obj U)
      (t : (integralCoefficientCommRingSheaf.{u, u} l E W n).obj.obj U) (x : M.val.obj U),
    b.val.app U (pbcTensorSection (compactSupportLevelSheafQuotient l E W m n h)
      Mm U t
      ((em.hom : (scalarReductionExtension.{u, u} l E W m).obj M ⟶ Mm).val.app U
        (compactSupportQuotientTensor l E W m M U s x))) =
      (en.hom : (scalarReductionExtension.{u, u} l E W n).obj M ⟶ Mn).val.app U
        (compactSupportQuotientTensor l E W n M U
        (t * (compactSupportLevelSheafQuotient l E W m n h).hom.app U s) x))
```

## New

The two new abbreviations only quantify section functions and carriers. They have
no choices, instances selected from existence, or proof holes.

```lean
abbrev QuotientSectionFormula {S T X Y : Type*} {Z Z' : Type v}
    (q : S → T) (pm : S → X → Y) (pn : T → X → Z) (a : Y → Z') : Prop :=
  ∀ (s : S) (x : X), HEq (a (pm s x)) (pn (q s) x)

/-- The balancing formula for section functions, with all carriers abstract.
Source: ordinary tensor associativity, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-quotient-coordinates). -/
abbrev BalancingSectionFormula {S T X Y Z H : Type*} [Mul T]
    (q : S → T) (pm : S → X → Y) (pn : T → X → Z)
    (tensor : T → Y → H) (b : H → Z) : Prop :=
  ∀ (s : S) (t : T) (x : X), b (tensor t (pm s x)) = pn (t * q s) x

def CompactSupportQuotientModuleSpec (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m)
    (M : scalarReductionSource.{u, u} l E W)
    (Mm : scalarReductionTarget.{u, u} l E W m)
    (Mn : scalarReductionTarget.{u, u} l E W n)
    (em : (scalarReductionExtension.{u, u} l E W m).obj M ≅ Mm)
    (en : (scalarReductionExtension.{u, u} l E W n).obj M ≅ Mn)
    (a : Mm ⟶ (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)).obj Mn)
    (b : (pbcExtend (compactSupportLevelSheafQuotient l E W m n h)).obj Mm ⟶ Mn) : Prop :=
  (∀ U : W.ProEtᵒᵖ, QuotientSectionFormula
    (fun s ↦ (compactSupportLevelSheafQuotient l E W m n h).hom.app U s)
    (fun s x ↦ em.hom.val.app U (compactSupportQuotientTensor l E W m M U s x))
    (fun t x ↦ en.hom.val.app U (compactSupportQuotientTensor l E W n M U t x))
    (fun y ↦ a.val.app U y)) ∧
  (∀ U : W.ProEtᵒᵖ, BalancingSectionFormula
    (fun s ↦ (compactSupportLevelSheafQuotient l E W m n h).hom.app U s)
    (fun s x ↦ em.hom.val.app U (compactSupportQuotientTensor l E W m M U s x))
    (fun t x ↦ en.hom.val.app U (compactSupportQuotientTensor l E W n M U t x))
    (pbcTensorSection (compactSupportLevelSheafQuotient l E W m n h) Mm U)
    (fun y ↦ b.val.app U y))
```

## Restriction comparison presentation aliases

The signatures and visibility of `compactSupportQuotientResId` and
`compactSupportQuotientResComp` are unchanged. Their original construction bodies
are factored through `CompactSupportCoefficientPresentation`: that module has the
same literal identity and composition comparisons, including the same `eqToIso`
factors, with canonical constant-coefficient source and target types. Unfolding the
new aliases gives precisely the old bodies. This changes no equality proof or map.

Profiling the direct identity specialization gave 282 ms of elaboration but 104 s
of kernel checking before a deterministic timeout. Naming the general construction
lets the quotient specialization compare the same named expressions instead of
normalizing the derived categories inside the equality casts repeatedly.

Old `compactSupportQuotientResId`:

```lean
def compactSupportQuotientResId (W : Scheme.{u}) (n : ℕ) :
    (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E n n le_rfl)).mapDerivedCategory ≅ 𝟭 _ :=
  eqToIso (congrArg (fun q ↦ (proEtaleCoefficientRestrictScalars W q).mapDerivedCategory)
      (compactSupportQuotient_self l E n)) ≪≫
    sfOpenDerivedCoefficientRestrictionId W (Padic.coefficientExtensionRing l E (n + 1))
```

New `compactSupportQuotientResId`:

```lean
def compactSupportQuotientResId (W : Scheme.{u}) (n : ℕ) :
    (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E n n le_rfl)).mapDerivedCategory ≅ 𝟭 _ :=
  compactSupportCoefficientResId W (Padic.coefficientExtensionRing l E (n + 1))
    (compactSupportLevelQuotient l E n n le_rfl) (compactSupportQuotient_self l E n)
```

Old `compactSupportQuotientResComp`:

```lean
def compactSupportQuotientResComp (W : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m) :
    (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n hmn)).mapDerivedCategory ⋙
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E r n (hmn.trans hrm))).mapDerivedCategory :=
  sfDerivedCoefficientRestrictionComp W
      (compactSupportLevelQuotient l E r m hrm)
      (compactSupportLevelQuotient l E m n hmn) ≪≫
    eqToIso (congrArg (fun q ↦ (proEtaleCoefficientRestrictScalars W q).mapDerivedCategory)
      (compactSupportQuotient_comp l E r m n hrm hmn))
```

New `compactSupportQuotientResComp`:

```lean
def compactSupportQuotientResComp (W : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m) :
    (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n hmn)).mapDerivedCategory ⋙
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E r n (hmn.trans hrm))).mapDerivedCategory :=
  compactSupportCoefficientResComp W
    (compactSupportLevelQuotient l E r m hrm)
    (compactSupportLevelQuotient l E m n hmn)
    (compactSupportLevelQuotient l E r n (hmn.trans hrm))
    (compactSupportQuotient_comp l E r m n hrm hmn)
```

## Users

`tools/downstream.py Sheaf.Paper.CompactSupportQuotientCocycle --uses
CompactSupportQuotientModuleSpec` reports one module mentioning the declaration:
the item itself, at the definition and representative theorem. The same use scans
for `compactSupportQuotientResId` and `compactSupportQuotientResComp` each report
only the item itself (three mentions each). `rg` confirms no
other current Lean file mentions or unfolds the definition. The two direct
importers of the original module use the unchanged cocycle theorem; both will be
compiled unchanged against this packet before delivery and their temporary copies
removed. All transitive importers retain the same named declarations and
proposition, and no consumer statement changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportQuotientCocycle | Q3 | Same signature; proof checks the unchanged section formulas through reducible abbreviations. |
| Sheaf.Paper.CompactSupportNormalizedRealization | no current claim found | Direct importer; only uses the unchanged cocycle theorem. |
| Sheaf.Paper.CompactSupportFiniteAction | no current claim found | Direct importer; only uses the unchanged cocycle theorem. |

No source-library module is changed. No target statement changes; expanding the new
abbreviations and applying `heq_iff_eq` yields a proposition equivalent to the old one, so no target definition changes
its mathematical meaning. Any target using this definition needs the usual statement/definition review.
No forced adaptation is proposed.

## Status

landed 20261027T135438-L-3708061 2026-10-27 (merge of deliver/Q3/Sheaf.Paper.CompactSupportQuotientCocycle)
