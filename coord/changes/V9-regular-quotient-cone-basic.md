# SheafOfModules.RegularQuotientCone: extract common constructions

## Reason

The strict-chain and flat-sequence lemmas need the scalar/cone definitions, while the main
augmentation theorem imports those lemmas. Extracting the existing definitions into a common
module avoids an import cycle. Every declaration name, universe, binder, body and visibility is
retained. The old module publicly imports the common module, so its public API is preserved.
No target statement or definition changes mathematically.

## Old

In lean/Sheaf/Algebra/Homology/RegularQuotientConeAugmentation.lean:

```lean
/-- The recorded module category, as a transparent abbreviation.
Source: Stacks 06YY (blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- The recorded restriction functor, as a transparent abbreviation.
Source: Stacks 03D7 (blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable abbrev restriction {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

/-- Multiplication by the compatible family of local scalars defining a global section.
Source: Stacks 06YP, principal-resolution construction
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def scalar (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (Modules R) ⟶ 𝟭 (Modules R) where
  app M := { val := {
    app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (t.val U))
    naturality := by
      intro U V f
      ext x
      change t.val V • M.val.map f x = M.val.map f (t.val U • x)
      rw [M.val.map_smul]
      congr 1
      exact (t.property f).symm } }
  naturality {M N} f := by
    ext U x
    change t.val U • f.val.app U x = f.val.app U (t.val U • x)
    exact ((f.val.app U).hom.map_smul (t.val U) x).symm

/-- The map of unit modules induced by the ring-sheaf map.
Source: Stacks 06YP, principal-resolution construction
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def ringMap {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    unit (derivedChangeRingIndependentCoefficients J R) ⟶
      (restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) :=
  ((restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S))).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : S.obj.obj U))
      (fun {_ _} f ↦ map_one (S.obj.map f).hom))

/-- Multiplication by the global section on an unbounded cochain complex.
Source: Stacks 06YP, principal-resolution construction
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def complexScalar (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ 𝟭 (CochainComplex (Modules R) ℤ) where
  app P := {
    f := fun n ↦ (scalar R t).app (P.X n)
    comm' := fun i j _ ↦ ((scalar R t).naturality (P.d i j)).symm }
  naturality {_P _Q} f := by
    ext n : 1
    exact (scalar R t).naturality (f.f n)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The strict cone functor, with diagonal action on chain maps.
Source: Stacks 06YP, principal quotient construction
(blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def cone (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ where
  obj P := CochainComplex.mappingCone ((complexScalar R t).app P)
  map {_P _Q} h := CochainComplex.mappingCone.map _ _ h h
    ((complexScalar R t).naturality h).symm
  map_id _P := CochainComplex.mappingCone.map_id _
  map_comp _f _g := CochainComplex.mappingCone.map_comp _ _ _ _ _ _ _ _ _

/-- The canonical inclusion into the unshifted summand of the cone.
Source: Stacks 06YP (blueprint: lem-cbc-regular-quotient-cone-augmentation). -/
noncomputable def inclusion (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ cone R t where
  app P := CochainComplex.mappingCone.inr ((complexScalar R t).app P)
  naturality {P Q} h := by
    ext n : 1
    simp [cone, CochainComplex.mappingCone.map]
```

## New

The same definitions, verbatim, are in
lean/Sheaf/Algebra/Homology/RegularQuotientConeBasic.lean. The old module re-exports them by:

```lean
public import Sheaf.Algebra.Homology.RegularQuotientConeBasic
```

The defining terms and signatures printed under Old are unchanged. The new basic DAG attachment
records their location; the original attachment continues to record Augmentation and its theorem.

## Users

`python3 tools/downstream.py Sheaf.Algebra.Homology.RegularQuotientConeAugmentation --uses
Modules restriction scalar ringMap complexScalar cone inclusion Augmentation nonempty_augmentation`
found zero downstream Lean modules. All textual uses of these names are in the item itself.
The existing unfinished DAG parent is preserved and continues to cite the item theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RegularQuotientConeAugmentation | V9 | Same public definitions via re-export; proof now uses the new auxiliary lemmas. |

## Status

landed 20261021T173349-L-3592564 2026-10-21 (merge of deliver/V9/Sheaf.Algebra.Homology.RegularQuotientConeAugmentation)
