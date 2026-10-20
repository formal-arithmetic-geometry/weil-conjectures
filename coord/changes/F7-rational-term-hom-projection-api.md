# CategoryTheory.RationalTermHom.zeroProjection

## Reason

The original data definitions made elaboration repeatedly traverse the full
Hom-complex existence specification and automatically unfold wrappers for single
complexes and sheaf Hom. The complete proof exceeded the file's 60-second limit.
The projection API now uses a compact structure whose value field is fixed by an
equality to exactly the old `Classical.choose` family. Its product and naturality
laws come from the original specification. `projectionData_exists` is proved,
not a new hole, and no arbitrary witness is selected from an unproved theorem.

The existing `single`, `coefficients`, `ordinary`, and `resolved` abbreviations
become ordinary definitions with explicit, unchanged types and universe arguments.
`HomologicalComplex.single _ (ComplexShape.up ℤ) 0` is definitionally equal to
`CochainComplex.singleFunctor _ 0`; likewise the new body of `resolved` is exactly
the definition of `homComplex`. `ordinaryMap` and `resolvedMap` use the same maps.
The normalization is unchanged because `ProjectionData.eq_chosen` pins the new
projection family to the original one. `comparison`, `localizedObject` and
`localizedMap` keep their constructions; explicit universe annotations introduce
no new mathematical parameters or constraints.

All new instance attributes are local. The project target
signatures in `Challenge.lean` are untouched. Targets depending transitively on
these definitions should be reviewed for preserved meaning; the equalities above
show that no statement is strengthened or weakened.

## Old

The old wrapper and projection definitions, verbatim:

```lean
/-- The degree-zero complex of a module sheaf. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev single
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).obj F

/-- The coefficient sheaf as a module over itself. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev coefficients :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The complex B(F) = Hom(F,R)[0]. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev ordinary
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  single R (SheafOfModules.homObj (R := R) F (coefficients R))

/-- The complex T(F) = Hom-complex(F[0],I). Source: Stacks, Sections 08J7 and 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev resolved
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  homComplex (R := R) (single R F) I

/-- Precomposition on B. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def ordinaryMap
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ G) : ordinary R G ⟶ ordinary R F :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).map
    (SheafOfModules.homObjMap (R := R) f (𝟙 (coefficients R)))

/-- Precomposition on T. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def resolvedMap
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ G) : resolved R I G ⟶ resolved R I F :=
  ((homComplexFunctor (R := R)).map
    ((CochainComplex.singleFunctor _ (0 : ℤ)).map f).op).app I

/-- Projection to the (0,0) factor of the existing Hom complex. Its product projections
are those in the specification of `homComplexFunctor`. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def zeroProjection
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (resolved R (single R (coefficients R)) F).X 0 ⟶
      SheafOfModules.homObj (R := R) ((single R F).X 0)
        ((single R (coefficients R)).X 0) :=
  Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
      (single R F) (single R (coefficients R)) 0 0 0 rfl

/-- The normalized degree-zero identification with the Hom complex. Source: Stacks,
Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison).
The displayed projection is the identity on ordinary local linear maps, transported
through the canonical degree-zero isomorphisms of the single complexes. -/
def IsNormalized
    (e : ∀ F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      ordinary R F ≅ resolved R (single R (coefficients R)) F) : Prop :=
  ∀ F, (e F).hom.f 0 ≫ zeroProjection R F =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.homObj (R := R) F (coefficients R))).hom ≫
        SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (coefficients R)).inv

/-- Postcomposition with j, following the normalized identification. Source: Stacks,
Tag 08JI (blueprint: lem-sf-rational-term-hom-comparison). -/
def comparison
    (e : ∀ F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      ordinary R F ≅ resolved R (single R (coefficients R)) F)
    {I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (j : single R (coefficients R) ⟶ I)
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ordinary R F ⟶ resolved R I F :=
  (e F).hom ≫ ((homComplexFunctor (R := R)).obj (op (single R F))).map j
```

## New

The replacement wrapper and projection definitions, verbatim:

```lean
/-- The degree-zero complex of a module sheaf. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
def single
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).obj F

/-- The coefficient sheaf as a module over itself. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
def coefficients :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
  SheafOfModules.unit.{u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The complex B(F) = Hom(F,R)[0]. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
def ordinary
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
  single R (SheafOfModules.homObj.{u, u, u, u} (R := R) F (coefficients R))

/-- The complex T(F) = Hom-complex(F[0],I). Source: Stacks, Sections 08J7 and 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def resolved
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
  ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op (single R F))).obj I

/-- Precomposition on B. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def ordinaryMap
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : F ⟶ G) : ordinary R G ⟶ ordinary R F :=
  (HomologicalComplex.single (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ) (0 : ℤ)).map
    (SheafOfModules.homObjMap.{u, u, u, u} (R := R) f (𝟙 (coefficients R)))

/-- Precomposition on T. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def resolvedMap
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : F ⟶ G) : resolved R I G ⟶ resolved R I F :=
  ((homComplexFunctor.{u, u, u, u} (R := R)).map
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).map f).op).app I

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A compact package for the already chosen Hom-complex projections. The equality
field fixes its data, so choosing this package makes no new choice of projections.
Source: Stacks, Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison). -/
structure ProjectionData where
  value : ∀ (L M : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n p q : ℤ), p + n = q →
      ((((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L)).obj M).X n ⟶
        SheafOfModules.homObj.{u, u, u, u} (R := R) (L.X p) (M.X q))
  eq_chosen : value = Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  isLimit : ∀ (L M : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (n : ℤ),
    Nonempty (IsLimit (Fan.mk
      ((((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L)).obj M).X n)
      (fun p : ℤ ↦ value L M n p (p + n) rfl)))
  map : ∀ (L L' M M' : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (h : p + n = q),
    ((((homComplexFunctor.{u, u, u, u} (R := R)).map f.op).app M) ≫
      ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L')).map g).f n ≫
        value L' M' n p q h =
      value L M n p q h ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) (f.f p) (g.f q)

/-- The compact projection package exists with exactly the existing chosen family.
Source: Stacks, Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison).
Proof: put the existing family in the value field, use reflexivity for its equality,
and take both laws from its already proved specification. -/
theorem projectionData_exists : Nonempty (ProjectionData R) := by
  let h := homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R)
  exact ⟨⟨Classical.choose h, rfl, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.2⟩⟩

/-- The existing product projection, obtained through its compact, uniquely fixed package.
Source: Stacks, Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison). -/
def projection
    (L M : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L)).obj M).X n ⟶
      SheafOfModules.homObj.{u, u, u, u} (R := R) (L.X p) (M.X q) :=
  (Classical.choice (projectionData_exists R)).value L M n p q h

private lemma projection_eq
    (L M : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    projection R L M n p q h = Classical.choose
      (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
        L M n p q h :=
  congrArg (fun π ↦ π L M n p q h)
    (Classical.choice (projectionData_exists R)).eq_chosen

/-- Projection to the (0,0) factor of the existing Hom complex. Its product projections
are those in the specification of `homComplexFunctor`. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def zeroProjection
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    (resolved R (single R (coefficients R)) F).X 0 ⟶
      SheafOfModules.homObj.{u, u, u, u} (R := R) ((single R F).X 0)
        ((single R (coefficients R)).X 0) :=
  projection R (single R F) (single R (coefficients R)) 0 0 0 rfl

/-- The normalized degree-zero identification with the Hom complex. Source: Stacks,
Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison).
The displayed projection is the identity on ordinary local linear maps, transported
through the canonical degree-zero isomorphisms of the single complexes. -/
def IsNormalized
    (e : ∀ F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ordinary R F ≅ resolved R (single R (coefficients R)) F) : Prop :=
  ∀ F, (e F).hom.f 0 ≫ zeroProjection R F =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.homObj.{u, u, u, u} (R := R) F (coefficients R))).hom ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R)
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (coefficients R)).inv

/-- Postcomposition with j, following the normalized identification. Source: Stacks,
Tag 08JI (blueprint: lem-sf-rational-term-hom-comparison). -/
def comparison
    (e : ∀ F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ordinary R F ≅ resolved R (single R (coefficients R)) F)
    {I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (j : single R (coefficients R) ⟶ I)
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ordinary R F ⟶ resolved R I F :=
  (e F).hom ≫ ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op (single R F))).map j
```

## Users

`tools/downstream.py Sheaf.Algebra.Homology.RationalTermHomComparison --uses
CategoryTheory.RationalTermHom.single` and the corresponding `zeroProjection`
query list one transitive importer, and textual uses only in the item itself.
The direct consumer has no Lean use of any `RationalTermHom` name (its proof plan
still cites the node), so its statement and construction retain their meaning.
It already privately imports `DerivedInternalHomOfUniverses` directly and does
not rely on either removed public import. No consumer adaptation is proposed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RationalTermHomComparison | F7 | Same single complexes, coefficients, Hom-complex objects, comparison and normalization; proved all original holes. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Only downstream importer; no textual use of the changed definitions; no signature or construction change. |

## Status

landed 20261020T221144-L-4150087 2026-10-20 (merge of deliver/F7/Sheaf.Algebra.Homology.RationalTermHomComparison)
