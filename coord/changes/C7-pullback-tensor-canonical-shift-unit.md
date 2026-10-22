# SheafOfModules.PullbackTensorCanonical.pullback_tensor_canonical_shift_unit

## Reason

Item: `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` (C7).

The main theorem was unproved. Its completed proof repeatedly unfolded the published derived
bifunctor, which is exported as reducible. A transparent presentation alias with a typed resolving
comparison keeps that existing data folded while checking the proof. The public shift hypotheses
and existential witnesses retain the original `derivedTensor` carrier. An identity conversion
uses the supplied shift structure for the alias, locally in this file; it adds no global instance.

The original theorem, helper predicates and action-unit structure retain their propositions and
constructions definitionally. All site and derived-category universes remain independent. No
adopted source-library file is changed. The definition presentation is submitted for review.

## Old

The following definitions are verbatim in their original section-variable context:

```lean
def HasCanonicalTensorShifts [(derivedTensor R).CommShift₂Int] : Prop :=
  ∀ (P : CochainComplex (Modules R) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (∃ cL : (totalTensor R).obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (derivedTensor R).obj (DerivedCategory.Q.obj P),
      NatTrans.CommShift cL.hom ℤ ∧
      ∀ (Q : CochainComplex (Modules R) ℤ) (hq : Q.IsKFlatIndependentCoefficients)
        (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        cL.app Q = representativeIso.{uC, vC, r, wR} R P Q hp hq hf hg) ∧
    (∃ cR : (totalTensor R).flip.obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (derivedTensor R).flip.obj (DerivedCategory.Q.obj P),
      NatTrans.CommShift cR.hom ℤ ∧
      ∀ (Q : CochainComplex (Modules R) ℤ) (hq : Q.IsKFlatIndependentCoefficients)
        (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        cR.app Q = representativeIso.{uC, vC, r, wR} R Q P hq hp hg hf)

structure ActionUnits where
  unit_kflat : CochainComplex.IsKFlatIndependentCoefficients
    (HomologicalComplex.tensorUnit (Modules R) (.up ℤ))
  unit_flat : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R)
    ((HomologicalComplex.tensorUnit (Modules R) (.up ℤ)).X n)
  rho : (derivedTensor R).flip.obj
    (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (Modules R) (.up ℤ))) ≅
      𝟭 (DerivedCategory (Modules R))
  ell : (derivedTensor R).obj
    (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (Modules R) (.up ℤ))) ≅
      𝟭 (DerivedCategory (Modules R))
  rho_normalized : ∀ (P : CochainComplex (Modules R) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (representativeIso.{uC, vC, r, wR} R P (HomologicalComplex.tensorUnit (Modules R) (.up ℤ))
      hp unit_kflat hf unit_flat).hom ≫
      rho.hom.app (DerivedCategory.Q.obj P) = DerivedCategory.Q.map
        (HomologicalComplex.rightUnitor P).hom
  ell_normalized : ∀ (P : CochainComplex (Modules R) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (representativeIso.{uC, vC, r, wR} R (HomologicalComplex.tensorUnit (Modules R) (.up ℤ)) P
      unit_kflat hp unit_flat hf).hom ≫
      ell.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (HomologicalComplex.leftUnitor P).hom

abbrev Phi := Functor.uncurry.obj (derivedTensor R) ⋙ L

abbrev Psi := (L.prod L) ⋙ Functor.uncurry.obj (derivedTensor S)

def IsNormalized (tau : Phi L ⟶ Psi L) : Prop :=
  ∀ (P Q : CochainComplex (Modules R) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    ∃ (hp' : CochainComplex.IsKFlatIndependentCoefficients
        ((pull.{r, uC, vC, uD, vD} f).obj P))
      (hq' : CochainComplex.IsKFlatIndependentCoefficients
        ((pull.{r, uC, vC, uD, vD} f).obj Q))
      (hf' : ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pull.{r, uC, vC, uD, vD} f).obj P).X n))
      (hg' : ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pull.{r, uC, vC, uD, vD} f).obj Q).X n)),
      L.map (representativeIso.{uC, vC, r, wR} R P Q hp hq hf hg).hom ≫
          tau.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (Functor.uncurry.obj (derivedTensor S)).map
            (Prod.mkHom (epsilon.app P) (epsilon.app Q)) =
        epsilon.app (((totalTensor R).obj P).obj Q) ≫
          DerivedCategory.Q.map (comparison.{r, uC, vC, uD, vD} f k P Q).hom ≫
          (representativeIso.{uD, vD, r, wS} S
            ((pull.{r, uC, vC, uD, vD} f).obj P) ((pull.{r, uC, vC, uD, vD} f).obj Q)
            hp' hq' hf' hg').hom
```

The original main proof was `by sorry`. Its two public wrapper imports were:

```lean
public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
```

## New

The following definitions are in the same independently sized context. `MR` and `MS` denote the
same module categories. `TR`/`TS` name `canonicalDerivedTensor` at the respective sites;
`DR`/`DS` retain the original `derivedTensor`; `tR₀`/`tS₀` remain the published `totalTensor`.
The presentation wrappers contain the original data.

```lean
variable (R) in
def canonicalDerivedTensor : DerivedCategory (MR) ⥤ DerivedCategory (MR) ⥤
    DerivedCategory (MR) := derivedTensor R

@[instance_reducible]
def canonicalDerivedTensorCommShift [(derivedTensor R).CommShift₂Int] :
    (canonicalDerivedTensor R).CommShift₂Int :=
  inferInstanceAs (derivedTensor R).CommShift₂Int

variable (R) in
def canonicalRepresentativeIso
    (P Q : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    DerivedCategory.Q.obj (((tR₀).obj P).obj Q) ≅
      ((TR).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q) :=
  representativeIso R P Q hp hq hf hg

def HasCanonicalTensorShifts [(DR).CommShift₂Int] : Prop :=
  ∀ (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (∃ cL : (tR₀).obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (TR).obj (DerivedCategory.Q.obj P),
      NatTrans.CommShift cL.hom ℤ ∧
      ∀ (Q : CochainComplex (MR) ℤ) (hq : Q.IsKFlatIndependentCoefficients)
        (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        cL.app Q = canonicalRepresentativeIso.{uC, vC, r, wR} R P Q hp hq hf hg) ∧
    (∃ cR : (tR₀).flip.obj P ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (TR).flip.obj (DerivedCategory.Q.obj P),
      NatTrans.CommShift cR.hom ℤ ∧
      ∀ (Q : CochainComplex (MR) ℤ) (hq : Q.IsKFlatIndependentCoefficients)
        (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        cR.app Q = canonicalRepresentativeIso.{uC, vC, r, wR} R Q P hq hp hg hf)

structure ActionUnits where
  unit_kflat : CochainComplex.IsKFlatIndependentCoefficients
    (HomologicalComplex.tensorUnit (MR) (.up ℤ))
  unit_flat : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R)
    ((HomologicalComplex.tensorUnit (MR) (.up ℤ)).X n)
  rho : (TR).flip.obj
    (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≅
      𝟭 (DerivedCategory (MR))
  ell : (TR).obj
    (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (MR) (.up ℤ))) ≅
      𝟭 (DerivedCategory (MR))
  rho_normalized : ∀ (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (canonicalRepresentativeIso.{uC, vC, r, wR} R P (HomologicalComplex.tensorUnit (MR) (.up ℤ))
      hp unit_kflat hf unit_flat).hom ≫
      rho.hom.app (DerivedCategory.Q.obj P) = DerivedCategory.Q.map
        (HomologicalComplex.rightUnitor P).hom
  ell_normalized : ∀ (P : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)),
    (canonicalRepresentativeIso.{uC, vC, r, wR} R (HomologicalComplex.tensorUnit (MR) (.up ℤ)) P
      unit_kflat hp unit_flat hf).hom ≫
      ell.hom.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (HomologicalComplex.leftUnitor P).hom

abbrev Phi := Functor.uncurry.obj (TR) ⋙ L

abbrev Psi := (L.prod L) ⋙ Functor.uncurry.obj (TS)

def IsNormalized (tau : Phi L ⟶ Psi L) : Prop :=
  ∀ (P Q : CochainComplex (MR) ℤ) (hp : P.IsKFlatIndependentCoefficients)
    (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    ∃ (hp' : CochainComplex.IsKFlatIndependentCoefficients
        ((pullF).obj P))
      (hq' : CochainComplex.IsKFlatIndependentCoefficients
        ((pullF).obj Q))
      (hf' : ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pullF).obj P).X n))
      (hg' : ∀ n : ℤ, IsFlatOnSite (J := K) (R := S) (((pullF).obj Q).X n)),
      L.map (canonicalRepresentativeIso.{uC, vC, r, wR} R P Q hp hq hf hg).hom ≫
          tau.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (Functor.uncurry.obj (TS)).map
            (Prod.mkHom (epsilon.app P) (epsilon.app Q)) =
        epsilon.app (((tR₀).obj P).obj Q) ≫
          DerivedCategory.Q.map (comparison.{r, uC, vC, uD, vD}
            (J := J) (K := K) (R := R) (S := S) f k P Q).hom ≫
          (canonicalRepresentativeIso.{uD, vD, r, wS} S
            ((pullF).obj P) ((pullF).obj Q)
            hp' hq' hf' hg').hom
```

The conversion is registered with `attribute [local instance] canonicalDerivedTensorCommShift`.
The presentation aliases are locally irreducible after proving the canonical shift existence API;
their public definitions remain transparent. No existing reducibility attribute is changed.
The conversion returns the input structure, so both signed comparisons and their laws are unchanged.

A temporary independent importer checks both normalization predicates against their original
definitions by `Iff.rfl`, transports every action-unit field in both directions, and checks equality
of the presentation and original derived tensors by `rfl`. The unchanged direct consumer is also
compiled against the packet. It needs no additional instance registration.

The two public wrapper imports are replaced by the directly required public import
`Mathlib.CategoryTheory.Functor.Derived.LeftDerived` and private proof imports. Both wrapper
modules remain in the library. New proved modules are:

- `Sheaf.Paper.PullbackTensorResolvingComputation`: computes the given universal counit on
  flat-term K-flat complexes, through homotopy and the universal left-derived criterion.
- `Sheaf.Paper.CochainPullbackTensorShift`: identifies the prescribed insertion-of-one comparison
  with the additive bifunctor comparison on each totalization summand and proves both signed shifts.

The retained proof constructs the normalized comparison by two-variable resolving descent,
proves uniqueness by fully faithful restriction, descends both cochain action unitors, proves their
uniqueness on resolving representatives, and verifies the two shift and two unit equations.
The ring complex is constructed by the existing cochain tensor-unit definition. The chosen derived
action units are determined uniquely by their representative normalization; the theorem proves
`Subsingleton ActionUnits`. No object is chosen from an undetermined unproved existence claim.

The action-unit and cochain-naturality proofs use the proved
`Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations` component API, imported privately,
rather than projecting these equations from the larger coherence theorem.

Performance controls seal existing tensor definitions locally during elaboration. The existing
signed-shift setup and the two fixed cochain shift instances are locally irreducible, preventing
repeated elaboration of their large total-complex data. The lower-level complex and bicomplex
mapping constructors are locally irreducible for the same reason. This changes no exported definition,
instance, attribute or statement. A proved private
resolving-existence lemma shares the flatness conversion, and abstract shift-equation lemmas avoid
re-elaborating the expanded sheaf tensor in the final assembly. Fully faithful resolving restriction
is packaged by a proved private theorem. The uncurrying comparison is constructed generically;
proved component equations expose only the components needed by normalization. The two comparison
constructors are locally irreducible after proving those equations. Private construction helpers
are marked `no_expose`; none occurs in a public definition or public signature.

The expensive multicospan sheaf-composition instance is excluded while this module elaborates
and restored at its original `high` priority before the end. Imported modules retain the original
instance.

Three proved private helpers factor repeated faithful-whiskering transport, normalized-square
cancellation, and fixed-shift transport through resolving models. They introduce no new assumptions.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.ExactPullbackSignedComparison` | X8 | No edit; compiled against the packet. |

This is the sole current direct consumer. No consumer signature changes or source-library edits
are made. Delivery checks repeat the consumer compilation. A temporary importer also checks the
restored sheaf-composition instance. No modules or DAG nodes are deleted. Parent and new nodes
record the actual proof dependencies. Final validation is recorded in report.md.

## Status

landed 20261022T013357-L-3556675 2026-10-22 (merge of deliver/C7/Sheaf.Paper.PullbackTensorCanonicalShiftUnit)
