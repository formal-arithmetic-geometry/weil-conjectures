# WeilConjectures.PointSignedCyclotomicAction data declarations

## Reason

The root-limit and signed-section sublemmas need the existing definitions without
importing the theorem that combines them. Move the existing data verbatim to
`Sheaf.Paper.PointSignedCyclotomicActionData`, publicly reexported by the original
module. This prevents an import cycle. This is an extraction for the reduction,
not a compile-time split. No definition body, type, declaration name, visibility,
coefficient convention or target meaning changes.

## Old

In `Sheaf.Paper.PointSignedCyclotomicAction`:

```lean
/-- The final site object of s = Spec k.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
abbrev point := Spec (CommRingCat.of D.k)

/-- The final object at which global sections are evaluated.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
abbrev finalObject : (point D).ProEt := ProEt.mk (𝟙 (point D))

/-- The canonical arrow from the final object into its base change. It is the
comma arrow followed by base change of restriction along g, with no chosen map.
Source: the restriction/coprojection formula in the node
(blueprint: lem-pur-point-signed-cyclotomic-action). -/
def sectionArrow : finalObject D ⟶
    (proEtaleBaseChange (frobeniusPointIso D).hom).obj (finalObject D) :=
  proEtaleIsoCommaArrow (frobeniusPointIso D).hom (finalObject D) ≫
    (proEtaleBaseChange (frobeniusPointIso D).hom).map (frobeniusPointRestriction D)

/-- Actual root-level restriction followed by the canonical inverse-image comparison.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
def rootAction (N : ℕ)
    (x : (proEtaleRootsOfUnitySheaf (point D) N).obj.obj (op (finalObject D))) :=
  (proEtaleRootsOfUnitySheaf (point D) N).obj.map (sectionArrow D).op
    ((proEtaleRootsOfUnityInverseImageMap (frobeniusPointIso D).hom N).hom.app
      (op ((proEtaleBaseChange (frobeniusPointIso D).hom).obj (finalObject D)))
      (((proEtaleSheafAdjunction (frobeniusPointIso D).hom AddCommGrpCat.{u + 1}).unit.app
        (proEtaleRootsOfUnitySheaf (point D) N)).hom.app (op (finalObject D)) x))

/-- The root section as an element of k, using the existing kernel and Spec identifications.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
def rootValue (N : ℕ)
    (x : (proEtaleRootsOfUnitySheaf (point D) N).obj.obj (op (finalObject D))) : D.k :=
  (ΓSpecIso (CommRingCat.of D.k)).hom.hom
    (proEtaleRootsOfUnitySections (point D) N (op (finalObject D)) x).toMul.val.val

/-- The inverse-limit root action, with precisely the published root-tower comparison.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
def rootLimitAction (x : (purTwistZlOne (point D) l).obj.obj (op (finalObject D))) :=
  (purTwistZlOne (point D) l).obj.map (sectionArrow D).op
    (FrobeniusCoefficientTwists.rootSection l (frobeniusPointIso D).hom (finalObject D) x)

/-- None denotes integral coefficients, and some n denotes A_(E,n+1).
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
abbrev coefficientRing (a : Option ℕ) : Sheaf (ProEt.topology (point D)) CommRingCat.{u + 1} :=
  match a with
  | none => (PurCompactSupport.completed l E).ring (point D)
  | some n => (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring (point D)

/-- The recorded signed sheaf line, at either of the two requested coefficients.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
abbrev line (a : Option ℕ) (m : ℤ) : SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology (point D))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficientRing D l E a)) :=
  match a with
  | none => FrobeniusCoefficientTwists.line l E (point D) m
  | some n => finiteCoefficientTwist l E (point D) n m

/-- Gamma(tau_m) after sigma, evaluated by the inverse-image unit and final-object
restriction. Naturality of tau identifies this formula with applying tau after restriction.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
def action (a : Option ℕ) (m : ℤ)
    (x : (line D l E a m).val.obj (op (finalObject D))) :
    (line D l E a m).val.obj (op (finalObject D)) :=
  match a with
  | none => (FrobeniusCoefficientTwists.line l E (point D) m).val.map (sectionArrow D).op
      ((FrobeniusCoefficientTwists.signedLineMaps l E (frobeniusPointIso D).hom m).hom.val.app
        (op ((proEtaleBaseChange (frobeniusPointIso D).hom).obj (finalObject D)))
        (FrobeniusCoefficientTwists.moduleSection l E (frobeniusPointIso D).hom
          (FrobeniusCoefficientTwists.line l E (point D) m) (finalObject D) x))
  | some n => (finiteCoefficientTwist l E (point D) n m).val.map (sectionArrow D).op
      ((FrobeniusCoefficientTwists.finiteSignedLineMaps l E
        (frobeniusPointIso D).hom n m).hom.val.app
        (op ((proEtaleBaseChange (frobeniusPointIso D).hom).obj (finalObject D)))
        (FrobeniusCoefficientTwists.finiteModuleSection l E (frobeniusPointIso D).hom n
          (finiteCoefficientTwist l E (point D) n m) (finalObject D) x))

/-- The pure root tensor e_B^(tensor d), including the coefficient unit at d=0.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
def generator (a : Option ℕ)
    (e : (purTwistZlOne (point D) l).obj.obj (op (finalObject D))) (d : ℕ) :
    (line D l E a (d : ℤ)).val.obj (op (finalObject D)) :=
  match a with
  | none => FrobeniusCoefficientTwists.generator l E (point D) (op (finalObject D)) 1 d
      (fun _ ↦ e)
  | some n => finiteTateProPowerGenerator l E n (point D) (op (finalObject D)) 1 d
      (fun _ ↦ e)

/-- The coefficient ring itself, with the harmless size lift used by the site.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
abbrev scalars (a : Option ℕ) : CommRingCat.{u + 1} :=
  match a with
  | none => CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
  | some n => CommRingCat.of (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1)))

/-- The actual constant-section map, completed by its quotient projections integrally.
Source: completed coefficient convention
(blueprint: lem-pur-point-signed-cyclotomic-action). -/
def scalarAt (a : Option ℕ) : scalars l E a →+*
    (coefficientRing D l E a).obj.obj (op (finalObject D)) :=
  match a with
  | none => pointIntegralSectionMap l E D.k
  | some n => pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1))

/-- Scalar multiplication through the specified coefficient section, without an extra
module structure on global sections.
Source: Deligne I (2.2) (blueprint: lem-pur-point-signed-cyclotomic-action). -/
def scale (a : Option ℕ) (m : ℤ) (b : scalars l E a)
    (x : (line D l E a m).val.obj (op (finalObject D))) :=
  scalarAt D l E a b • x

/-- Evaluation of the actual internal sheaf Hom on the identity slice.
Source: Deligne I (2.2), negative twists
(blueprint: lem-pur-point-signed-cyclotomic-action). -/
def evaluate (a : Option ℕ) (n : ℕ)
    (φ : (line D l E a (Int.negSucc n)).val.obj (op (finalObject D)))
    (x : (line D l E a ((n + 1 : ℕ) : ℤ)).val.obj (op (finalObject D))) :
    (coefficientRing D l E a).obj.obj (op (finalObject D)) :=
  match a with
  | none => φ.app (op (Over.mk (𝟙 (finalObject D)))) x
  | some _ => φ.app (op (Over.mk (𝟙 (finalObject D)))) x

/-- The pure tensor in the successor power of the existing line.
Source: Deligne I (2.2), positive twists
(blueprint: lem-pur-point-signed-cyclotomic-action). -/
def tensor (a : Option ℕ) (n : ℕ)
    (x : (line D l E a ((n + 1 : ℕ) : ℤ)).val.obj (op (finalObject D)))
    (y : (line D l E a 1).val.obj (op (finalObject D))) :
    (line D l E a ((n + 2 : ℕ) : ℤ)).val.obj (op (finalObject D)) :=
  match a with
  | none => SheafOfModules.siteSheafTensorTmul
      (FrobeniusCoefficientTwists.positiveLine l E (point D) (n + 1))
      (purTwistIntegralModule (point D) l E) (op (finalObject D)) x y
  | some j => SheafOfModules.siteSheafTensorTmul
      (coefficientTwistPower (point D) (purTwistFiniteOne (point D) l E j) (n + 1))
      (purTwistFiniteOne (point D) l E j) (op (finalObject D)) x y

/-- Restriction, inverse-image unit, and comparison on a constant coefficient factor.
Source: Deligne I (2.2), coefficient factors
(blueprint: lem-pur-point-signed-cyclotomic-action). -/
def constantAction (R : CommRingCat.{u + 1})
    (x : ((constantSheaf (ProEt.topology (point D)) CommRingCat.{u + 1}).obj R).obj.obj
      (op (finalObject D))) :=
  (((constantSheaf (ProEt.topology (point D)) CommRingCat.{u + 1}).obj R).obj.map
    (sectionArrow D).op)
    ((proEtaleConstantInverseImageMap (frobeniusPointIso D).hom CommRingCat.{u + 1} R).hom.app
      (op ((proEtaleBaseChange (frobeniusPointIso D).hom).obj (finalObject D)))
      (((proEtaleSheafAdjunction (frobeniusPointIso D).hom CommRingCat.{u + 1}).unit.app
        ((constantSheaf (ProEt.topology (point D)) CommRingCat.{u + 1}).obj R)).hom.app
          (op (finalObject D)) x))

```

## New

The declarations in the preceding block appear verbatim in
`Sheaf.Paper.PointSignedCyclotomicActionData`. The original module contains:

```lean
public import Sheaf.Paper.PointSignedCyclotomicActionData
```

The original public imports are retained in the original module. The data module
contains those same public prerequisites; proof imports stay in the theorem module.
The two new theorem modules publicly import the data module and the original module
imports the theorem modules privately. No downstream adaptation is required.

## Users

`python3 tools/downstream.py Sheaf.Paper.PointSignedCyclotomicAction --uses
WeilConjectures.PointSignedCyclotomicAction.action` reports zero downstream modules
and the original module itself as the sole textual user. The same module contains
all declarations being extracted. All other definition consumers were checked by
searching their fully qualified namespace; there is no external Lean consumer.
The parent DAG node retains its theorem attachment and all dependencies needed
for its unchanged statement. The sixteen data attachments move to the new definition
node `def-pur-point-cyclotomic-section-data`, recording their actual new module. There is no target declaration or definition repair.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointSignedCyclotomicAction | A3 | Same public interface through public data reexport; completed proof from sublemmas. |
| Sheaf.Paper.PointSignedCyclotomicActionData | A3 (new) | Existing definitions, unchanged. |
| Sheaf.Paper.PointRootLimitCyclotomicAction | A3 (new) | Uses root-tower definitions. |
| Sheaf.Paper.PointSignedCyclotomicScalar | A3 (new) | Uses signed-line and scalar definitions. |

## Status

landed 20261025T163532-L-691593 2026-10-25 (merge of deliver/A3/Sheaf.Paper.PointSignedCyclotomicAction)
