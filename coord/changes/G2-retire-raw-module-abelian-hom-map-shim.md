# AlgebraicGeometry.Etale.rawModuleAbelianHomMap and its canonical formula chain

## Reason

Complete the duplicate retirement listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap. P2's reviewed migration already
moved its definition to the canonical upstream module, leaving a reexport shim.
Its only four importers form an otherwise unused chain of duplicate formula
modules, each also listed for retirement and currently unclaimed. Retire the
whole chain in one packet and point its four remaining DAG attachments to the
existing canonical upstream theorems. This retains the actual mathematical
construction, every formula, every parent dependency and the unit route.

The direct-import migration first tested in scratch exposed the existing cost
of checking raw native-view equations. A low-heartbeat profiler localized the
cost to kernel checking of rawModuleScalarHom_evaluate, rather than its proof
elaboration (299 ms). The exact canonical formula is already proved upstream.
Reusing the canonical proved declarations removes the duplicate equation checks
and the otherwise unused shim, with no new construction or proof obligation.
No file under lean/WeilConjectures is edited, removed or weakened.

## Old

### RawModuleAbelianHomMap

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! The canonical upstream construction and the historical scalar-forgetting API.
The definitions are unchanged after unfolding the compatibility abbreviation.
(blueprint: def-sbc-raw-module-abelian-hom-map). -/

@[expose] public section
```

### RawModuleScalarHomEvaluation

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups M2 and N4
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import Sheaf.AlgebraicGeometry.RawModuleScalarClassMorphisms
public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap

/-! # Concrete formulas for raw scalar comparison
Source: Stacks Project, Tags 03FD, 03Q8 and 03D7.
(blueprint: lem-sbc-raw-scalar-hom-evaluation).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local instance] moduleSheafCategory moduleSheafPreadditive moduleSheafAbelian
  moduleSheafHasDerivedCategory

/-- Evaluation of the explicit additive scalar Hom map.
Source: Stacks Project, Tags 03FD and 03Q8, formula-expansion step of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-hom-evaluation).

Proof: Expand the definition of rawModuleAbelianHomMap. Its additive map is the composite of
derived forgetting, right composition by the coefficient factor, and left composition by the
source factor. Evaluation of AddCommGrpCat.ofHom and of the two additive compositions therefore
gives c composed with V(z) composed with b. The two named factor definitions have exactly these
source and coefficient bodies. No naturality or coherence equation is used. This applies to zero
classes, zero sheaves, identity geometric maps and degree zero. -/
theorem rawModuleScalarHom_evaluate
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A : Over W)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A)) :
    rawAbelianClassMorphism (A.hom ≫ k)
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
      (rawModuleAbelianHomMap Λ k G q U A z) =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (rawModuleClassMorphism Λ k G (q : ℤ) U A z) ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ) := by
  rfl

end AlgebraicGeometry.Etale
```

### RawModuleScalarHomCompositeFormula

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import Sheaf.AlgebraicGeometry.RawModuleScalarClassMorphisms
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientNative
import Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation
import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas

/-! # The bundled scalar Hom composite

Source: Stacks Project, Tags 03FD and 03Q8, the explicit scalar map.
(blueprint: lem-sbc-raw-module-scalar-hom-composite-formula).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem map_three_factors
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z T : C} {P Q : D}
    (c : P ⟶ F.obj X) (b : F.obj T ⟶ Q)
    (m : X ⟶ Y) (z : Y ⟶ Z) (t : Z ⟶ T) (x : X ⟶ T)
    (h : x = m ≫ z ≫ t) :
    c ≫ F.map x ≫ b = c ≫ F.map m ≫ F.map z ≫ F.map t ≫ b := by
  rw [h, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency true in
/-- Expand the scalar map on a raw module pullback, retaining all module factors.
Source: Stacks Project, Tags 03FD and 03Q8, raw-map expansion.
(blueprint: lem-sbc-raw-module-scalar-hom-composite-formula).

Proof: Evaluate rawModuleAbelianHomMap as its defining additive composite:
derived scalar forgetting on Hom groups, right composition by its coefficient
morphism b, and left composition by its source morphism c. The definitions of
scalarCoefficientFactor and scalarSourceFactor identify b and c with the displayed
factors. Apply rawModuleScalar_pullback_module_formula to the raw pullback input,
inside the derived scalar-forgetting map. This replaces that input with the
module source factor, the derived module inverse image of z, and the module
coefficient factor. Distribute scalar forgetting by Functor.map_comp,
but do not use either scalar source coherence or inverse-comparison naturality.
The equality holds for zero classes, q = 0, identity f, and zero coefficients.
-/
theorem rawModuleScalar_hom_composite_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawAbelianClassMorphism (A.hom ≫ k)
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
      (rawModuleAbelianHomMap Λ k G q U A
        ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z)) =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map
          (rawModuleClassMorphism Λ k G (q : ℤ) U B z)) ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleCoefficientFactorNative Λ G (q : ℤ) A B f) ≫
      scalarCoefficientFactor Λ A.hom G (q : ℤ) := by
  rw [rawModuleScalarHom_evaluate]
  apply map_three_factors
  exact (rawModuleScalar_pullback_formulas Λ k G q U A B f z).1

end AlgebraicGeometry.Etale
```

### RawModuleAbelianHomSourceFormula

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import Sheaf.AlgebraicGeometry.RawModuleScalarClassMorphisms
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientNative
import Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula
import Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula

/-! # The source and class factors of the raw scalar comparison

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-module-abelian-hom-source-formula).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Expand the module pullback and commute only its source and class factors.
The coefficient comparison is deliberately retained as the module coefficient tail.
Source: Stacks Project, Tags 03D7 and 03Q8, source-generator part of the scalar
naturality calculation.
(blueprint: lem-sbc-raw-module-abelian-hom-source-formula).

Proof: Evaluate the additive composite defining rawModuleAbelianHomMap. Use the module
raw pullback formula to expose its source, class and coefficient factors. Functoriality of
scalar forgetting separates these factors. Apply the underived scalar sheaf-composition
square to the free represented module sheaf and its free abelian generator map. Naturality
of upperStarComp moves this generator map across the comparison. Apply singleFunctor to
this sheaf square and use plus_single_source_square_core to identify the inverse derived
scalar comparison. This moves the source factor past scalar forgetting. Naturality of the
inverse derived comparison on z moves z past that comparison. Reassociate, leaving the
inverse comparison at the shifted coefficient, the forgotten module coefficient factor,
and the scalar coefficient factor untouched. No coefficient square or abelian raw pullback
is used. The argument covers zero classes, zero or empty sheaves, degree zero and identity
arrows; neither invertibility of the scalar Hom map nor acyclicity is assumed. -/
theorem rawModuleAbelianHomMap_source_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawAbelianClassMorphism (A.hom ≫ k)
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
      (rawModuleAbelianHomMap Λ k G q U A
        ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z)) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      ((RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
          (((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦(q : ℤ)⟧) ≫
        (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
          (moduleCoefficientFactorNative Λ G (q : ℤ) A B f) ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ)) := by
  have hs := rawModuleScalar_source_class_formula Λ k G q U A B f z
  have ht := congrArg
    (fun v ↦ v ≫
      (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus.map
        (moduleCoefficientFactorNative Λ G (q : ℤ) A B f) ≫
      scalarCoefficientFactor Λ A.hom G (q : ℤ)) hs
  have he := rawModuleScalar_hom_composite_formula Λ k G q U A B f z
  apply he.trans
  simpa only [rawModuleClassMorphism, Category.assoc] using ht

end AlgebraicGeometry.Etale
```

### RawModuleAbelianHomTargetFormula

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import Sheaf.AlgebraicGeometry.RawModuleScalarClassMorphisms
import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula
import Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation

/-! # Abelian expansion of the scalar raw Hom map

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-module-abelian-hom-target-formula).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Expand the abelian raw pullback and only the source-side scalar map.
Source: Stacks Project, Tags 03FD and 03Q8, explicit pullback factor expansion.
(blueprint: lem-sbc-raw-module-abelian-hom-target-formula).

Proof: Apply rawModuleScalar_pullback_abelian_formula to the input
rawModuleAbelianHomMap evaluated on z. Expand the additive scalar map as derived forgetting
followed by right composition with scalarCoefficientFactor and left composition with
scalarSourceFactor. Apply Functor.map_comp to separate the scalar coefficient factor from
the source factor and the forgotten class. Reassociate the morphisms: the leading abelian
source comparison and the image of the source factor composed with the class are exactly
rawModuleScalarSourcePrefix; the final two morphisms are the image of the scalar coefficient
factor and abelianCoefficientFactor. This argument uses only the definitions, functoriality
and associativity. It uses neither the source coherence square nor the coefficient coherence
square, and assumes no invertibility of the scalar Hom map. Zero and identity morphisms,
empty test objects and q = 0 satisfy the same formula. -/
theorem rawModuleAbelianHomMap_target_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawAbelianClassMorphism (A.hom ≫ k)
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
      (abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) q _ _
      ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
        (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G))
      U (rawModuleAbelianHomMap Λ k G q U B z)) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
          (scalarCoefficientFactor Λ B.hom G (q : ℤ)) ≫
        abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
          (q : ℤ) A B f) := by
  refine (rawModuleScalar_pullback_abelian_formula Λ k G q U A B f _).trans ?_
  rw [rawModuleScalarHom_evaluate]
  dsimp only [rawModuleScalarSourcePrefix]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
```

## New

All five listed Sheaf files are withdrawn through deleted.txt and land as:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The definition node def-sbc-raw-module-abelian-hom-map already names
WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap and is unchanged.
The four formula nodes now name the identical fully qualified declaration in
the corresponding WeilConjectures.AlgebraicGeometry module. Each lean.statement
is copied verbatim from that existing source declaration; existing is true.

| DAG node | canonical module suffix | preserved declaration suffix |
| --- | --- | --- |
| lem-sbc-raw-scalar-hom-evaluation | RawModuleScalarHomEvaluation | rawModuleScalarHom_evaluate |
| lem-sbc-raw-module-scalar-hom-composite-formula | RawModuleScalarHomCompositeFormula | rawModuleScalar_hom_composite_formula |
| lem-sbc-raw-module-abelian-hom-source-formula | RawModuleAbelianHomSourceFormula | rawModuleAbelianHomMap_source_formula |
| lem-sbc-raw-module-abelian-hom-target-formula | RawModuleAbelianHomTargetFormula | rawModuleAbelianHomMap_target_formula |

The mathematical statements and hypotheses are identical after unfolding the
following existing definitions. rawModuleClassMorphism and rawAbelianClassMorphism
return their input. RawModuleScalarComparison.forget abbreviates
moduleAbelianForget. moduleCoefficientFactorNative abbreviates
moduleCoefficientFactor. RawModuleScalarComparison.derivedPullbackIso has inv
field equal to moduleAbelianDerivedUpperStarIso.hom. Thus the old native-view
presentations are the canonical equations at definitionally equal endpoints.
All ring, scheme, sheaf, Over-arrow, degree and class binders are preserved.
No nonzero, nonempty, acyclicity or invertibility hypothesis is added.

The four proof records follow the canonical proofs. Their native-view identity
presentation is no longer a proof dependency. The composite proof uses
rawModuleScalar_pullback_module_formula directly instead of extracting the
module half of rawModuleScalar_pullback_formulas. Both give the same three
module factors. Evaluation, source and target calculations keep their existing
categorical arguments. No mathematical statement, stmt_deps, statement_change,
unit, chapter, source or review metadata is edited.

## Users

All four item importers are exactly the four formula modules being withdrawn.
The formula modules have no external live or quarantined importer. Their only
internal import edges are evaluation to composite/target, and composite to
source. No importer adaptation outside this chain is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap | G2 | Withdraw redundant canonical-construction reexport; definition node already upstream. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Withdraw duplicate theorem; its node now names the existing canonical formula. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Withdraw duplicate theorem; its node now names the canonical composite formula. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Withdraw duplicate theorem; its node now names the canonical source formula. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Withdraw duplicate theorem; its node now names the canonical target formula. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap | unclaimed | Canonical construction remains unchanged. |
| WeilConjectures.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Existing formula and full proof remain unchanged. |
| WeilConjectures.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Already imports and uses canonical evaluation; no source edit. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Already imports and uses canonical composite; no source edit. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Already imports and uses canonical evaluation; no source edit. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapNaturality | unclaimed | Existing parent imports and uses canonical source and target formulas; no source edit. |

The full source scan, including quarantine, found no other import site. The
separate coord/rework.tsv audit checked all 56 present quarantine archives and
found no archived importer of any withdrawn module. No unit realizes any of
the four migrated theorem nodes or the original definition node.
The definition node has ten mathematical citers, all preserved. The migrated
formula nodes still exist and retain all incoming DAG dependencies; only their
Lean locations and proof records change. The canonical upstream declarations
are the actual replacement arguments, with their existing complete proofs.
Target statements and meanings are unchanged; no target-definition re-review
is opened by moving duplicate-node attachments to the same constructions.

## Status

landed 20261025T060830-L-2376591 2026-10-25 (merge of deliver/G2/Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap)
