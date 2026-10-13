/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData

/-! # Hom complex comparison with specified product projections

Source: Stacks Project, Tags 0A8X and 08DL, Hom complexes and their differential.
(blueprint: lem-pc-hom-complex-over-equiv-projections). -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Assemble any natural termwise internal-Hom comparison through the specified
product projections, retaining both the differential and naturality in the target.
Source: Stacks Project, Tags 0A8X and 08DL.
(blueprint: lem-pc-hom-complex-over-equiv-projections).

Proof: the equivalence preserves each product fan. Postcompose its projections
with the given termwise isomorphisms and use uniqueness of product objects to
obtain a degreewise isomorphism. Its defining projection equation identifies the
two differential formulas by naturality of the termwise comparison, additivity,
and preservation of integer scalar multiplication. Assemble the degreewise maps
into a chain isomorphism. For naturality, postcompose in every degree with every
Hom projection, use the specified action of the Hom bifunctor, and apply the
termwise naturality equation. Product projections are jointly monic, so these
component equations imply equality. No boundedness or nonzero-open assumption is
used: the product fans and their universal properties apply to all complexes. -/
theorem exists_homComplex_overEquiv_projections (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} U.toScheme.ringCatSheaf)
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∀ (e : ∀ A B : localEvaluationModules X U,
        L.obj (SheafOfModules.homObj (R := X.sheaf.over U) A B) ≅
          SheafOfModules.homObj (R := U.toScheme.sheaf) (L.obj A) (L.obj B)),
      (∀ (A A' B B' : localEvaluationModules X U) (f : A' ⟶ A) (g : B ⟶ B'),
        L.map (SheafOfModules.homObjMap (R := X.sheaf.over U) f g) ≫
            (e A' B').hom =
          (e A B).hom ≫ SheafOfModules.homObjMap (R := U.toScheme.sheaf)
            (L.map f) (L.map g)) →
      ∃ b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
          T.obj (homComplex (R := X.sheaf.over U) P M) ≅
            homComplex (R := U.toScheme.sheaf) (T.obj P) (T.obj M),
        (∀ (M N : CochainComplex (localEvaluationModules X U) ℤ) (a : M ⟶ N),
          T.map (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map a) ≫
              (b N).hom =
            (b M).hom ≫ ((homComplexFunctor (R := U.toScheme.sheaf)).obj
              (op (T.obj P))).map (T.map a)) ∧
        (∀ (M : CochainComplex (localEvaluationModules X U) ℤ)
            (n r s : ℤ) (h : r + n = s),
          (b M).hom.f n ≫
              (Classical.choose (homComplex_projections_exists.{u, u, u, u}
                (R := U.toScheme.sheaf)))
                (T.obj P) (T.obj M) n r s h =
            L.map (localEvaluationProjection X U P M n r s h) ≫
              (e (P.X r) (M.X s)).hom) := by sorry

end AlgebraicGeometry
