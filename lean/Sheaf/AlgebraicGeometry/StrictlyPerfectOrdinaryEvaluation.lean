/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Ordinary evaluation for a strictly perfect complex

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ and 08DM.
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation).
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

local instance localEvaluationPreadditive {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  Classical.choice (SheafOfModules.tensorClosed R).1

/-- The existing module category on the localized site, written in the carrier form
used by internal Hom. This is an abbreviation, not a different module category.
Source: Stacks Project, Tag 08DL
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
abbrev localEvaluationModules (X : Scheme.{u}) (U : X.Opens) :=
  SheafOfModules.{u} ((sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))

/-- The structure sheaf in degree zero on the localized site.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationUnit (X : Scheme.{u}) (U : X.Opens) :
    CochainComplex (localEvaluationModules X U) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ (localEvaluationModules X U))

/-- The ordinary Hom dual, with its actual Hom-complex differential.
Source: Stacks Project, Tag 08DM
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationDual (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :=
  homComplex (R := X.sheaf.over U) P (localEvaluationUnit X U)

/-- The total tensor with the ordinary Hom dual.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationTensor (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) :=
  CochainComplex.mapBifunctor F (localEvaluationDual X U P) (curriedTensor _)

/-- The specified product projection of the recorded Hom complex.
Source: Stacks Project, Tag 08DM
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationProjection (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (n r s : ℤ) (h : r + n = s) :
    (homComplex (R := X.sheaf.over U) P F).X n ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X s) :=
  (Classical.choose (Classical.choose_spec
    (homComplex_exists (R := X.sheaf.over U)))) P F n r s h

/-- The ordinary evaluation on a tensor summand, followed by a Hom projection.
It is zero unless the dual degree cancels the input degree; otherwise it sends
`y tensor phi` to `x ↦ y * phi(x)`, using the unit action on the second module.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def localEvaluationComponent (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (p q n r : ℤ) (hpq : p + q = n) :
    F.X p ⊗ (localEvaluationDual X U P).X q ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X (r + n)) :=
  if h : r + q = 0 then
    SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _ _
      ((β_ (P.X r) (F.X p ⊗ (localEvaluationDual X U P).X q)).hom ≫
        (α_ (F.X p) ((localEvaluationDual X U P).X q) (P.X r)).hom ≫
        F.X p ◁ ((β_ ((localEvaluationDual X U P).X q) (P.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _
            (𝟙_ (localEvaluationModules X U))).symm
            (localEvaluationProjection X U P (localEvaluationUnit X U) q r 0 h ≫
              SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                  (𝟙_ (localEvaluationModules X U))).hom)) ≫
        (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = r + n)).hom)
  else 0

/-- A chain map has the actual ordinary evaluation formula, with the tensor ordered
as `F tensor Hom(P,O[0])`. This predicate specifies maps, not just objects.
Source: Stacks Project, Tag 08DQ
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation). -/
def IsLocalOrdinaryEvaluation (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F) : Prop :=
  ∀ (p q n r : ℤ) (h : p + q = n),
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n h ≫ f.f n ≫
      localEvaluationProjection X U P F n r (r + n) rfl =
        localEvaluationComponent X U P F p q n r h

/-- Ordinary evaluation is degreewise invertible for a strictly perfect first input.
There is no bound on the second complex and the open need not be affine.
Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of Lemma 20.50.5,
and Tag 08DM, proof of Lemma 20.46.9.
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation).

Proof: in degree q, the dual Hom complex has just the possibly nonzero factor
Hom(P^(-q),O); all other target terms of O[0] are zero. The bounded support of P
makes the tensor summands in any total degree finite. The Hom complex on the
right likewise has finitely many possibly nonzero factors. Under these product
and coproduct identifications, the specified formula is the sum of the maps
F^p tensor Hom(P^(-q),O) to Hom(P^(-q),F^p), with p+q=n. For a finite free
module this is the identity on finitely many copies of F^p, by evaluation on
basis sections. A retraction of P^(-q) from a finite free module gives a
retraction of this comparison; naturality restricts the inverse to that
retraction. Thus each block, and hence every degree map, is invertible.
The argument also covers rank zero, P=0, empty U, and unbounded F. -/
theorem isIso_localOrdinaryEvaluation_degree (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) (n : ℤ) : IsIso (f.f n) := by sorry

end AlgebraicGeometry
