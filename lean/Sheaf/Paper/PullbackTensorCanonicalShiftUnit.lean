/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.KFlatTotalTensorModel

/-! # Canonical shifts and action units of derived tensor pullback

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 07A4;
more-algebra.tex, Tag 0FNH, item-shift-tensor; sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit).

The helper predicates spell out the normalizations in this node. All tensors,
representative comparisons, cochain unitors and pullback maps are existing ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.PullbackTensorCanonical

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] siteDerivedTensorIndependentCoefficients
attribute [local irreducible] representativeIso

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]


attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Normalization of the two derived tensor shifts by signed total-complex shifts.
The fixed-argument comparisons agree with the published resolving comparison.
`CommShift` includes the zero and addition laws, and `CommShift₂Int` includes
naturality in the other derived argument.
Source: Stacks 06YU and 0FNH
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
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


set_option genSizeOf false in
set_option genCtorIdx false in
set_option genInjectivity false in
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The action unitors, specified on flat-term K-flat representatives by the
ordinary cochain action maps. The ring complex is itself a resolving complex.
Source: Stacks 06YU and 03EL
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
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


variable (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  (k : Comparison.{r, uC, vC, uD, vD} f)
  (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))
  (epsilon : DerivedCategory.Q ⋙ L ⟶ pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q)

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The two derived bifunctors in the comparison.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
abbrev Phi := Functor.uncurry.obj (derivedTensor R) ⋙ L

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Pull back each input before taking the published derived tensor.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
abbrev Psi := (L.prod L) ⋙ Functor.uncurry.obj (derivedTensor S)


attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The Tag 07A4 representative square, in an equivalent form avoiding inverses
of computation maps. Its cochain comparison is the prescribed insertion-of-one map.
Source: Stacks 07A4
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit). -/
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


attribute [local irreducible] HasCanonicalTensorShifts IsNormalized

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Canonical derived pullback tensor comparison, coherent with both integer
shifts and both normalized tensor action units, for arbitrary ringed topoi.
The universal left-derived comparison is written on complexes rather than the
homotopy category; localization through homotopy identifies the two formulations.
No derived direct image, derived adjunction or projection mate is part of the data.
Source: Stacks 06YY, 07A4, 0FNH (item-shift-tensor), and 03EL
(blueprint: lem-weil-pbc-pullback-tensor-canonical-shift-unit).

Proof plan, following the node's eight steps:
1. Use lem-weil-pbc-site-derived-tensor-descent to test transformations on
   flat-term K-flat representatives. The computation epsilon is natural and
   invertible there by lem-weil-pbc-ringed-topoi-derived-pullback. Shifting a
   representative preserves the resolving class by the fixed-tensor lemma;
   termwise pullback has identity shift maps and differential (-1)^n f*(d).
2. Use lem-pur-kflat-total-tensor-model and the canonical tensor-pullback lemma
   to compute epsilon on the total tensor. Compose the representative maps in
   IsNormalized. Tensor descent extends these components uniquely, and detects
   their invertibility. Descend the ordinary action unitors in the same way.
3. The first-input chain shift square is unsigned: on each summand both
   composites send b tensor (x tensor y) to (b tensor x) tensor (1 tensor y).
4. The second-input square contributes (-1)^(np) on both sides, where p is
   the first input degree. Pullback is additive, so it preserves this sign.
   lem-pur-cochain-pullback-tensor-coherence supplies the chain comparison.
5. The identity termwise shift maps and the signed total shifts satisfy zero
   and addition laws (lem-weil-pbc-total-tensor-integer-shifts). Conjugation by
   computation maps preserves these laws, giving the stated CommShift data.
6. R[0] is K-flat with flat terms: tensoring with it is the identity. Its
   pullback unit sends b tensor a to b c(a), inverse b to b tensor 1.
   Compose its localization with epsilon to obtain the normalized u.
7. For the right action, b tensor (x tensor a) goes to
   (b tensor x) tensor (1 tensor a), then to b c(a) tensor x = b tensor ax.
   For the left action, b tensor (a tensor y) goes to b c(a) tensor y =
   b tensor ay. These are the pulled-back action maps; the degree-zero ring
   factor contributes no sign. Apply localization and computation comparisons.
8. Faithful restriction from tensor descent proves both shift squares and both
   action equations globally. Naturality holds for complex maps, then inverse
   quasi-isomorphisms by rearranging their squares, and all localized composites.
   No boundedness or flatness of the structural ring map is used.
-/
theorem pullback_tensor_canonical_shift_unit
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ))) :
    ∃ (_ : L.CommShift ℤ) (_ : (derivedTensor R).CommShift₂Int)
      (_ : (derivedTensor S).CommShift₂Int),
      NatTrans.CommShift epsilon ℤ ∧
      HasCanonicalTensorShifts (R := R) ∧ HasCanonicalTensorShifts (R := S) ∧
      (∀ (P : CochainComplex (Modules R) ℤ), P.IsKFlatIndependentCoefficients →
        (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) → IsIso (epsilon.app P)) ∧
      ∃ mu : Phi L ≅ Psi L,
        IsNormalized f k L epsilon mu.hom ∧
        (∀ tau : Phi L ⟶ Psi L, IsNormalized f k L epsilon tau → tau = mu.hom) ∧
        ∃ (aR : ActionUnits (R := R)) (aS : ActionUnits (R := S))
          (u : L.obj (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (Modules R) (.up ℤ))) ≅
            DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (Modules S) (.up ℤ))),
          Subsingleton (ActionUnits (R := R)) ∧ Subsingleton (ActionUnits (R := S)) ∧
          u.hom = epsilon.app (HomologicalComplex.tensorUnit (Modules R) (.up ℤ)) ≫
            DerivedCategory.Q.map
              (CategoryTheory.CochainPullback.unit.{r, uC, vC, uD, vD} f k).hom ∧
          (∀ (n : ℤ) (M N : DerivedCategory (Modules R)),
            mu.hom.app (M⟦n⟧, N) ≫
                ((derivedTensor S).map ((L.commShiftIso n).hom.app M)).app (L.obj N) ≫
                (((derivedTensor S).flip.obj (L.obj N)).commShiftIso n).hom.app (L.obj M) =
              L.map ((((derivedTensor R).flip.obj N).commShiftIso n).hom.app M) ≫
                (L.commShiftIso n).hom.app (((derivedTensor R).obj M).obj N) ≫
                (mu.hom.app (M, N))⟦n⟧') ∧
          (∀ (n : ℤ) (M N : DerivedCategory (Modules R)),
            mu.hom.app (M, N⟦n⟧) ≫
                ((derivedTensor S).obj (L.obj M)).map ((L.commShiftIso n).hom.app N) ≫
                (((derivedTensor S).obj (L.obj M)).commShiftIso n).hom.app (L.obj N) =
              L.map ((((derivedTensor R).obj M).commShiftIso n).hom.app N) ≫
                (L.commShiftIso n).hom.app (((derivedTensor R).obj M).obj N) ≫
                (mu.hom.app (M, N))⟦n⟧') ∧
          (∀ M : DerivedCategory (Modules R),
            mu.hom.app
                (M, DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (Modules R) (.up ℤ))) ≫
                ((derivedTensor S).obj (L.obj M)).map u.hom ≫ aS.rho.hom.app (L.obj M) =
              L.map (aR.rho.hom.app M)) ∧
          (∀ N : DerivedCategory (Modules R),
            mu.hom.app
                (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit (Modules R) (.up ℤ)), N) ≫
                ((derivedTensor S).map u.hom).app (L.obj N) ≫ aS.ell.hom.app (L.obj N) =
              L.map (aR.ell.hom.app N)) := by
  sorry


end SheafOfModules.PullbackTensorCanonical
