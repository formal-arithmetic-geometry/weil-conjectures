/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryEvaluationData
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # The local representative equation for evaluation with an exact Hom source

Source: Stacks Project, Tags 08DL, 08DM and 08DQ, the ordinary complex models;
Tag 08DJ, the tensor-Hom representative equation.
(blueprint: lem-pc-exact-source-evaluation-local-comparisons).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The representative equation needs preservation of quasi-isomorphisms by Hom(P,-)
and K-flatness of its ordinary dual, rather than finite freeness or invertibility
of ordinary evaluation. The second complex is arbitrary.
Source: Stacks Project, Tags 08DL, 08DM and 08DQ, the ordinary complex models;
Tag 08DJ, the tensor-Hom representative equation.
(blueprint: lem-pc-exact-source-evaluation-local-comparisons).

Proof:
1. Resolve F and O[0] by the functorial K-injective resolution. The assumption
   hhom makes Hom(P,F) -> Hom(P,I(F)) and Hom(P,O[0]) -> Hom(P,I(O[0]))
   quasi-isomorphisms. The localization factorization of derived internal Hom,
   together with its open restriction comparison and eK,eN, therefore gives
   target and dual comparisons using the actual Hom complexes.
2. Since Hom(P,O[0]) is K-flat by hdual, its ordinary tensor with F computes
   the derived tensor, even if F is unbounded. Exact open restriction commutes
   with sheaf tensor and its total complex; transport this comparison through
   eN and the dual comparison of step 1. This constructs the source comparison
   a independently of any inverse of evaluation. The target comparison is b.
3. Replace the tensor inputs by K-flat resolutions and the final target by the
   same K-injective resolution used by the canonical tensor-Hom family. Its
   representative equation uncurries the adjunct defining g. On a tensor
   summand (p,q), followed by the r-th Hom projection, the result evaluates the
   dual on P^r and then acts on F^p by the unit when r+q=0; otherwise it is zero.
   The associator and symmetry restore the order F tensor Hom(P,O[0]). These
   are exactly the component equations hf. Naturality of evaluation makes the
   resolution maps commute with this calculation. Tensor inclusions and Hom
   product projections detect equality, so the representative chain maps agree.
   Localize and use the model comparisons to obtain the displayed square.
No inverse of f is used or asserted. Empty opens and zero complexes use the same
universal properties and zero maps; the hypotheses retain all unbounded F.
-/
theorem exists_exactSource_evaluation_local_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsKFlat)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by sorry

end AlgebraicGeometry
