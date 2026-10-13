/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Paper.DerivedInternalHomRestrictOpen

/-! # Compatible comparison isomorphisms for an ordinary evaluation map

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ, 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-evaluation-comparisons).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Given representatives and an ordinary evaluation chain map, there are compatible
source and target comparison isomorphisms. The comparisons are existentially
quantified; the square is not asserted for arbitrary isomorphisms.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of
lemma-dual-perfect-complex; Tag 08DM, lemma-Rhom-strictly-perfect;
Tag 08DL, lemma-restriction-RHom-to-U.
(blueprint: lem-pc-strictly-perfect-evaluation-comparisons).

Proof:
1. Restrict the derived Hom computation to U (08DL) and identify its arguments
   using eK and eN. Internal Hom from each term of P is exact because that term
   is a retract of a finite free sheaf. The finite stupid filtration of P shows
   Hom(P,-) preserves quasi-isomorphisms, so the map to Hom(P,I(F)) is a
   quasi-isomorphism. Its localization and the derived Hom factorization give b.
   This is the proof of 08DM on the localized ringed site; no affine assumption
   on U is necessary.
2. The same computation with the structure complex gives the ordinary dual
   Hom(P,O[0]) representing the restricted D. Its degree-q term is the dual of
   P^(-q). Dualizing the finite free retraction shows this is finite projective,
   hence flat. The dual is bounded, hence K-flat by the bounded-above flat
   theorem. Its total tensor with F therefore computes the derived tensor.
   Exact restriction and eN give the source comparison a. The tensor order
   agrees with F tensor Hom(P,O[0]); use symmetry if the K-flat factor is second.
3. Evaluate the representative equation of the fixed canonical tensor-Hom
   family into the K-injective resolution of F. After uncurrying on each
   tensor summand, the hypothesis hf is precisely evaluation of the dual
   element on P followed by the unit action on F. Naturality of evaluation
   makes this commute with F to I(F) and with the dual's resolution.
4. The representative equation thus identifies the localization of f with
   the adjunct of the associator, evaluation and right unitor. Transport it
   along eK and eN and the restriction comparison. With a and b from steps
   1 and 2 this is the displayed square. Product and coproduct extensionality
   justify the summand check. No invertibility of f is used.
   Empty U and zero P or F use zero objects and the same comparisons.
-/
theorem exists_strictlyPerfect_evaluation_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (_hstrict : Scheme.IsStrictlyPerfect X U P)
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
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  sorry

end AlgebraicGeometry
