/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Monoidal
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees
import Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-! # Perfect-algebra coinduction is tensor with its algebra-valued dual

Source: Stacks Project, Dualizing Complexes, Tags 0BZE, 0A70 and 0A71
(blueprint: lem-trf-perfect-algebra-coinduction-tensor).
-/

@[expose] public section

universe u wR wB

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings TensorProduct

namespace ModuleCat

/-- Coextension is additive because it is a right adjoint and preserves binary products.
Source: Stacks Project, Tag 0A70 (blueprint: lem-trf-perfect-algebra-coinduction-tensor). -/
instance coextendScalars_additive {R B : Type u} [CommRing R] [CommRing B]
    (f : R →+* B) : (coextendScalars.{u, u, u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The complex `Hom_R(B,J)` with the coextension action `b • h = (b' ↦ h(b'b))`.
This is termwise application of Mathlib's coextension, without a new Hom construction.
Source: Stacks Project, Tag 0A71 (blueprint: lem-trf-perfect-algebra-coinduction-tensor). -/
noncomputable abbrev coinductionComplex {R B : Type u} [CommRing R] [CommRing B]
    (f : R →+* B) (J : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  ((coextendScalars f).mapHomologicalComplex (.up ℤ)).obj J

end ModuleCat

namespace DerivedCategory

variable {R B : Type u} [CommRing R] [CommRing B]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wB} (ModuleCat.{u} B)]

/-- Perfect-algebra coinduction is tensor with the algebra-valued dual, with its canonical
counit normalization. Source: Stacks Project, Tags 0BZE, 0A70 and 0A71
(blueprint: lem-trf-perfect-algebra-coinduction-tensor).

Here `J` is any K-injective resolution of `R[0]`, so `coinductionComplex f J` represents
`D_B = C_B(R[0])`. The functor `L`, with its left-derived comparison `ε`, is precisely
tensor with this second factor. The natural isomorphism has target the existing unbounded
right derived functor of coextension. Its adjunct is specified on every K-flat `F` by a
chain map `e` with formula `x ⊗ h ↦ x ⊗ h(1)`. The displayed formula includes the scalar
`b` in the extension presentation of the mixed tensor, so it determines `e` on every
coproduct summand. Composing with the inverse of `F ⊗ R[0] → F ⊗ J` and the right unitor
is exactly tensoring with the evaluation counit. Forgetting the B-action therefore gives
the ordinary perfect-complex evaluation comparison.

Proof:
1. The coinduction adjunction (lem-trf-derived-coinduction-adjunction) is the unbounded
derived adjunction of restriction and coextension. On K-injective representatives its
counit is evaluation at one. Use the existing upstream derived-adjunction construction.
2. Choose a K-flat representative F of an arbitrary unbounded input, using
lem-pc-kflat-resolution, and a K-injective resolution q: F ⊗ J → I. The mixed-tensor
left derived functor is supplied by lem-pc-derived-tensor-second-factor-functor.
3. Define t(x ⊗ h)(b) = q(x ⊗ h(b)). The action h(b'b) makes t B-linear. The signed
total differential commutes with t, and evaluation at one is q(x ⊗ h(1)), giving e
and the displayed adjunct equation.
4. Choose a bounded finite projective P representing B[0] by def-pc-perfect-ring-complex.
Use lem-pc-ring-derived-map-representative to realize it by a quasi-isomorphism P → B[0].
5. The normalized degreewise tensor-dual isomorphisms of
lem-pc-perfect-ring-hom-tensor-degrees commute with differentials by
lem-pc-perfect-ring-hom-tensor-differential. Their composite with symmetry is the evaluation
map F ⊗ Hom(P,J) → Hom(P,F ⊗ J); the two symmetry signs cancel to the input normalization.
6. Precomposition with P → B gives a commuting square with t on top and
Hom(P,q) after this evaluation on the bottom. Its vertical arrows are quasi-isomorphisms
by lem-pur-rhom-well-defined and K-flatness (def-pc-module-kflat-complex); its bottom is a
quasi-isomorphism by lem-pod-projective-hom-evaluation-model. Thus t is a quasi-isomorphism.
Restriction detects this, hence detects its derived isomorphism, by
lem-weil-pbc-unbounded-derived-iso-cohomology.
7. The adjunct description makes the comparison independent of resolutions and natural:
for an input morphism the two composites have the same tensor-counit adjunct. Only P
was bounded and finite projective; no flatness or Noetherian hypothesis was used. -/
theorem perfect_algebra_coinduction_tensor (f : R →+* B)
    (hB : IsPerfectRingComplex
      ((singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))))
    (J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective]
    (η : 𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ J) [QuasiIso η] :
    ∃ (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
      (ε : Q ⋙ L ⟶
        ((ModuleCat.mixedTensor f).flip.map₂CochainComplex).flip.obj
          (ModuleCat.coinductionComplex f J) ⋙ Q),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) ∧
      (∀ F : CochainComplex (ModuleCat.{u} R) ℤ,
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
          IsIso (ε.app F)) ∧
      ∃ θ : L ≅ (ModuleCat.coextendScalars f).rightDerivedFunctor,
        ∀ F : CochainComplex (ModuleCat.{u} R) ℤ,
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
          ∃ (s : Q.obj F ≅ Q.obj (F ⊗ J)),
            s.hom = Q.map (ρ_ F).inv ≫ Q.map (F ◁ η) ∧
          ∃ e : ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
              ((((ModuleCat.mixedTensor f).flip.map₂CochainComplex).obj F).obj
                (ModuleCat.coinductionComplex f J)) ⟶ F ⊗ J,
            (∀ (p q n : ℤ) (hpq : p + q = n) (x : F.X p)
              (h : (ModuleCat.coinductionComplex f J).X q) (b : B),
              (e.f n).hom
                ((HomologicalComplex.ιMapBifunctor F (ModuleCat.coinductionComplex f J)
                  (ModuleCat.mixedTensor f).flip (.up ℤ) p q n hpq).hom
                    (h ⊗ₜ[B] (b ⊗ₜ[R, f] x))) =
                (HomologicalComplex.ιTensorObj F J p q n hpq).hom
                  (x ⊗ₜ[R] (ModuleCat.CoextendScalars.equiv f (J.X q) h b))) ∧
            (ModuleCat.restrictScalars f).mapDerivedCategory.map (θ.hom.app (Q.obj F)) ≫
                (Adjunction.mapDerivedCategoryRightDerivedAdjunction
                  (ModuleCat.restrictCoextendScalarsAdj f)).counit.app (Q.obj F) =
              (ModuleCat.restrictScalars f).mapDerivedCategory.map (ε.app F) ≫
                (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app _ ≫
                Q.map e ≫ s.inv := by
  sorry

end DerivedCategory
