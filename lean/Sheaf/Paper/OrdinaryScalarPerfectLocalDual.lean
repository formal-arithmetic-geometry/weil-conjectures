/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.FiniteConstantModelResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.Algebra.Ring.NegOnePow

/-! # Ordinary scalar models on the pro-etale site -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [∀ T : Scheme.{u}, (FiniteConstantModel.modelFunctor A T).Additive]

/-- A scalar-perfect local model computes the restriction of the derived coefficient dual.
Source: Stacks 08JH, 08JJ; blueprint internal-Hom stability proof, paragraph 2,
last sentence (blueprint: lem-sfb-ordinary-scalar-perfect-local-dual).

Proof: use the equivalence between internal abelian sheaf modules and sectionwise
modules over the associated ring sheaf. The constant scalar map and its extension
identify the transported model functor with scalar realization. Lift the finite
projective splittings to finite free sheaf splittings. The theorem
scalarPerfectDualRealization makes Hom from each term exact and identifies Hom into
a K-injective resolution with the ordinary Hom complex into the coefficient unit.
The evaluation comparison is an isomorphism on finite free modules and hence on
retracts. Its coordinates have differential -(-1)^i times precomposition by d_F;
the supplied coordinates identify this complex with G. Exact restriction to the
covering slice commutes with derived internal Hom, so transport the given model
isomorphism and then transport back through the equivalence of module categories.
This proves the formula on every original chart, with no refinement. Empty schemes,
zero modules and empty degree intervals are included by the same constructions. -/
theorem ordinaryScalarPerfect_local_dual
    (S : Scheme.{u})
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj A) S)))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (F G : 𝒰.I₀ → CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hbounded : ∀ i : 𝒰.I₀, ∃ a b : ℤ, ∀ q : ℤ,
      q < a ∨ b < q → IsZero ((F i).X q))
    (hprojective : ∀ (i : 𝒰.I₀) (q : ℤ), Module.Finite A ((F i).X q) ∧
      Module.Projective A ((F i).X q))
    (τ : ∀ (i : 𝒰.I₀) (q : ℤ),
      (G i).X q ≅ ModuleCat.of A (Module.Dual A ((F i).X (-q))))
    (hτ : ∀ (i : 𝒰.I₀) (q r : ℤ),
      (G i).d q r ≫ (τ i r).hom = (τ i q).hom ≫
        ModuleCat.ofHom (-q.negOnePow • ((F i).d (-r) (-q)).hom.dualMap))
    (hmodel : ∀ i : 𝒰.I₀, Nonempty
      (((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A)
        (𝒰.f i)).mapDerivedCategory).obj P ≅ DerivedCategory.Q.obj
          (((FiniteConstantModel.modelFunctor A (𝒰.X i)).mapHomologicalComplex
            (.up ℤ)).obj (F i)))) :
    ∀ i : 𝒰.I₀, Nonempty
      (((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A)
        (𝒰.f i)).mapDerivedCategory).obj
          (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj A) S).obj
            (op P)).obj (𝟙_ _)) ≅ DerivedCategory.Q.obj
              (((FiniteConstantModel.modelFunctor A (𝒰.X i)).mapHomologicalComplex
                (.up ℤ)).obj (G i))) := by
  sorry

end AlgebraicGeometry.ProEtale
