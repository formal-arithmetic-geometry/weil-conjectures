/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.CategoryTheory.SheafPolynomialCotangentComparison
public import Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary
import Sheaf.CategoryTheory.YonedaDerivedExtComparison
import Sheaf.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Conormal representatives of sheaf cotangent Ext classes

Source: Stacks Project, Deformation Theory, Tag 08UJ,
lemma-NL-represent-ext-class-ringed-topoi
(blueprint: lem-sfb-sheaf-cotangent-ext-representative).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The positive quotient onto the degree minus one term, placed in degree -1,
then identified with its degree-zero embedding shifted by one.
Source: Stacks Project, Tags 0149 and 06XS(1)
(blueprint: lem-sfb-sheaf-cotangent-ext-representative). -/
def twoTermSupportedQuotient (K : CochainComplex A ℤ)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) :
    Q.obj K ⟶ ((singleFunctor A 0).obj (K.X (-1)))⟦(1 : ℤ)⟧ :=
  Q.map (HomologicalComplex.mkHomToSingle (j := (-1 : ℤ)) (𝟙 (K.X (-1)))
    (fun i hi ↦ (hK i (by have : i + 1 = -1 := hi; omega)
      (by have : i + 1 = -1 := hi; omega)).eq_of_src _ _)) ≫
      ((singleFunctors A).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app (K.X (-1))

/-- The same additive boundary `δ ↦ δ[1] ∘ q` on any complex supported in
`[-1,0]`. For the cone model this is the positive quotient used by
`twoTermBoundary`; it uses no projectivity or injectivity hypothesis.
Source: Stacks Project, Tags 0149 and 06XS(1)
(blueprint: lem-sfb-sheaf-cotangent-ext-representative). -/
def twoTermSupportedBoundary (K : CochainComplex A ℤ)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) (G : A) :
    (K.X (-1) ⟶ G) →+
      (Q.obj K ⟶ ((singleFunctor A 0).obj G)⟦(1 : ℤ)⟧) :=
  (Preadditive.leftComp _ (twoTermSupportedQuotient K hK)).comp
    (((shiftFunctor (DerivedCategory A) (1 : ℤ)).mapAddHom).comp
      (singleFunctor A 0).mapAddHom)

end DerivedCategory

namespace CategoryTheory.SheafPolynomialCotangent

/-- Every derived Ext-one class is a conormal map for a suitable sheaf-surjective
polynomial presentation. `D` supplies the canonically normalized comparison models
of the dependency, not an additional condition on the ring map or coefficient sheaf.

Source: Stacks Project, Deformation Theory, Tag 08UJ,
lemma-NL-represent-ext-class-ringed-topoi
(blueprint: lem-sfb-sheaf-cotangent-ext-representative).

Proof, following the five DAG steps:
1. Begin with the identity generators `E = B`. Evaluation is surjective since
   `b` is the image of `X b`. Put `x = ξ ∘ λ` and let `F` be the differential term.
   Polynomial differentials identify `F` with the free module sheaf on `E`.
2. The rotated cone triangle gives `F[0] → K → M[1]` with the positive quotient
   up to sign. Hom exactness, followed by full faithfulness in degree zero,
   identifies classes killing `F[0]` with boundaries of actual maps `M → G`.
   Absorb the possible cone sign into the map. The obstruction is `η = x|F[0]`.
3. Yoneda/derived Ext comparison represents `η` by `0 → G → H → F → 0`.
   Form `E' = E × |H|` over `|F|` using the differential generators. The module
   epimorphism is epic on abelian sheaves, so the general-site local-surjectivity
   lemma gives local lifts of every generator. Thus `A[E'] → B` is sheaf-surjective.
4. The second projection `E' → |H|` extends by the free-module universal property
   to `F' → H`, lifting `F' → F`. The pulled-back extension splits; naturality and
   the split-zero clause of Yoneda comparison give `η|F' = 0`.
5. The generator-induced chain map commutes with the degree-zero inclusions.
   Hence `x|K'` kills `F'[0]`, so step 2 supplies `δ` with `x|K' = ∂(δ)`.
   Naturality of the canonical comparisons gives `ξ ∘ λ_E' = ∂(δ)`.
   Compose with `λ_E'⁻¹` and rename `E'` to obtain the displayed equality.
-/
theorem sheaf_cotangent_ext_representative
    {C : Type u} [SmallCategory C] (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (A B : Sheaf J.toGrothendieck CommRingCat.{u}) (f : A ⟶ B) (D : Comparison f)
    (G : ringedSiteModules.{u} (siteModuleRings B))
    (ξ : (localization B).obj (D.models (canonical f)).complex ⟶
      ((localization B).obj ((CochainComplex.singleFunctor _ 0).obj G))⟦(1 : ℤ)⟧) :
    ∃ (P : Presentation f) (δ : (D.models P).complex.X (-1) ⟶ G),
      ξ = (D.lambda P).inv ≫
        @DerivedCategory.twoTermSupportedBoundary _ _ _ (HasDerivedCategory.standard _)
          (D.models P).complex (D.models P).supported G δ := by
  sorry

end CategoryTheory.SheafPolynomialCotangent
