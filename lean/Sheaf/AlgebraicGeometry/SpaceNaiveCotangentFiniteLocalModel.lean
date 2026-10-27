module

public import Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
import Sheaf.AlgebraicGeometry.AffineEtaleNaiveCotangentPresentation
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.RingTheory.KaehlerDifferentialsPolynomialExtension
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Finite two-term étale local models of the naive cotangent complex

Source: Stacks Project, More on Morphisms of Spaces, Tag 0D0Z, lemma-netherlander-fp
(blueprint: lem-sfb-space-naive-cotangent-finite-local-model).

We use the existing small affine ringed models of the small étale sites. Along an
étale chart, ordinary tensor pullback is exact restriction, so its termwise application
to the given naive cotangent complex followed by Q represents its derived restriction.
Finiteness and quasi-coherence are tested after the existing inverse basis equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An lfp algebraic-space morphism has étale local two-term quasi-coherent models,
with finite-type degree -1 and finitely presented degree 0, without Noetherianness.
Source: Stacks Project, Tag 0D0Z, lemma-netherlander-fp
(blueprint: lem-sfb-space-naive-cotangent-finite-local-model).

Proof:
1. Choose a surjective étale scheme atlas V of Y and an atlas W of X ×_Y V,
   using lem-trf-space-fibre-products-etale-covers. Compose scheme-test covers by
   lem-weil-pbc-etale-covering-composition. The chart-test hypothesis makes W → V
   locally of finite presentation. Refine by affine opens U_i = Spec B_i and
   V_i = Spec R_i so B_i = R_i[x_1,...,x_n]/(g_1,...,g_m). Open immersions are
   étale by lem-weil-pbc-open-immersion-etale, so these remain a covering of X
   and give commuting squares with étale vertical maps to X → Y.
2. lem-sfb-space-naive-cotangent-etale-localization identifies restricted NL with
   NL of each affine chart morphism. Apply lem-sfb-affine-etale-naive-cotangent-presentation
   to identify it in the derived category with [I/I² → B tensor_P Omega[P/R]].
3. The classes of the finitely many g_j generate I/I²: reduce the coefficients
   of an expression h = sum a_j g_j modulo I; changes of lifts lie in I².
   By lem-weil-pbc-kahler-differentials-polynomial-extension and Omega[R/R] = 0
   (def-weil-pbc-kahler-differentials), Omega[P/R] is free on dx_1,...,dx_n.
   Its base change is B^n, hence is finitely presented, with no relations.
4. lem-weil-pbc-spec-module-tilde-sections and
   lem-weil-pbc-quasi-coherent-finite-type-affine give the corresponding Zariski
   finiteness properties. Transfer them by
   lem-sfb-scheme-etale-module-exact-finiteness-comparison; quasi-coherence follows
   from lem-trf-scheme-zariski-etale-quasi-coherent-equivalence. Transport along
   the existing affine-basis module equivalence. The complex is zero outside -1,0.
   No kernel finiteness or Noetherian assumption occurs. -/
theorem naiveCotangent_finite_local_model
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hfp : MapIsLocallyOfFinitePresentation f) :
    ∃ (I : Type u) (U : I → Over S) (a : ∀ i : I, schemeSpace (U i) ⟶ X),
      (∀ i : I, IsEtale (a i).hom.hom) ∧
      IsJointlySurjective (fun i : I ↦ (a i).hom.hom) ∧
      ∀ (i : I) [HasDerivedCategory.{w} (schemeSpace (U i)).SmallModules],
        ∃ K : CochainComplex (schemeSpace (U i)).SmallModules ℤ,
          (∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (K.X n)) ∧
          ((schemeSpace (U i)).smallModuleEquivalence.inverse.obj (K.X (-1))).IsQuasicoherent ∧
          ((schemeSpace (U i)).smallModuleEquivalence.inverse.obj (K.X 0)).IsQuasicoherent ∧
          ((schemeSpace (U i)).smallModuleEquivalence.inverse.obj (K.X (-1))).IsFiniteType ∧
          ((schemeSpace (U i)).smallModuleEquivalence.inverse.obj (K.X 0)).IsFinitePresentation ∧
          Nonempty ((smallTensorPullbackComplex (a i)).obj (naiveCotangentComplex f) ≅
            DerivedCategory.Q.obj K) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
