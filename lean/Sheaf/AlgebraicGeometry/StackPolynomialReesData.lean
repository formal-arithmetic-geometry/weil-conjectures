/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.AlgebraicGeometry.StackScalarAlgebra
public import Sheaf.AlgebraicGeometry.StackFlatScalarSections
public import Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.DirectSum.Basic

/-! # Polynomial and Rees comparison data on an algebraic stack

Source: Alper, Adequate moduli spaces, Lemmas 4.1.8 and 5.2.1, pp.503 and 507
(blueprint: def-sfb-stack-polynomial-rees-data).

These are records of specified comparisons, not chosen algebra constructions.
Rees inclusions are tested on smooth affine charts and on global sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits Opposite
open scoped DirectSum

namespace CategoryTheory

variable {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
variable {hF : IsFibredInGroupoids F}

/-- Evaluation of a compatible ring section. Source: Stacks 06W6 and Alper 5.2.1
(blueprint: def-sfb-stack-polynomial-rees-data). -/
def moduliRingSectionEval
    (A : Sheaf (moduliFppfTopology F) CommRingCat.{max (u + 1) v w}) (x : F.obj) :
    moduliGlobalSectionsRing A →+* A.obj.obj (op x) where
  toFun s := s.1 (op x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A module section mapped into an algebra is a compatible ring section.
Source: Stacks 06W6 and Alper 5.2.1
(blueprint: def-sfb-stack-polynomial-rees-data). -/
def moduliModuleSectionInAlgebra {M : SheafOfModules.{max (u + 1) v w}
      (moduliModuleRings F hF)} (B : ModuliAlgebraSheaf F hF)
    (f : M ⟶ moduliAlgebraModule B) (s : M.sections) :
    moduliGlobalSectionsRing B.right :=
  ⟨(SheafOfModules.sectionsMap f s).1, (SheafOfModules.sectionsMap f s).2⟩

/-- The object of the total category singled out by the identity of a scheme chart.
Source: Stacks 003T, Yoneda; Alper 5.2.1
(blueprint: def-sfb-stack-polynomial-rees-data). -/
abbrev moduliPolynomialChartObject {T : Over S}
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) F) : F.obj :=
  t.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T)))

/-- An object representing a smooth scheme test. The definition reuses the existing
smooth-test predicate and retains isomorphisms in the actual total category.
Source: Alper, Section 2 and proof of Lemma 5.2.1
(blueprint: def-sfb-stack-polynomial-rees-data). -/
def IsSmoothModuliPolynomialObject (x : F.obj) : Prop :=
  ∃ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
    IsSmoothModuliSchemeTest t ∧ Nonempty (x ≅ moduliPolynomialChartObject t)

/-- A polynomial-algebra system with its coefficient and variable normalizations,
coefficientwise global comparison and natural maps preserving sheaf surjections.
Polynomial identifications are required on precisely the smooth affine scheme charts.
Source: Alper, proof of Lemmas 4.1.8 and 5.2.1
(blueprint: def-sfb-stack-polynomial-rees-data). -/
structure ModuliPolynomialSystem (F : BasedCategory.{v, w} (Over S))
    (hF : IsFibredInGroupoids F) (L : Type (max (u + 1) v w)) where
  /-- The polynomial algebra over each quasi-coherent coefficient algebra. -/
  algebra (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B) :
    ModuliAlgebraSheaf F hF
  /-- Its underlying module is quasi-coherent. -/
  quasicoherent (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B) :
    IsQuasicoherentModuliAlgebra (algebra B hB)
  /-- The coefficient inclusion. -/
  constant (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B) :
    B ⟶ algebra B hB
  /-- The globally specified variables. -/
  generator (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B) :
    L → moduliGlobalSectionsRing (algebra B hB).right
  /-- Comparison on affine scheme tests, using the existing scheme restriction. -/
  chart (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B)
      (x : F.obj) (hx : IsAffine ((moduliSchemeForget F).obj x))
      (hs : IsSmoothModuliPolynomialObject x) :
    (algebra B hB).right.obj.obj (op x) ≃+* MvPolynomial L (B.right.obj.obj (op x))
  /-- Constants are ordinary polynomial constants. -/
  chart_constant (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B)
      (x : F.obj) (hx : IsAffine ((moduliSchemeForget F).obj x))
      (hs : IsSmoothModuliPolynomialObject x)
      (b : B.right.obj.obj (op x)) :
    chart B hB x hx hs ((constant B hB).right.hom.app (op x) b) = MvPolynomial.C b
  /-- Variables are the ordinary polynomial variables. -/
  chart_variable (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B)
      (x : F.obj) (hx : IsAffine ((moduliSchemeForget F).obj x))
      (hs : IsSmoothModuliPolynomialObject x) (l : L) :
    chart B hB x hx hs ((generator B hB l).1 (op x)) = MvPolynomial.X l
  /-- The coefficientwise global algebra isomorphism. -/
  sectionsEquiv (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B) :
    MvPolynomial L (moduliGlobalSectionsRing B.right) ≃+*
      moduliGlobalSectionsRing (algebra B hB).right
  /-- Its formula on every affine chart fixes the actual coefficientwise map. -/
  global_chart (B : ModuliAlgebraSheaf F hF) (hB : IsQuasicoherentModuliAlgebra B)
      (x : F.obj) (hx : IsAffine ((moduliSchemeForget F).obj x))
      (hs : IsSmoothModuliPolynomialObject x)
      (s : MvPolynomial L (moduliGlobalSectionsRing B.right)) :
    chart B hB x hx hs ((sectionsEquiv B hB s).1 (op x)) =
      MvPolynomial.map (moduliRingSectionEval B.right x) s
  /-- The map induced by a coefficient homomorphism. -/
  map {B B' : ModuliAlgebraSheaf F hF}
      (hB : IsQuasicoherentModuliAlgebra B) (hB' : IsQuasicoherentModuliAlgebra B')
      (f : B ⟶ B') : algebra B hB ⟶ algebra B' hB'
  /-- Its affine-chart formula is coefficientwise. -/
  map_chart {B B' : ModuliAlgebraSheaf F hF}
      (hB : IsQuasicoherentModuliAlgebra B) (hB' : IsQuasicoherentModuliAlgebra B')
      (f : B ⟶ B') (x : F.obj) (hx : IsAffine ((moduliSchemeForget F).obj x))
      (hs : IsSmoothModuliPolynomialObject x)
      (s : (algebra B hB).right.obj.obj (op x)) :
    chart B' hB' x hx hs ((map hB hB' f).right.hom.app (op x) s) =
      MvPolynomial.map (f.right.hom.app (op x)).hom (chart B hB x hx hs s)
  /-- Naturality of the global comparison for every coefficient map. -/
  global_naturality {B B' : ModuliAlgebraSheaf F hF}
      (hB : IsQuasicoherentModuliAlgebra B) (hB' : IsQuasicoherentModuliAlgebra B')
      (f : B ⟶ B') (s : MvPolynomial L (moduliGlobalSectionsRing B.right)) :
    moduliAlgebraSectionsMap (map hB hB' f) (sectionsEquiv B hB s) =
      sectionsEquiv B' hB' (MvPolynomial.map (moduliAlgebraSectionsMap f) s)
  /-- Surjectivity is local for the fppf topology. -/
  map_surjective {B B' : ModuliAlgebraSheaf F hF}
      (hB : IsQuasicoherentModuliAlgebra B) (hB' : IsQuasicoherentModuliAlgebra B')
      (f : B ⟶ B') : IsSurjectiveModuliAlgebra f →
        IsSurjectiveModuliAlgebra (map hB hB' f)

variable {k : Type u} [Field k] {P : Type u} [CommRing P] [Algebra k P]
variable {X : BasedCategory.{v, w} (Over (Spec (.of k)))}
variable {hX : IsFibredInGroupoids X}

/-- The structural image of a base scalar in a coefficient algebra on a test.
Source: Alper 5.2.1; uses the existing scalar pullback, not an arbitrary action
(blueprint: def-sfb-stack-polynomial-rees-data). -/
def moduliPolynomialScalar
    (p : BasedFunctor X (discreteModuli
      (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k P)))))))
    (B : ModuliAlgebraSheaf X hX) (x : X.obj) : P →+* B.right.obj.obj (op x) :=
  (B.hom.hom.app (op x)).hom.comp (moduliScalarMap p x)

/-- Rees data include quasi-coherent ideal powers, the quotient, a coproduct grading,
smooth-affine Rees comparisons, the graded polynomial surjection, and the global
coefficient embedding. No injectivity on arbitrary nonflat tests is required.
Source: Alper, proof of Lemma 5.2.1, with the unital degree-zero summand
(blueprint: def-sfb-stack-polynomial-rees-data). -/
structure ModuliReesPresentation
    (p : BasedFunctor X (discreteModuli
      (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k P)))))))
    (B : ModuliAlgebraSheaf X hX) (hB : IsQuasicoherentModuliAlgebra B)
    (J : Type (max (u + 1) v w)) (I : Ideal P) (a : J → P)
    (polynomial : ModuliPolynomialSystem X hX J) where
  /-- The powers J^m as actual quasi-coherent module sheaves, in the full subcategory
  cut out by Mathlib's local-presentation predicate on the recorded module rings. -/
  power : ℕ → (SheafOfModules.isQuasicoherent (moduliModuleRings X hX)).FullSubcategory
  /-- Their inclusions in the coefficient algebra in QCoh. -/
  inclusion (m : ℕ) : power m ⟶ ⟨moduliAlgebraModule B, hB⟩
  /-- These are monomorphisms in QCoh, not asserted monos in all big-site modules. -/
  inclusion_mono (m : ℕ) : Mono (inclusion m)
  /-- Degree zero is B with its identity inclusion. -/
  zero : power 0 ≅ ⟨moduliAlgebraModule B, hB⟩
  /-- Normalization of the degree-zero inclusion. -/
  inclusion_zero : inclusion 0 = zero.hom
  /-- Powers are exactly the ordinary extended ideal powers on smooth affine charts. -/
  power_chart (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
      (ht : IsSmoothModuliSchemeTest t) (hT : IsAffine T.left) (m : ℕ) :
    Function.Injective ((inclusion m).hom.val.app (op (moduliPolynomialChartObject t))) ∧
      Set.range ((inclusion m).hom.val.app (op (moduliPolynomialChartObject t))) =
        ((I.map (moduliPolynomialScalar p B (moduliPolynomialChartObject t)) ^ m :
          Ideal (B.right.obj.obj (op (moduliPolynomialChartObject t)))) :
          Set (B.right.obj.obj (op (moduliPolynomialChartObject t))))
  /-- The quotient algebra B/J. -/
  quotient : ModuliAlgebraSheaf X hX
  /-- The quotient is quasi-coherent. -/
  quotient_quasicoherent : IsQuasicoherentModuliAlgebra quotient
  /-- Its specified quotient map. -/
  quotientMap : B ⟶ quotient
  /-- The quotient map is a sheaf surjection. -/
  quotient_surjective : IsSurjectiveModuliAlgebra quotientMap
  /-- On smooth affine charts this is the ordinary algebra quotient by the ideal. -/
  quotient_chart (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
      (ht : IsSmoothModuliSchemeTest t) (hT : IsAffine T.left) :
    Function.Surjective (quotientMap.right.hom.app (op (moduliPolynomialChartObject t))) ∧
      RingHom.ker (quotientMap.right.hom.app (op (moduliPolynomialChartObject t))).hom =
        I.map (moduliPolynomialScalar p B (moduliPolynomialChartObject t))
  /-- The unital Rees algebra. -/
  algebra : ModuliAlgebraSheaf X hX
  /-- The Rees algebra is quasi-coherent. -/
  quasicoherent : IsQuasicoherentModuliAlgebra algebra
  /-- The homogeneous-summand maps. -/
  degree (m : ℕ) : (power m).obj ⟶ moduliAlgebraModule algebra
  /-- Their coproduct, in all module sheaves, is the underlying Rees module. -/
  coproduct : IsColimit (Cofan.mk (moduliAlgebraModule algebra) degree)
  /-- Smooth affine restrictions are ordinary Rees algebras. -/
  chart (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
      (ht : IsSmoothModuliSchemeTest t) (hT : IsAffine T.left) :
    algebra.right.obj.obj (op (moduliPolynomialChartObject t)) ≃+*
      reesAlgebra (I.map (moduliPolynomialScalar p B (moduliPolynomialChartObject t)))
  /-- The chart comparison respects the grading and its ideal inclusions. -/
  degree_chart (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
      (ht : IsSmoothModuliSchemeTest t) (hT : IsAffine T.left) (m : ℕ)
      (s : (power m).obj.val.obj (op (moduliPolynomialChartObject t))) :
    (chart T t ht hT ((degree m).val.app (op (moduliPolynomialChartObject t)) s)).val =
      Polynomial.monomial m (@id (B.right.obj.obj (op (moduliPolynomialChartObject t)))
        ((inclusion m).hom.val.app (op (moduliPolynomialChartObject t)) s))
  /-- The structural B-algebra map, in degree zero. -/
  constant : B ⟶ algebra
  /-- Its degree-zero formula on smooth charts. -/
  constant_chart (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
      (ht : IsSmoothModuliSchemeTest t) (hT : IsAffine T.left)
      (b : B.right.obj.obj (op (moduliPolynomialChartObject t))) :
    (chart T t ht hT (constant.right.hom.app (op (moduliPolynomialChartObject t)) b)).val =
      Polynomial.C b
  /-- The polynomial presentation. -/
  q : polynomial.algebra B hB ⟶ algebra
  /-- Surjective as a sheaf of graded algebras. -/
  q_surjective : IsSurjectiveModuliAlgebra q
  /-- The degree-zero map is the identity of B in its coefficient coordinates. -/
  q_constant : polynomial.constant B hB ≫ q = constant
  /-- Each generator maps to a_j T. The full formula also specifies gradedness. -/
  q_chart (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X)
      (ht : IsSmoothModuliSchemeTest t) (hT : IsAffine T.left)
      (hx : IsAffine ((moduliSchemeForget X).obj (moduliPolynomialChartObject t)))
      (s : (polynomial.algebra B hB).right.obj.obj (op (moduliPolynomialChartObject t))) :
    (chart T t ht hT (q.right.hom.app (op (moduliPolynomialChartObject t)) s)).val =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun j ↦ Polynomial.monomial 1
          (moduliPolynomialScalar p B (moduliPolynomialChartObject t) (a j)))
        (polynomial.chart B hB (moduliPolynomialChartObject t) hx
          ⟨T, t, ht, ⟨Iso.refl _⟩⟩ s)
  /-- Global sections of the grading are the direct sum of the homogeneous sections.
  The unit-module Hom is the existing compatible-family global sections functor. -/
  global_coproduct : Function.Bijective
    (DirectSum.toAddMonoid (fun m : ℕ ↦
      Preadditive.rightComp (SheafOfModules.unit (moduliModuleRings X hX)) (degree m)) :
      (⨁ m : ℕ, (SheafOfModules.unit (moduliModuleRings X hX) ⟶ (power m).obj)) →+
        (SheafOfModules.unit (moduliModuleRings X hX) ⟶ moduliAlgebraModule algebra))
  /-- The global graded-algebra embedding into B[T]. -/
  globalEmbedding : moduliGlobalSectionsRing algebra.right →+*
    Polynomial (moduliGlobalSectionsRing B.right)
  /-- It is injective, also when the stack or coefficient algebra is zero. -/
  global_injective : Function.Injective globalEmbedding
  /-- The homogeneous sections have exactly their specified monomial coordinates. -/
  global_degree (m : ℕ) (s : (power m).obj.sections) :
    globalEmbedding (moduliModuleSectionInAlgebra algebra (degree m) s) =
      Polynomial.monomial m (moduliModuleSectionInAlgebra B (inclusion m).hom s)
  /-- The image consists exactly of polynomials whose m-th coefficient is in Γ(J^m). -/
  global_range (f : Polynomial (moduliGlobalSectionsRing B.right)) :
    (∃ s, globalEmbedding s = f) ↔ ∀ m : ℕ, ∃ s : (power m).obj.sections,
      moduliModuleSectionInAlgebra B (inclusion m).hom s = f.coeff m
  /-- The structural global scalar family exists and fixes every Γ(q) coefficient. -/
  global_scalar (r : P) : ∃ b : moduliGlobalSectionsRing B.right,
    ∀ x : X.obj, b.1 (op x) = moduliPolynomialScalar p B x r
  /-- Γ(q) is finite polynomial evaluation with x_j sent to a_j T. -/
  global_q (f : MvPolynomial J (moduliGlobalSectionsRing B.right))
      (b : J → moduliGlobalSectionsRing B.right)
      (hb : ∀ (j : J) (x : X.obj),
        (b j).1 (op x) = moduliPolynomialScalar p B x (a j)) :
    globalEmbedding (moduliAlgebraSectionsMap q (polynomial.sectionsEquiv B hB f)) =
      MvPolynomial.eval₂Hom Polynomial.C (fun j ↦ Polynomial.monomial 1 (b j)) f

end CategoryTheory
