/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Adequately affine morphisms of algebraic stacks

Source: Alper, *Adequate moduli spaces and geometrically reductive group schemes*,
Definitions 3.4.1 and 4.1.1, printed pp. 14 and 16
(blueprint: def-sfb-adequately-affine-morphism).

The smooth tests and their étale covering families are expanded in the predicate.
Direct-image values are the existing compatible-family section rings on the actual
2-fibre products. Restriction uses the canonical right-factor base-change functor;
the power-lifting equation is evaluated at every object of the base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A smooth scheme map to a stack: every scheme base change is an algebraic space
whose specified projection is smooth on all étale scheme charts. No surjectivity is
required. Source: Alper, §2 and Definition 3.4.1
(blueprint: def-sfb-adequately-affine-morphism). -/
def IsSmoothModuliSchemeTest {S : Scheme.{u}}
    {V : BasedCategory.{v₂, w₂} (Over S)} {T : Over S}
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) V) : Prop :=
  ∀ (W : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj W)) V),
    ∃ (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj W),
      HasSpaceBaseChange t W p Z a ∧ SpaceMapIsSmooth Z W a

/-- An arrow of scheme tests is a scheme map together with the specified
2-isomorphism over the stack. Restricting its endpoints to smooth tests gives the
arrows of Lis-ét. Source: Alper, §2
(blueprint: def-sfb-adequately-affine-morphism). -/
structure ModuliSchemeTestArrow {S : Scheme.{u}}
    {V : BasedCategory.{v₂, w₂} (Over S)} {T T' : Over S}
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) V)
    (t' : BasedFunctor (discreteModuli (yoneda.obj T')) V) where
  /-- The underlying scheme map over the base. -/
  schemeMap : T ⟶ T'
  /-- The 2-isomorphism comparing the composite to the given source test. -/
  comparison : (discreteModuliMap (yoneda.map schemeMap)).comp t' ≅ t

/-- The ring Γ(U ×_V T, A|), with literal restriction along the first projection.
Its elements are compatible section families on the entire 2-fibre-product category,
not just sections on a chosen atlas. Source: Alper, §2 and Definition 3.4.1
(blueprint: def-sfb-adequately-affine-morphism). -/
def moduliSchemeTestSections {S : Scheme.{u}}
    {U : BasedCategory.{v₁, w₁} (Over S)} {V : BasedCategory.{v₂, w₂} (Over S)}
    {hU : IsFibredInGroupoids U} (f : BasedFunctor U V)
    (A : ModuliAlgebraSheaf U hU) {T : Over S}
    (t : BasedFunctor (discreteModuli (yoneda.obj T)) V) :=
  RingCat.sectionsSubring
    ((moduliTwoFiberFst f t).toFunctor.op ⋙ A.right.obj ⋙ forget₂ CommRingCat RingCat)

/-- Restriction of compatible section families by the actual 2-base-change functor.
It retains the specified 2-isomorphism of a test arrow. Source: Alper, §2 and
Definition 3.4.1 (blueprint: def-sfb-adequately-affine-morphism). -/
def moduliSchemeTestRestriction {S : Scheme.{u}}
    {U : BasedCategory.{v₁, w₁} (Over S)} {V : BasedCategory.{v₂, w₂} (Over S)}
    {hU : IsFibredInGroupoids U} (f : BasedFunctor U V)
    (A : ModuliAlgebraSheaf U hU) {T T' : Over S}
    {t : BasedFunctor (discreteModuli (yoneda.obj T)) V}
    {t' : BasedFunctor (discreteModuli (yoneda.obj T')) V}
    (a : ModuliSchemeTestArrow t t')
    (s : moduliSchemeTestSections f A t') : moduliSchemeTestSections f A t :=
  ⟨fun x ↦ s.1 (op ((moduliTwoFiberMapRight f
      (discreteModuliMap (yoneda.map a.schemeMap)) a.comparison).obj x.unop)),
    fun g ↦ s.2 ((moduliTwoFiberMapRight f
      (discreteModuliMap (yoneda.map a.schemeMap)) a.comparison).map g.unop).op⟩

/-- Universal adequacy of the induced direct-image map, expanded on smooth scheme
tests. The cover is a jointly surjective étale scheme family, its maps are over S,
and its test maps are the composites with t. On each member a positive power of the
restricted section lifts. Equality is pointwise in the compatible-family section ring.
Source: Alper, Definition 3.4.1 (blueprint: def-sfb-adequately-affine-morphism). -/
def IsUniversallyAdequateModuliDirectImage {S : Scheme.{u}}
    {U : BasedCategory.{v₁, w₁} (Over S)} {V : BasedCategory.{v₂, w₂} (Over S)}
    {hU : IsFibredInGroupoids U} {A B : ModuliAlgebraSheaf U hU}
    (f : BasedFunctor U V) (q : A ⟶ B) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) V),
    IsSmoothModuliSchemeTest t → ∀ s : moduliSchemeTestSections f B t,
      ∃ (I : Type u) (W : I → Over S) (j : ∀ i : I, W i ⟶ T),
        (∀ i : I, Etale (j i).left) ∧
        (∀ x : T.left, ∃ (i : I) (y : (W i).left), (j i).left y = x) ∧
        ∀ i : I, ∃ (N : ℕ) (_ : 0 < N)
          (r : moduliSchemeTestSections f A
            ((discreteModuliMap (yoneda.map (j i))).comp t)),
          ∀ x : (moduliTwoFiberProduct f
              ((discreteModuliMap (yoneda.map (j i))).comp t)).obj,
            (q.right.hom.app (op x.obj.left)) (r.1 (op x)) =
              ((moduliSchemeTestRestriction f B
                ⟨j i, Iso.refl _⟩ s).1 (op x)) ^ N

/-- A qcqs morphism of algebraic stacks is adequately affine if every surjection
of arbitrary quasi-coherent algebras has universally adequate direct image.
No finite generation or finite presentation restriction is imposed on the algebras.
The field and algebraic-stack proofs express the ambient setting of the definition.
Source: Alper, Definition 4.1.1 (blueprint: def-sfb-adequately-affine-morphism). -/
def IsAdequatelyAffineMorphism {k : Type u} [Field k]
    {U : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {V : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (f : BasedFunctor U V) (hU : IsAlgebraicModuliStack U)
    (_hV : IsAlgebraicModuliStack V) : Prop :=
  IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, 0, 0} f ∧
    IsQuasiSeparatedAlgebraicModuliMap f ∧
    ∀ (A B : ModuliAlgebraSheaf U hU.1.1) (q : A ⟶ B),
      IsQuasicoherentModuliAlgebra A → IsQuasicoherentModuliAlgebra B →
      IsSurjectiveModuliAlgebra q → IsUniversallyAdequateModuliDirectImage f q

end CategoryTheory
