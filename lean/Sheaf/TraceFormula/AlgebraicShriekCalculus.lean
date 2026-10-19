/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.TensorProduct.Basic

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.RingTheory.RegularSequenceKoszulRegular
import Sheaf.RingTheory.RegularSequenceConormal
import Sheaf.RingTheory.KoszulRegularSequenceDualComplex
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.Algebra.Homology.FlatResolutionTorComparison
import Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise
import Sheaf.RingTheory.ProjectiveResolutionKernelProjective
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.BaseChangeRHomPerfect
import Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor
import Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange

/-! # Polynomial models for algebraic upper shriek

Source: Stacks Project, dualizing.tex, Tags 0BZI, 0BZJ, 0A70, 0A71, 0C0F,
0BZN, 0BZT and 0C0H (blueprint: lem-trf-algebraic-shriek-calculus).

The data package states existence of scalar extension and coinduction, fixes their
adjunctions and K-injective model, and states the polynomial-model calculus. No functor
is chosen from its still unproved existence theorem. The standard localization universe
is used for ordinary modules; the ring and module universe `u` is arbitrary.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Standard localization of ordinary module complexes.
Source: Stacks 05RR (blueprint: lem-trf-algebraic-shriek-calculus). -/
instance algebraicShriekModuleDerived (R : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- Ordinary coinduction is additive by its explicit restriction/coinduction adjunction.
Source: Stacks 0A70 (blueprint: lem-trf-algebraic-shriek-calculus). -/
instance algebraicShriekCoextendAdditive {R A : CommRingCat.{u}} (φ : R →+* A) :
    (ModuleCat.coextendScalars.{u, u, u} φ).Additive :=
  (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} φ).right_adjoint_additive

/-- The ordinary module derived category, with its standard localization size.
Source: Stacks 05RR (blueprint: lem-trf-algebraic-shriek-calculus). -/
abbrev algebraicShriekD (R : CommRingCat.{u}) := DerivedCategory (ModuleCat.{u} R)

/-- Exact derived restriction of scalars.
Source: Stacks 0A70 (blueprint: lem-trf-algebraic-shriek-calculus). -/
def algebraicShriekRestriction {R A : CommRingCat.{u}} (φ : R →+* A) :
    algebraicShriekD A ⥤ algebraicShriekD R :=
  (ModuleCat.restrictScalars φ).mapDerivedCategory

/-- Canonical composition comparison for restriction of scalars.
Source: Stacks 0C0F (blueprint: lem-trf-algebraic-shriek-calculus). -/
def algebraicShriekRestrictionComp {R B C : CommRingCat.{u}}
    (a : R →+* B) (b : B →+* C) :
    algebraicShriekRestriction (b.comp a) ≅
      algebraicShriekRestriction b ⋙ algebraicShriekRestriction a :=
  Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp a b) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The actual tensor-product base-change ring, with structures induced by the given maps.
Source: Stacks 0BZN (blueprint: lem-trf-algebraic-shriek-calculus). -/
def algebraicShriekBaseRing {R A R' : CommRingCat.{u}} (φ : R →+* A) (ρ : R →+* R') :
    CommRingCat.{u} :=
  letI := φ.toAlgebra
  letI := ρ.toAlgebra
  CommRingCat.of (A ⊗[R] R')

/-- The left tensor coprojection `A → A ⊗_R R'`.
Source: Stacks 0BZN (blueprint: lem-trf-algebraic-shriek-calculus). -/
def algebraicShriekBaseLeft {R A R' : CommRingCat.{u}} (φ : R →+* A) (ρ : R →+* R') :
    A →+* algebraicShriekBaseRing φ ρ :=
  letI := φ.toAlgebra
  letI := ρ.toAlgebra
  Algebra.TensorProduct.includeLeftRingHom

/-- The base-changed map `R' → A ⊗_R R'`.
Source: Stacks 0BZN (blueprint: lem-trf-algebraic-shriek-calculus). -/
def algebraicShriekBaseRight {R A R' : CommRingCat.{u}} (φ : R →+* A) (ρ : R →+* R') :
    R' →+* algebraicShriekBaseRing φ ρ :=
  letI := φ.toAlgebra
  letI := ρ.toAlgebra
  Algebra.TensorProduct.includeRight.toRingHom

/-- The base-changed map is finite type by Mathlib's base-change stability theorem.
Source: Stacks 0BZN (blueprint: lem-trf-algebraic-shriek-calculus). -/
abbrev algebraicShriekBaseFiniteType {R A R' : CommRingCat.{u}}
    (φ : R →+* A) (hφ : RingHom.FiniteType φ) (ρ : R →+* R') :
    RingHom.FiniteType (algebraicShriekBaseRight φ ρ) :=
  letI := φ.toAlgebra
  letI := ρ.toAlgebra
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := R')
  RingHom.finiteType_isStableUnderBaseChange R A R' (A ⊗[R] R') hφ

/-- The tensor-product ring is Noetherian, using its finite-type structure over R'.
Source: Stacks 0BZN and 00FN (blueprint: lem-trf-algebraic-shriek-calculus). -/
abbrev algebraicShriekBaseNoetherian {R A R' : CommRingCat.{u}} [IsNoetherianRing R']
    (φ : R →+* A) (hφ : RingHom.FiniteType φ) (ρ : R →+* R') :
    IsNoetherianRing (algebraicShriekBaseRing φ ρ) :=
  letI := (algebraicShriekBaseRight φ ρ).toAlgebra
  letI : Algebra.FiniteType R' (algebraicShriekBaseRing φ ρ) :=
    algebraicShriekBaseFiniteType φ hφ ρ
  Algebra.FiniteType.isNoetherianRing R' (algebraicShriekBaseRing φ ρ)

/-- Choices of the algebraic upper-shriek calculus, with the comparisons of the node.
Scalar extension is characterized by its left adjunction to the actual exact restriction;
coinduction by its right adjunction and by ordinary `Hom_R(A,I)` on K-injective targets.
Thus the latter includes the multiplication action and forgetting it is ordinary RHom.
The counit normalization fixes evaluation at one. Polynomial models are compared as
functors, with no chosen orientation between presentations.
Source: Stacks 0BZI, 0BZJ, 0A70, 0A71, 0C0F, 0BZN, 0BZT, 0C0H
(blueprint: lem-trf-algebraic-shriek-calculus). -/
structure AlgebraicShriekCalculus where
  /-- Derived extension of scalars for every ring map. -/
  extension : ∀ {R A : CommRingCat.{u}}, (R →+* A) → (algebraicShriekD R ⥤ algebraicShriekD A)
  /-- The tensor/restriction adjunction determines extension up to unique isomorphism. -/
  extensionAdj : ∀ {R A : CommRingCat.{u}} (φ : R →+* A),
    extension φ ⊣ algebraicShriekRestriction φ
  /-- Derived coinduction for every ring map, without Noetherian hypotheses. -/
  coinduction : ∀ {R A : CommRingCat.{u}}, (R →+* A) →
    (algebraicShriekD R ⥤ algebraicShriekD A)
  /-- The restriction/coinduction adjunction. -/
  coinductionAdj : ∀ {R A : CommRingCat.{u}} (φ : R →+* A),
    algebraicShriekRestriction φ ⊣ coinduction φ
  /-- K-injective coinduction model, with the evaluation-at-one counit. -/
  coinductionModel : ∀ {R A : CommRingCat.{u}} (φ : R →+* A)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective],
    ∃ e : (coinduction φ).obj (DerivedCategory.Q.obj I) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I),
      (algebraicShriekRestriction φ).map e.hom ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          (((ModuleCat.restrictCoextendScalarsAdj.{u, u, u} φ).mapHomologicalComplex
            (.up ℤ)).counit.app I) =
      (coinductionAdj φ).counit.app (DerivedCategory.Q.obj I)
  /-- Canonical coinduction composition, characterized by its counits. -/
  coinductionComp : ∀ {R B C : CommRingCat.{u}} (a : R →+* B) (b : B →+* C),
    ∃ e : coinduction a ⋙ coinduction b ≅ coinduction (b.comp a),
      ∀ K : algebraicShriekD R,
        (algebraicShriekRestriction (b.comp a)).map (e.inv.app K) ≫
          (algebraicShriekRestrictionComp a b).hom.app _ ≫
          (algebraicShriekRestriction a).map
            ((coinductionAdj b).counit.app ((coinduction a).obj K)) ≫
          (coinductionAdj a).counit.app K = (coinductionAdj (b.comp a)).counit.app K
  /-- Chosen upper shriek for finite-type maps of Noetherian rings. -/
  shriek : ∀ {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A), RingHom.FiniteType φ → (algebraicShriekD R ⥤ algebraicShriekD A)
  /-- Every chosen polynomial presentation computes the same functor up to isomorphism. -/
  polynomialModel : ∀ {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : RingHom.FiniteType φ) (n : ℕ)
    (p : MvPolynomial (Fin n) R →+* A) (_hp : Function.Surjective p)
    (_hc : p.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = φ),
    Nonempty (shriek φ hφ ≅
      extension (R := R) (A := CommRingCat.of (MvPolynomial (Fin n) R)) MvPolynomial.C ⋙
        coinduction (R := CommRingCat.of (MvPolynomial (Fin n) R)) p ⋙
          shiftFunctor (algebraicShriekD A) (n : ℤ))
  /-- Surjective maps have the zero-variable coinduction model. -/
  surjection : ∀ {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : RingHom.FiniteType φ) (_hs : Function.Surjective φ),
    Nonempty (shriek φ hφ ≅ coinduction φ)
  /-- Composition for bounded-below input, allowing zero polynomial generators. -/
  composition : ∀ {R B C : CommRingCat.{u}}
    [IsNoetherianRing R] [IsNoetherianRing B] [IsNoetherianRing C]
    (a : R →+* B) (b : B →+* C) (ha : RingHom.FiniteType a)
    (hb : RingHom.FiniteType b)
    (K : algebraicShriekD R) (_hK : ∃ n : ℤ, K.IsGE n),
    Nonempty ((shriek b hb).obj ((shriek a ha).obj K) ≅ (shriek (b.comp a) (hb.comp ha)).obj K)
  /-- The identity ring map admits the identity model. -/
  identity : ∀ (R : CommRingCat.{u}) [IsNoetherianRing R],
    Nonempty (shriek (RingHom.id R) (RingHom.FiniteType.id R) ≅ 𝟭 (algebraicShriekD R))
  /-- Flat base change for the actual tensor-product ring and bounded-below input. -/
  flatBaseChange : ∀ {R A R' : CommRingCat.{u}}
    [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing R']
    (φ : R →+* A) (hφ : RingHom.FiniteType φ) (ρ : R →+* R') (_hρ : RingHom.Flat ρ)
    (K : algebraicShriekD R) (_hK : ∃ n : ℤ, K.IsGE n),
    Nonempty ((extension (algebraicShriekBaseLeft φ ρ)).obj ((shriek φ hφ).obj K) ≅
      (@shriek R' (algebraicShriekBaseRing φ ρ) inferInstance
        (algebraicShriekBaseNoetherian φ hφ ρ) (algebraicShriekBaseRight φ ρ)
        (algebraicShriekBaseFiniteType φ hφ ρ)).obj ((extension ρ).obj K))
  /-- Open-immersion localization on the entire unbounded derived category. -/
  openImmersion : ∀ {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : RingHom.FiniteType φ)
    (_hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))),
    Nonempty (shriek φ hφ ≅ extension φ)

/-- Existence of all polynomial upper-shriek models and the comparisons specified above.
Source: Stacks 0BZI, 0BZJ, 0A70, 0A71, 0C0F, 0BZN, 0BZT, 0C0H
(blueprint: lem-trf-algebraic-shriek-calculus).

Proof:
1. Resolve ordinary module complexes by K-injectives. Ordinary coinduction is
Hom_R(A,I), with (a h)(a') = h(a'a), and the counit is evaluation at one. Its
Hom-complex adjunction proves that coinduction preserves K-injectives and descends
to the derived category; forgetting the A-action gives ordinary derived Hom. Use
lem-weil-pbc-ring-modules-grothendieck-abelian, lem-sfb-grothendieck-k-injective,
lem-sc-kinjective-quasi-iso-comparison and def-pur-derived-internal-hom.
2. Successive coinduction is identified by h ↦ (c ↦ (b ↦ h(bc))), inverse
v ↦ (c ↦ v(c)(1)); both evaluation counits compose to evaluation at one.
3. For a nonzerodivisor quotient T → T/(s), the two-term Koszul resolution and
conormal generator give coinduction of T equal to T/(s)[-1]. Perfect-algebra
coinduction/tensor comparison gives the formula for every input complex. Use
lem-weil-pbc-regular-sequence-koszul-regular,
lem-weil-pbc-regular-sequence-conormal-free,
lem-sc-koszul-regular-sequence-dual-complex and
lem-trf-perfect-algebra-coinduction-tensor.
4. Define the polynomial model by extension, coinduction and shift by n. Compare
P → A with P[y] → A using a lift g of y and the monic regular element y-g.
Step 3 cancels the added shift. Iteration and a common polynomial refinement
compare any two models, without asserting an orientation independent of lifts. Use
lem-pur-derived-change-of-rings and lem-pc-derived-tensor-second-factor-functor.
5. A surjection admits zero variables and hence coinduction; identity coinduction
is the identity by evaluation at one.
6. Hilbert's basis theorem makes polynomial rings Noetherian. A finite-free
resolution makes A pseudo-coherent over P; polynomial extensions are flat by
the monomial basis. Flatness persists after scalar extension. Use
lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-finite-free-resolution-noetherian, def-pc-ring-pseudo-coherent-complex
and def-weil-pbc-flat-ring-map.
7. The coinduction flat-base-change arrow is the mate of scalar extension of
evaluation. Forgetting the action identifies it with the pseudo-coherent RHom
flat comparison on bounded-below targets; restriction reflects isomorphisms. Use
lem-trf-pseudocoherent-rhom-flat-base-change.
8. Base change the polynomial presentation. Apply step 7 and double scalar
extension to obtain the flat-base-change comparison on bounded-below inputs.
9. For R → B → C use P → B and Q=P[y], Q'=B[y] → C. Step 7 followed by
coinduction composition gives the polynomial model over Q and shift n+m.
10. For an open immersion, flatness and stalkwise Tor dimension zero give a
perfect polynomial resolution; truncate a finite-free resolution at a projective
syzygy. The zero ring is treated by the zero derived category. Use
def-weil-open-immersion, def-weil-flat-morphism,
lem-weil-pbc-flat-morphism-affine-criterion, lem-pc-flat-resolution-tor-comparison,
lem-pc-affine-polynomial-resolution-of-stalkwise,
lem-weil-pbc-projective-resolution-kernel-projective, def-pc-perfect-ring-complex,
pqf-def-locnoeth and lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact.
11. The open-immersion monomorphism gives A tensor_R A = A. The base-changed
presentation is the graph quotient by x_i-a_i; its ordered regular sequence
and dual Koszul complex identify its coinduction with A[-n]. Use
lem-weil-pbc-fibre-product-affine-spectra and the regular-sequence and dual-Koszul
inputs of step 3.
12. Perfect derived-Hom base change and the equality of the two coprojections
show that the shifted coinduction of P has only H^0=A, with its A-action. Use
lem-pc-base-change-rhom-perfect.
13. Perfect-algebra coinduction/tensor comparison now gives extension of scalars
for every input, including unbounded complexes. Use
lem-trf-perfect-algebra-coinduction-tensor and
lem-pc-derived-tensor-second-factor-functor. -/
theorem nonempty_algebraicShriekCalculus : Nonempty (AlgebraicShriekCalculus.{u}) := by
  sorry

end AlgebraicGeometry
