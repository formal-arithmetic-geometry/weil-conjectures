/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Flat.Basic

/-! # Flat quotient base change for derived coinduction

Source: Stacks Project, dualizing.tex, equation-base-change, Tags 0BZM and 0E2A;
more-algebra.tex, Tag 0A6A(3).
(blueprint: lem-trf-coinduction-flat-quotient-base-change).

The pushout square presents A' = A tensor_P P'. Universal scalar pairs present
ordinary derived extension of scalars with their actual K-flat counits. The
K-injective formula specifies the underlying RHom map without forgetting the
A'-action in the derived comparison itself.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wP wA wT wB

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- Flat quotient base change, natural on the whole unbounded derived category and
invertible on its cohomologically bounded-below objects. The component equation
fixes the map as the evaluation-counit mate. The last clause identifies its
restriction with the ordinary derived-Hom comparison on every K-injective model:
B(s tensor h)(b(t) * a(x)) = q(st tensor h(x)). No Noetherianity of T or upper
cohomological bound is assumed.

Source: Stacks Project, dualizing.tex, equation-base-change, Tags 0BZM and 0E2A;
more-algebra.tex, Tag 0A6A(3)
(blueprint: lem-trf-coinduction-flat-quotient-base-change).

Proof:
1. On the one-object identity-cover site sheaves are ordinary modules. The
balancing maps N tensor_A (A tensor_P T) to N tensor_P T and back send
x tensor (a tensor s) to ax tensor s and x tensor s to x tensor (1 tensor s).
Flat tensor exactness (lem-weil-pbc-flat-tensor-exact) shows A' is A-flat and
both termwise scalar functors preserve all quasi-isomorphisms. Their derived
universal counits (lem-pur-derived-change-of-rings) therefore give the natural
isomorphism theta with the displayed shared tensor normalization.
2. Apply lem-trf-derived-coinduction-adjunction to theta followed by scalar
extension of the evaluation-at-one counit. Its transpose is beta, including
its A'-action. Naturality of theta, the counit and the adjunction gives a
natural transformation on every object of D(P).
3. For a K-injective P-complex I and a K-injective resolution q of T tensor_P I,
define B(s tensor h)(b(t) a(x)) = q(st tensor h(x)). The tensor relations and
the chain-map equation for q make B well defined and a chain map. Its formula
commutes with the A'-action by precomposition. Evaluation at 1 gives the
scalar extension of h mapped to h(1), so its localized map is the mate in
step 2. Forgetting the A'-action is precisely extension of morphisms followed
by q and T-linear extension, the ordinary RHom map of
def-pur-derived-internal-hom and Tag 0A6A. The final equation retains the
canonical K-injective model maps and the actual derived scalar counits.
4. Surjectivity makes A cyclic over P. The Noetherian finite-free resolution
lem-weil-pbc-finite-free-resolution-noetherian supplies a nonpositive complex
of finite free modules resolving A, with no finite-length assertion. Hence
A[0] is pseudo-coherent (def-pc-ring-pseudo-coherent-complex).
5. For a bounded-below M, lem-trf-pseudocoherent-rhom-flat-base-change makes
the underlying map of step 3 invertible. Flatness identifies the derived
base change of A with A'. Restriction is conservative by
lem-trf-derived-coinduction-adjunction, so beta is invertible in D(A'). -/
theorem coinduction_flatQuotient_baseChange
    {P A T B : Type u} [CommRing P] [CommRing A] [CommRing T] [CommRing B]
    [IsNoetherianRing P]
    [HasDerivedCategory.{wP} (ModuleCat.{u} P)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wT} (ModuleCat.{u} T)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (f : P →+* A) (g : P →+* T) (a : A →+* B) (b : T →+* B)
    (hf : Function.Surjective f) (hg : g.Flat)
    (hB : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom a) (CommRingCat.ofHom b))
    (dP : CoinductionScalarPair g) (dA : CoinductionScalarPair a) :
    ∃ (θ : dA.F ⋙ (restrictScalars b).mapDerivedCategory ≅
          (restrictScalars f).mapDerivedCategory ⋙ dP.F)
      (β : derivedCoinduction f ⋙ dA.F ⟶ dP.F ⋙ derivedCoinduction b),
      CoinductionTensorNormalized f g a b dP dA θ ∧
      (∀ M : DerivedCategory (ModuleCat.{u} P),
        β.app M = coinductionScalarExchange f b dP dA θ M) ∧
      (∀ M : DerivedCategory (ModuleCat.{u} P),
        (∃ c : ℤ, ∀ i : ℤ, i < c →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} P) i).obj M)) →
        IsIso (β.app M)) ∧
      (∀ (I : CochainComplex (ModuleCat.{u} P) ℤ) [I.IsKInjective]
        (J : CochainComplex (ModuleCat.{u} T) ℤ) [J.IsKInjective]
        (q : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj I ⟶ J),
        QuasiIso q →
        ∃ H : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj
              (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
                ((coinductionComplexFunctor f).obj I)) ⟶
            ((restrictScalars b).mapHomologicalComplex (.up ℤ)).obj
              ((coinductionComplexFunctor b).obj J),
          (∀ (n : ℤ) (s t : T) (x : A) (h : ((coinductionComplexFunctor f).obj I).X n),
            CoextendScalars.equiv b (J.X n) (H.f n (s ⊗ₜ[P,g] h)) (b t * a x) =
              q.f n ((s * t) ⊗ₜ[P,g] (CoextendScalars.equiv f (I.X n) h x))) ∧
          θ.inv.app ((derivedCoinduction f).obj (DerivedCategory.Q.obj I)) ≫
              (restrictScalars b).mapDerivedCategory.map (β.app (DerivedCategory.Q.obj I)) ≫
              (restrictScalars b).mapDerivedCategory.map
                ((derivedCoinduction b).map (dP.counit.app I ≫ DerivedCategory.Q.map q)) ≫
              (restrictScalars b).mapDerivedCategory.map (derivedCoinductionModel b J).hom ≫
              (restrictScalars b).mapDerivedCategoryFactors.hom.app
                ((coinductionComplexFunctor b).obj J) =
            dP.F.map ((restrictScalars f).mapDerivedCategory.map
              (derivedCoinductionModel f I).hom) ≫
              dP.F.map ((restrictScalars f).mapDerivedCategoryFactors.hom.app
                ((coinductionComplexFunctor f).obj I)) ≫
              dP.counit.app (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
                ((coinductionComplexFunctor f).obj I)) ≫ DerivedCategory.Q.map H) := by
  sorry

end ModuleCat
