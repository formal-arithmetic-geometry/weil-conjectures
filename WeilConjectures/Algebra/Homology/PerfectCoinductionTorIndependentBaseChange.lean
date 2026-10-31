/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PerfectCoinductionTorIndependentExchange
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.BaseChangeRHomPerfect

/-! # Tor-independent base change for perfect derived coinduction

Source: Stacks Project, more-algebra.tex, Tags 0A6A, 0661 and 07VI;
dualizing.tex, Tags 0A70 and 0A71.
(blueprint: lem-sfb-perfect-coinduction-tor-independent-base-change).
The comparison uses the published exchange interface, specialized to the fixed
ordinary scalar-extension functors. The Hom formula below retains arbitrary
unbounded K-flat targets, as required by perfect-source base change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Present the fixed ordinary derived scalar extension in the shared exchange interface.
Its data is the existing universal pair, with its actual K-flat counit.
Source: Stacks 06YY, 0661
(blueprint: lem-sfb-perfect-coinduction-tor-independent-base-change). -/
def ordinaryCoinductionScalarPair {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : CoinductionScalarPair f where
  F := ordinaryDerivedExtendScalars f
  counit := (ordinaryDerivedChangeOfRings f).counit
  universal := (ordinaryDerivedChangeOfRings f).universal
  computes := (ordinaryDerivedChangeOfRings f).computes

/-- Normalization of the identity scalar comparison on K-flat representatives.
Source: Stacks 06YY, 0661, ordinary multiplication for identity scalar extension
(blueprint: lem-sfb-perfect-coinduction-tor-independent-base-change). -/
def CoinductionIdentityScalarNormalized {R : Type u} [CommRing R]
    (e : ordinaryDerivedExtendScalars (RingHom.id R) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} R))) : Prop :=
  ∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P →
    e.hom.app (DerivedCategory.Q.obj P) =
      (ordinaryDerivedChangeOfRings (RingHom.id R)).counit.app P ≫
        DerivedCategory.Q.map
          (((NatIso.mapHomologicalComplex (extendScalarsId R) (.up ℤ)) ≪≫
            Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (.up ℤ)).hom.app P)

/-- The underlying perfect RHom map on every bounded finite projective source model
and every unbounded K-flat target. The shared K-injective comparison fixes both Hom
identifications. The coordinate formula is the scalar-extension map on Hom, and the
last equation is its ordered, signed evaluation formula, including Koszul evaluations.
Source: Stacks 0A6A, equation-base-change-RHom, 07VI
(blueprint: lem-sfb-perfect-coinduction-tor-independent-base-change). -/
def CoinductionPerfectHomFormula
    {A B T D : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing D]
    (f : A →+* B) (g : A →+* T) (b : B →+* D) (q : T →+* D)
    (θ : (ordinaryCoinductionScalarPair b).F ⋙ (restrictScalars q).mapDerivedCategory ≅
      (restrictScalars f).mapDerivedCategory ⋙ (ordinaryCoinductionScalarPair g).F) :
    Prop :=
  ∀ (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (s : E ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
      ((restrictScalars f).obj (of B B))),
    QuasiIso s →
    (∃ i j : ℤ, E.IsStrictlyGE i ∧ E.IsStrictlyLE j) →
    (∀ n : ℤ, Module.Finite A (E.X n) ∧ Module.Projective A (E.X n)) →
    ∀ Q : CochainComplex (ModuleCat.{u} A) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat Q →
    ∃ (sT : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E ⟶
          (CochainComplex.singleFunctor (ModuleCat.{u} T) 0).obj
            ((restrictScalars q).obj (of D D)))
      (χ : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.moduleHomComplex E Q) ⟶
        CochainComplex.moduleHomComplex
          (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E)
          (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q))
      (eA : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex E Q) ≅
        (restrictScalars f).mapDerivedCategory.obj
          ((derivedCoinduction f).obj (DerivedCategory.Q.obj Q)))
      (eT : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex
          (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E)
          (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
        (restrictScalars q).mapDerivedCategory.obj ((derivedCoinduction q).obj
          (DerivedCategory.Q.obj (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q)))),
      QuasiIso sT ∧
      (∀ (t : T) (x : E.X 0),
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((restrictScalars q).obj (of D D))).hom (sT.f 0 (t ⊗ₜ[A,g] x)) =
        q t * b ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((restrictScalars f).obj (of B B))).hom (s.f 0 x))) ∧
      CoinductionHomScalarFormula g E Q χ ∧ CoinductionHomModel f E Q s eA ∧
      CoinductionHomModel q
        (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E)
        (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q) sT eT ∧
      (ordinaryDerivedExtendScalars g).map eA.hom ≫
          θ.inv.app ((derivedCoinduction f).obj (DerivedCategory.Q.obj Q)) ≫
          (restrictScalars q).mapDerivedCategory.map
            (coinductionScalarExchange f q (ordinaryCoinductionScalarPair g)
              (ordinaryCoinductionScalarPair b) θ (DerivedCategory.Q.obj Q)) ≫
          (restrictScalars q).mapDerivedCategory.map
            ((derivedCoinduction q).map ((ordinaryDerivedChangeOfRings g).counit.app Q)) =
        (ordinaryDerivedChangeOfRings g).counit.app (CochainComplex.moduleHomComplex E Q) ≫
          DerivedCategory.Q.map χ ≫ eT.hom ∧
      (∀ (n r t : ℤ) (h : r + n = t)
        (z : (CochainComplex.moduleHomComplex E Q).X n) (x : E.X r) (a c : T),
        (r * n).negOnePow •
            (((χ.f n (a ⊗ₜ[A,g] z)).v r t h) (c ⊗ₜ[A,g] x)) =
          (a * c) ⊗ₜ[A,g] ((r * n).negOnePow • ((z.v r t h) x)))

/-- Tor-independent base change for perfect derived coinduction, with its canonical
underlying RHom comparison, counit, naturality, signed evaluations and tower equations.

Source: Stacks 0A6A (case 1), 0661, 07VI, 0A70 and 0A71
(blueprint: lem-sfb-perfect-coinduction-tor-independent-base-change).

Proof:
1. Resolve B[0] by a nonpositive free A-complex. It is K-flat by
lem-pc-module-bounded-flat-kflat. Its scalar extension has cohomology Tor_i^A(B,T)
by def-weil-pbc-tor-modules; hence its augmentation to D[0] is a quasi-isomorphism.
This identifies the derived tensor algebra with the ordinary pushout algebra.
2. Apply lem-sfb-perfect-coinduction-tor-independent-exchange to the fixed universal
scalar pairs. Its normalized tensor comparison gives the actual counit mate in D(D),
not merely an underlying A'-isomorphism. The adjunction gives the counit equation.
3. On a bounded finite-projective resolution of B and any K-flat model of N, the
inverse ordinary Hom adjunction sends x to (b to h(bx)). After scalar extension its
formula is (h tensor a)(x tensor c) = ac tensor h(x). The K-injective comparisons
therefore identify the underlying mate with def-pc-perfect-rhom-base-change-map.
By lem-pc-base-change-rhom-perfect this is invertible for every unbounded N;
conservativity of restriction in lem-trf-derived-coinduction-adjunction gives IsIso.
4. The exchange naturality and tower equations give naturality in N and successive
Tor-independent extension. For identity extension, the normalized multiplication
isomorphisms identify the mate's adjunct with the original evaluation counit, so
uniqueness in the adjunction gives the displayed identity equation.
5. A polynomial Koszul complex is bounded finite free. Its evaluation has sign
(-1)^(rn) in source degree r and Hom degree n. The coordinate formula commutes with
this sign and hence with every scalar-extended ordered Koszul evaluation, as in
lem-pod-perfect-dual-scalar-calculus. No Noetherianity or flatness is used. -/
theorem perfectCoinductionTorIndependentBaseChange :
    (∀ {A B T D : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing D]
      (f : A →+* B) (g : A →+* T) (b : B →+* D) (q : T →+* D),
      IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
        (CommRingCat.ofHom b) (CommRingCat.ofHom q) →
      DerivedCategory.IsPerfectRingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((restrictScalars f).obj (of B B))) →
      (∀ i : ℕ, 0 < i → IsZero (((Tor' (ModuleCat.{u} A) i).obj
        ((restrictScalars f).obj (of B B))).obj ((restrictScalars g).obj (of T T)))) →
      ∃ θ : (ordinaryCoinductionScalarPair b).F ⋙ (restrictScalars q).mapDerivedCategory ≅
          (restrictScalars f).mapDerivedCategory ⋙ (ordinaryCoinductionScalarPair g).F,
        CoinductionTensorNormalized f g b q (ordinaryCoinductionScalarPair g)
          (ordinaryCoinductionScalarPair b) θ ∧
        (∀ N : DerivedCategory (ModuleCat.{u} A),
          IsIso (coinductionScalarExchange f q (ordinaryCoinductionScalarPair g)
            (ordinaryCoinductionScalarPair b) θ N)) ∧
        (∀ N : DerivedCategory (ModuleCat.{u} A),
          (restrictScalars q).mapDerivedCategory.map
              (coinductionScalarExchange f q (ordinaryCoinductionScalarPair g)
                (ordinaryCoinductionScalarPair b) θ N) ≫
              (derivedCoinductionAdjunction q).counit.app
                ((ordinaryDerivedExtendScalars g).obj N) =
            θ.hom.app ((derivedCoinduction f).obj N) ≫
              (ordinaryDerivedExtendScalars g).map
                ((derivedCoinductionAdjunction f).counit.app N)) ∧
        (∀ (N M : DerivedCategory (ModuleCat.{u} A)) (v : N ⟶ M),
          (ordinaryDerivedExtendScalars b).map ((derivedCoinduction f).map v) ≫
              coinductionScalarExchange f q (ordinaryCoinductionScalarPair g)
                (ordinaryCoinductionScalarPair b) θ M =
            coinductionScalarExchange f q (ordinaryCoinductionScalarPair g)
                (ordinaryCoinductionScalarPair b) θ N ≫
              (derivedCoinduction q).map ((ordinaryDerivedExtendScalars g).map v)) ∧
        CoinductionPerfectHomFormula f g b q θ ∧
        CoinductionExchangeTower f g b q (ordinaryCoinductionScalarPair g)
          (ordinaryCoinductionScalarPair b) θ) ∧
    (∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B),
      DerivedCategory.IsPerfectRingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((restrictScalars f).obj (of B B))) →
      ∃ (eA : ordinaryDerivedExtendScalars (RingHom.id A) ≅ 𝟭 _)
        (eB : ordinaryDerivedExtendScalars (RingHom.id B) ≅ 𝟭 _)
        (θ : (ordinaryCoinductionScalarPair (RingHom.id B)).F ⋙
            (restrictScalars f).mapDerivedCategory ≅
          (restrictScalars f).mapDerivedCategory ⋙
            (ordinaryCoinductionScalarPair (RingHom.id A)).F),
        CoinductionIdentityScalarNormalized eA ∧ CoinductionIdentityScalarNormalized eB ∧
        CoinductionTensorNormalized f (RingHom.id A) (RingHom.id B) f
          (ordinaryCoinductionScalarPair (RingHom.id A))
          (ordinaryCoinductionScalarPair (RingHom.id B)) θ ∧
        ∀ N : DerivedCategory (ModuleCat.{u} A),
          coinductionScalarExchange f f (ordinaryCoinductionScalarPair (RingHom.id A))
              (ordinaryCoinductionScalarPair (RingHom.id B)) θ N ≫
              (derivedCoinduction f).map (eA.hom.app N) =
            eB.hom.app ((derivedCoinduction f).obj N)) := by
  sorry

end ModuleCat
