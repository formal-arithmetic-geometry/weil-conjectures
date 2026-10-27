/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.Algebra.Homology.TorIndependentKFlatResolutionTensor
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso
import Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction
import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Sheaf.Algebra.Homology.PerfectRingHomScalarExtension
import Sheaf.Algebra.Homology.PerfectRingHomKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.RingBoundedProjectiveExtension
import Sheaf.CategoryTheory.SystemScalarCoherence
import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Tor-independent exchange for perfect derived coinduction

Source: Stacks Project, dualizing.tex, equation-base-change and Tag 0BZP;
more-algebra.tex, Tags 0661 and 0A6A.
(blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange).
The scalar pairs below are presentations of the existing total left derived functors,
with their universal counits. All comparison normalizations are equations in derived
categories, including on unbounded complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wR wS wA wT wB wV wC

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- A presentation of derived extension by its universal counit. This is the ordinary
module specialization of the fixed-second-factor functor, with the coefficient ring
in degree zero; it retains independently chosen localization universes.
Source: Stacks 06Y6 (blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange). -/
structure CoinductionScalarPair {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{u} S)] (f : R →+* S) where
  F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S)
  counit : DerivedCategory.Q ⋙ F ⟶
    (extendScalars f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : F.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
  computes : ∀ E : CochainComplex (ModuleCat.{u} R) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat E →
      IsIso (counit.app E)

/-- The ordinary balancing map is fixed on every pure tensor. Requiring the equation
for every such isomorphism avoids making any choice of an ordinary tensor model.
Source: Stacks 0661 (blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange). -/
def CoinductionTensorNormalized
    {R A T B : Type u} [CommRing R] [CommRing A] [CommRing T] [CommRing B]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wT} (ModuleCat.{u} T)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (f : R →+* A) (g : R →+* T) (a : A →+* B) (b : T →+* B)
    (dR : CoinductionScalarPair g) (dA : CoinductionScalarPair a)
    (θ : dA.F ⋙ (restrictScalars b).mapDerivedCategory ≅
      (restrictScalars f).mapDerivedCategory ⋙ dR.F) : Prop :=
  ∀ (E : CochainComplex (ModuleCat.{u} A) ℤ),
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat E →
    ∀ e : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj E) ≅
      ((restrictScalars b).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars a).mapHomologicalComplex (.up ℤ)).obj E),
      (∀ (n : ℤ) (t : T) (x : E.X n),
        e.hom.f n (t ⊗ₜ[R,g] x) = b t ⊗ₜ[A,a] x) →
      θ.inv.app (DerivedCategory.Q.obj E) ≫
          (restrictScalars b).mapDerivedCategory.map (dA.counit.app E) ≫
          (restrictScalars b).mapDerivedCategoryFactors.hom.app _ =
        dR.F.map ((restrictScalars f).mapDerivedCategoryFactors.hom.app E) ≫
          dR.counit.app _ ≫ DerivedCategory.Q.map e.hom

/-- The counit mate, with its actual algebra action, in D(B).
Source: dualizing.tex, equation-base-change
(blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange). -/
def coinductionScalarExchange
    {R A T B : Type u} [CommRing R] [CommRing A] [CommRing T] [CommRing B]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wT} (ModuleCat.{u} T)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (f : R →+* A) (b : T →+* B)
    {g : R →+* T} {a : A →+* B}
    (dR : CoinductionScalarPair g) (dA : CoinductionScalarPair a)
    (θ : dA.F ⋙ (restrictScalars b).mapDerivedCategory ≅
      (restrictScalars f).mapDerivedCategory ⋙ dR.F)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    dA.F.obj ((derivedCoinduction f).obj M) ⟶
      (derivedCoinduction b).obj (dR.F.obj M) :=
  ((derivedCoinductionAdjunction b).homEquiv _ _)
    (θ.hom.app ((derivedCoinduction f).obj M) ≫
      dR.F.map ((derivedCoinductionAdjunction f).counit.app M))

/-- The canonical Hom model of underlying derived coinduction, fixed by the
K-injective model and precomposition with the augmentation. The three chain maps
in the equation have their entire coordinate formulas specified.
Source: Stacks 0A71 and 0A6A
(blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange). -/
def CoinductionHomModel
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (f : R →+* A) (E Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (s : E ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((restrictScalars f).obj (of A A)))
    (e : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex E Q) ≅
      (restrictScalars f).mapDerivedCategory.obj
        ((derivedCoinduction f).obj (DerivedCategory.Q.obj Q))) : Prop :=
  ∀ (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] (l : Q ⟶ I),
    ∃ (j : CochainComplex.moduleHomComplex E Q ⟶ CochainComplex.moduleHomComplex E I)
      (p : CochainComplex.moduleHomComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            ((restrictScalars f).obj (of A A))) I ⟶
        CochainComplex.moduleHomComplex E I)
      (k : ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
          ((coinductionComplexFunctor f).obj I) ≅
        CochainComplex.moduleHomComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            ((restrictScalars f).obj (of A A))) I),
      (∀ (n r t : ℤ) (h : r + n = t)
        (z : (CochainComplex.moduleHomComplex E Q).X n) (x : E.X r),
        ((j.f n z).v r t h) x = l.f t ((z.v r t h) x)) ∧
      (∀ (n r t : ℤ) (h : r + n = t)
        (z : (CochainComplex.moduleHomComplex
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            ((restrictScalars f).obj (of A A))) I).X n) (x : E.X r),
        ((p.f n z).v r t h) x = (z.v r t h) (s.f r x)) ∧
      (∀ (n : ℤ) (z : ((coinductionComplexFunctor f).obj I).X n)
        (x : ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          ((restrictScalars f).obj (of A A))).X 0),
        ((k.hom.f n z).v 0 n (zero_add n)) x =
          (CoextendScalars.equiv f (I.X n) z)
            ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
              ((restrictScalars f).obj (of A A))).hom x)) ∧
      DerivedCategory.Q.map j =
        e.hom ≫ (restrictScalars f).mapDerivedCategory.map
          ((derivedCoinduction f).map (DerivedCategory.Q.map l)) ≫
        (restrictScalars f).mapDerivedCategory.map (derivedCoinductionModel f I).hom ≫
        (restrictScalars f).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map k.hom ≫ DerivedCategory.Q.map p

/-- The normalized Hom scalar map on all homogeneous coordinates; for degree-zero
L it is exactly `(h tensor t)(z tensor s) = ts(h(z) tensor 1)` after tensor flips.
Source: Stacks, equation-base-change-RHom and Tag 0A6A
(blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange). -/
def CoinductionHomScalarFormula
    {R T : Type u} [CommRing R] [CommRing T] (g : R →+* T)
    (E Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (χ : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.moduleHomComplex E Q) ⟶
      CochainComplex.moduleHomComplex
        (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E)
        (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q)) : Prop :=
  ∀ (n r t : ℤ) (h : r + n = t)
    (z : (CochainComplex.moduleHomComplex E Q).X n) (x : E.X r) (a b : T),
    ((χ.f n (a ⊗ₜ[R,g] z)).v r t h) (b ⊗ₜ[R,g] x) =
      (a * b) ⊗ₜ[R,g] ((z.v r t h) x)

/-- The localized coordinate formula, for every augmented bounded finite projective
resolution and every finite projective module in degree zero. Both Hom identifications
are normalized by K-injective comparison, so the equation fixes the actual map.
Source: Stacks 0BZP and 0A6A
(blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange). -/
def CoinductionExchangeResolutionFormula
    {R A T B : Type u} [CommRing R] [CommRing A] [CommRing T] [CommRing B]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wT} (ModuleCat.{u} T)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (f : R →+* A) (g : R →+* T) (a : A →+* B) (b : T →+* B)
    (dR : CoinductionScalarPair g) (dA : CoinductionScalarPair a)
    (θ : dA.F ⋙ (restrictScalars b).mapDerivedCategory ≅
      (restrictScalars f).mapDerivedCategory ⋙ dR.F) : Prop :=
  ∀ (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (s : E ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((restrictScalars f).obj (of A A))),
    QuasiIso s →
    (∃ i j : ℤ, E.IsStrictlyGE i ∧ E.IsStrictlyLE j) →
    (∀ n : ℤ, Module.Finite R (E.X n) ∧ Module.Projective R (E.X n)) →
    ∀ (L : ModuleCat.{u} R), Module.Finite R L → Module.Projective R L →
    ∀ Q : CochainComplex (ModuleCat.{u} R) ℤ,
    Q = (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj L →
    ∃ (sT : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E ⟶
          (CochainComplex.singleFunctor (ModuleCat.{u} T) 0).obj
            ((restrictScalars b).obj (of B B)))
      (χ : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.moduleHomComplex E Q) ⟶
        CochainComplex.moduleHomComplex
          (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E)
          (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q))
      (eR : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex E Q) ≅
        (restrictScalars f).mapDerivedCategory.obj
          ((derivedCoinduction f).obj (DerivedCategory.Q.obj Q)))
      (eT : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex
          (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E)
          (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
        (restrictScalars b).mapDerivedCategory.obj ((derivedCoinduction b).obj
          (DerivedCategory.Q.obj (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q)))),
      QuasiIso sT ∧
      (∀ (t : T) (x : E.X 0),
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((restrictScalars b).obj (of B B))).hom (sT.f 0 (t ⊗ₜ[R,g] x)) =
        b t * a ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((restrictScalars f).obj (of A A))).hom (s.f 0 x))) ∧
      CoinductionHomScalarFormula g E Q χ ∧ CoinductionHomModel f E Q s eR ∧
      CoinductionHomModel b
        (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E)
        (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q) sT eT ∧
      dR.F.map eR.hom ≫ θ.inv.app ((derivedCoinduction f).obj (DerivedCategory.Q.obj Q)) ≫
          (restrictScalars b).mapDerivedCategory.map
            (coinductionScalarExchange f b dR dA θ (DerivedCategory.Q.obj Q)) ≫
          (restrictScalars b).mapDerivedCategory.map
            ((derivedCoinduction b).map (dR.counit.app Q)) =
        dR.counit.app (CochainComplex.moduleHomComplex E Q) ≫
          DerivedCategory.Q.map χ ≫ eT.hom ∧
      (∀ (E' : CochainComplex (ModuleCat.{u} R) ℤ)
        (s' : E' ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          ((restrictScalars f).obj (of A A))) (v : E' ⟶ E),
        QuasiIso s' → (∃ i j : ℤ, E'.IsStrictlyGE i ∧ E'.IsStrictlyLE j) →
        (∀ n : ℤ, Module.Finite R (E'.X n) ∧ Module.Projective R (E'.X n)) →
        v ≫ s = s' →
        ∀ χ' : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj
            (CochainComplex.moduleHomComplex E' Q) ⟶
          CochainComplex.moduleHomComplex
            (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj E')
            (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q),
        CoinductionHomScalarFormula g E' Q χ' →
        ((extendScalars g).mapHomologicalComplex (.up ℤ)).map
            (CochainComplex.moduleHomPrecomp Q v) ≫ χ' =
          χ ≫ CochainComplex.moduleHomPrecomp
            (((extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q)
            (((extendScalars g).mapHomologicalComplex (.up ℤ)).map v))

/-- Derived scalar associativity with its ordinary normalization, in the direction
successive to direct. Source: Stacks 06Y6
(blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange). -/
def CoinductionScalarCompNormalized
    {R S V : Type u} [CommRing R] [CommRing S] [CommRing V]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{u} S)]
    [HasDerivedCategory.{wT} (ModuleCat.{u} V)]
    (f : R →+* S) (g : S →+* V)
    (d : CoinductionScalarPair f) (e : CoinductionScalarPair g)
    (h : CoinductionScalarPair (g.comp f)) (α : d.F ⋙ e.F ≅ h.F) : Prop :=
  ∀ E : CochainComplex (ModuleCat.{u} R) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat E →
    α.hom.app (DerivedCategory.Q.obj E) ≫ h.counit.app E =
      e.F.map (d.counit.app E) ≫
        e.counit.app (((extendScalars f).mapHomologicalComplex (.up ℤ)).obj E) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (extendScalarsComp f g) (.up ℤ)).inv.app E)

/-- The direct and successive counit mates agree under canonical scalar associators.
All three tensor comparisons are required to have their representative normalization;
no arbitrary comparison can satisfy this predicate by a choice of associators.
Source: dualizing.tex equation-base-change; scalar associativity of 06Y6
(blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange). -/
def CoinductionExchangeTower
    {R A T B : Type u} [CommRing R] [CommRing A] [CommRing T] [CommRing B]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wT} (ModuleCat.{u} T)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (f : R →+* A) (g : R →+* T) (a : A →+* B) (b : T →+* B)
    (dR : CoinductionScalarPair g) (dA : CoinductionScalarPair a)
    (θ : dA.F ⋙ (restrictScalars b).mapDerivedCategory ≅
      (restrictScalars f).mapDerivedCategory ⋙ dR.F) : Prop :=
  ∀ (V C : Type u) [CommRing V] [CommRing C]
    [HasDerivedCategory.{wV} (ModuleCat.{u} V)]
    [HasDerivedCategory.{wC} (ModuleCat.{u} C)]
    (t : T →+* V) (j : B →+* C) (c : V →+* C),
    IsPushout (CommRingCat.ofHom b) (CommRingCat.ofHom t)
      (CommRingCat.ofHom j) (CommRingCat.ofHom c) →
    ∀ (dT : CoinductionScalarPair t) (dB : CoinductionScalarPair j)
      (dR' : CoinductionScalarPair (t.comp g)) (dA' : CoinductionScalarPair (j.comp a)),
    Nonempty (dR'.F.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((restrictScalars f).obj (of A A))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} V) 0).obj
        ((restrictScalars c).obj (of C C))) →
    ∃ (eR : dR.F ⋙ dT.F ≅ dR'.F) (eA : dA.F ⋙ dB.F ≅ dA'.F),
    CoinductionScalarCompNormalized g t dR dT dR' eR ∧
    CoinductionScalarCompNormalized a j dA dB dA' eA ∧
    ∃ (θ' : dA'.F ⋙ (restrictScalars c).mapDerivedCategory ≅
        (restrictScalars f).mapDerivedCategory ⋙ dR'.F)
      (θ'' : dB.F ⋙ (restrictScalars c).mapDerivedCategory ≅
        (restrictScalars b).mapDerivedCategory ⋙ dT.F),
    CoinductionTensorNormalized f (t.comp g) (j.comp a) c dR' dA' θ' ∧
    CoinductionTensorNormalized b t j c dT dB θ'' ∧
    ∀ M : DerivedCategory (ModuleCat.{u} R),
      eA.inv.app ((derivedCoinduction f).obj M) ≫
          dB.F.map (coinductionScalarExchange f b dR dA θ M) ≫
          coinductionScalarExchange b c dT dB θ'' (dR.F.obj M) ≫
          (derivedCoinduction c).map (eR.hom.app M) =
        coinductionScalarExchange f c dR' dA' θ' M

/-- The inverse tensor comparison exists with the Stacks representative normalization;
its counit mate is natural on all derived morphisms, and is invertible for a perfect
source algebra and an arbitrary, possibly unbounded, target.
Source: Stacks 0661, dualizing.tex equation-base-change and 0BZP
(blueprint: lem-sfb-perfect-coinduction-tor-independent-exchange).

Proof: Choose an A-K-flat model and an R-K-flat resolution of its restriction.
By lem-pc-tor-independent-kflat-resolution-tensor and lem-pc-base-tensor-ordinary-iso,
tensoring that resolution with T is a quasi-isomorphism, followed by the balancing
map t tensor x to (1 tensor t) tensor x. Localize and invert this comparison.
The universal scalar counits make the resulting theta natural and give exactly
CoinductionTensorNormalized. Apply lem-trf-derived-coinduction-adjunction: gamma
is the adjunct of theta followed by scalar extension of evaluation at one. The
adjunction gives the displayed counit equation and naturality on derived morphisms.
Forget to T. The explicit inverse Hom correspondence x to (a to g(ax)) of
lem-trf-algebraic-shriek-derived-hom-adjunction identifies this mate with the
normalized Hom-complex comparison of def-pc-perfect-rhom-base-change-map.
For a bounded finite projective model F of A and a K-flat model of M,
lem-pc-perfect-ring-hom-kflat and lem-pc-perfect-ring-hom-scalar-extension make
that comparison an isomorphism. Restriction is conservative by
lem-trf-derived-coinduction-adjunction, so gamma is invertible in D(A tensor_R T).
For degree-zero finite projective L the localized comparison is the coordinate
map chi. For a map of augmented resolutions, both composites evaluated on
(a tensor h, b tensor x) are ab tensor h(v(x)); the two chain maps agree.
This gives the displayed precomposition square, and localization preserves it.
For a further scalar extension, derived tensor associativity identifies the
second tensor algebra with the direct tensor algebra; Tor independence for the
first and direct squares implies it for the second square. The scalar associators
are fixed by ordinary tensor associativity, as in lem-pur-system-scalar-coherence.
Transpose the successive gamma composite through the final coinduction adjunction.
Substitute its counit equation twice; naturality and the normalized associators
reduce it to the transpose of the direct gamma. Injectivity of the adjunction
bijection gives the tower equation, including identity scalar extension.
No flatness of T, surjectivity, Noetherianity or boundedness of M is used. -/
theorem perfectCoinduction_torIndependent_exchange
    {R A T B : Type u} [CommRing R] [CommRing A] [CommRing T] [CommRing B]
    [Algebra R A] [Algebra R T]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wT} (ModuleCat.{u} T)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (a : A →+* B) (b : T →+* B)
    (eB : (A ⊗[R] T) ≃+* B)
    (ha : a = eB.toRingHom.comp (algebraMap A (A ⊗[R] T)))
    (hb : b = eB.toRingHom.comp
      (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T).toRingHom)
    (dR : CoinductionScalarPair (algebraMap R T)) (dA : CoinductionScalarPair a)
    (hTor : Nonempty
      (dR.F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (of R A)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} T) 0).obj
          ((restrictScalars b).obj (of B B)))) :
    ∃ θ : dA.F ⋙ (restrictScalars b).mapDerivedCategory ≅
        (restrictScalars (algebraMap R A)).mapDerivedCategory ⋙ dR.F,
      CoinductionTensorNormalized (algebraMap R A) (algebraMap R T) a b dR dA θ ∧
      (∀ (M : DerivedCategory (ModuleCat.{u} R)),
        (restrictScalars b).mapDerivedCategory.map
            (coinductionScalarExchange (algebraMap R A) b dR dA θ M) ≫
            (derivedCoinductionAdjunction b).counit.app (dR.F.obj M) =
          θ.hom.app ((derivedCoinduction (algebraMap R A)).obj M) ≫
            dR.F.map ((derivedCoinductionAdjunction (algebraMap R A)).counit.app M)) ∧
      (∀ (M N : DerivedCategory (ModuleCat.{u} R)) (v : M ⟶ N),
        dA.F.map ((derivedCoinduction (algebraMap R A)).map v) ≫
            coinductionScalarExchange (algebraMap R A) b dR dA θ N =
          coinductionScalarExchange (algebraMap R A) b dR dA θ M ≫
            (derivedCoinduction b).map (dR.F.map v)) ∧
      CoinductionExchangeResolutionFormula (algebraMap R A) (algebraMap R T)
        a b dR dA θ ∧
      CoinductionExchangeTower (algebraMap R A) (algebraMap R T) a b dR dA θ ∧
      (DerivedCategory.IsPerfectRingComplex
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (of R A)) →
        ∀ M : DerivedCategory (ModuleCat.{u} R),
          IsIso (coinductionScalarExchange (algebraMap R A) b dR dA θ M)) := by
  sorry

end ModuleCat
