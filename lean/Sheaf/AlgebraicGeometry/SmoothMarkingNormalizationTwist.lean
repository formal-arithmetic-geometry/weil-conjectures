/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.Curve

public import Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Smooth marking divisors and normalization of their adjunction twist

Source: Stacks Project, Divisors, Tags 067R, 062T, 0C4U; Curves, Tags 0C1A and 0BS6;
normalization adjunction as recorded in lem-trf-nodal-normalization-adjunction.
(blueprint: lem-sfb-smooth-marking-normalization-twist)

The auxiliary predicates spell out this lemma's hypotheses and canonical comparisons.
No dualizing module, stability datum, or modification map is constructed here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The actual product of the section ideals, including the unit ideal for no sections.
Source: Stacks, Divisors, Tags 01WT and 067R.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def smoothMarkingIdeal {X S : Scheme.{u}} {n : ℕ} (a : Fin n → (S ⟶ X)) :
    X.IdealSheafData :=
  ∏ i : Fin n, (a i).ker

/-- The expression `K ⊗ O(D)` for the actual product ideal of the markings.
Source: Stacks, Divisors, Tags 01WT and 01WU.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def smoothMarkingTwist {X S : Scheme.{u}} {n : ℕ} (K : X.Modules)
    (a : Fin n → (S ⟶ X)) : X.Modules :=
  K ⊗ Scheme.Modules.dual (smoothMarkingIdeal a).toModules

/-- A nonempty reduced pure one-dimensional geometric fibre, with the node condition
only at nonsmooth closed points. The equation on constants makes the completed-ring
isomorphism an isomorphism over the geometric field, without selecting a scalar action.
Source: Stacks, Curves, Tags 0C47 and 0C4D.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def IsSmoothMarkingGeometricFibre {Ω : Type u} [Field Ω] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation p] : Prop :=
  Nonempty Y ∧ IsReduced Y ∧ Y.IsPureDimension 1 ∧
    ∀ y : Y, IsClosed ({y} : Set Y) → y ∉ p.smoothLocus →
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y) ≃+*
            (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span
              {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) * MvPowerSeries.X 1}),
        ∀ c : Ω, e (AdicCompletion.of (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y) (Y.presheaf.germ ⊤ y (Set.mem_univ y)
            (p.appTop ((Scheme.ΓSpecIso (.of Ω)).inv c)))) =
              Ideal.Quotient.mk _ (MvPowerSeries.C c)

/-- The supplied identification with the canonical adjunction line of a geometric fibre.
The system and its determinant normalization are the recorded dependency's interface.
Source: Stacks, Duality, Tags 0B6V and 0E2Y, canonical adjunction construction.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
structure SmoothMarkingFibreAdjunction {Ω : Type u} [Field Ω] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of Ω)) (K : Y.Modules) where
  system : FlatLCIAdjunctionSystem p 1
  normalized : system.IsNormalized
  identification : K ≅ system.line (FlatLCIBaseChange.identity p)

/-- A Cartier ideal frame together with its inverse dual frame. Evaluation equals one,
so this fixes the dual frame, including on nonreduced bases.
Source: Stacks, Divisors, Tag 01WU, dual of a Cartier ideal generator.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def IsSmoothMarkingDualFrame {X : Scheme.{u}} (D : X.IdealSheafData) (U : X.Opens)
    (t : Γ(D.toModules, U)) (v : Γ(Scheme.Modules.dual D.toModules, U)) : Prop :=
  Scheme.Modules.IsFreeGenerator t ∧
    PresheafOfModules.homObjEvalId D.toModules.val
      (SheafOfModules.unit X.ringCatSheaf).val U v t = Scheme.Modules.unitSectionsEquiv U 1

/-- The canonical comparison sends `s ⊗ t⁻¹` to `kappa(1 ⊗ s) ⊗ (g#t)⁻¹`.
The ideal inclusion equation specifies the actual pulled generator. The formula on every
open fixes the map and expresses preservation of tensor products of local sections.
Source: Stacks, Divisors, Tag 0C4U, dual-frame calculation.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def IsSmoothMarkingTwistComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : X.Modules) (N : Y.Modules) (kappa : (Scheme.Modules.tensorPullback g).obj K ≅ N)
    (D : X.IdealSheafData) (E : Y.IdealSheafData)
    (e : (Scheme.Modules.tensorPullback g).obj (K ⊗ Scheme.Modules.dual D.toModules) ≅
      N ⊗ Scheme.Modules.dual E.toModules) : Prop :=
  ∀ (U : X.Opens) (s : Γ(K, U))
    (t : Γ(D.toModules, U)) (v : Γ(Scheme.Modules.dual D.toModules, U))
    (t' : Γ(E.toModules, g ⁻¹ᵁ U))
    (v' : Γ(Scheme.Modules.dual E.toModules, g ⁻¹ᵁ U)),
    IsSmoothMarkingDualFrame D U t v →
    IsSmoothMarkingDualFrame E (g ⁻¹ᵁ U) t' v' →
    E.toModulesι.app (g ⁻¹ᵁ U) t' =
      Scheme.Modules.unitSectionsEquiv (g ⁻¹ᵁ U)
        (g.app U ((Scheme.Modules.unitSectionsEquiv U).symm (D.toModulesι.app U t))) →
    e.hom.app (g ⁻¹ᵁ U)
        (Scheme.Modules.tensorPullbackSection g (K ⊗ Scheme.Modules.dual D.toModules) U
          (Scheme.Modules.tmulSection s v)) =
      Scheme.Modules.tmulSection
        (kappa.hom.app (g ⁻¹ᵁ U) (Scheme.Modules.tensorPullbackSection g K U s)) v'

/-- Composition of dual-frame comparisons. The final transport is exactly `comap_comp`;
the tensor-pullback comparison is fixed by its section-normalized adjunction. Together
with existence and uniqueness, this is the composition compatibility in the statement.
Source: Stacks, Divisors, Tag 0C4U, composition of ring maps on Cartier generators.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def SmoothMarkingTwistComposition {X S : Scheme.{u}} (f : X ⟶ S) (K : X.Modules)
    (D : X.IdealSheafData) : Prop :=
  ∀ (Y Z T R : Scheme.{u}) (p : Y ⟶ T) (q : Z ⟶ R)
    (g : Y ⟶ X) (b : T ⟶ S) (h : Z ⟶ Y) (c : R ⟶ T)
    (eg : (Scheme.Modules.tensorPullback g).obj (K ⊗ Scheme.Modules.dual D.toModules) ≅
      (Scheme.Modules.tensorPullback g).obj K ⊗ Scheme.Modules.dual (D.comap g).toModules)
    (eh : (Scheme.Modules.tensorPullback h).obj
        ((Scheme.Modules.tensorPullback g).obj K ⊗ Scheme.Modules.dual (D.comap g).toModules) ≅
      (Scheme.Modules.tensorPullback h).obj ((Scheme.Modules.tensorPullback g).obj K) ⊗
        Scheme.Modules.dual ((D.comap g).comap h).toModules),
    IsPullback g p f b → IsPullback h q p c →
    IsSmoothMarkingTwistComparison g K _ (Iso.refl _) D (D.comap g) eg →
    IsSmoothMarkingTwistComparison h _ _ (Iso.refl _) (D.comap g) ((D.comap g).comap h) eh →
    IsSmoothMarkingTwistComparison (h ≫ g) K _ (Iso.refl _) D (D.comap (h ≫ g))
      ((Scheme.Modules.tensorPullbackSectionComp h g).app
          (K ⊗ Scheme.Modules.dual D.toModules) ≪≫
        (Scheme.Modules.tensorPullback h).mapIso eg ≪≫ eh ≪≫
          ((Scheme.Modules.tensorPullbackSectionComp h g).symm.app K ⊗ᵢ
            eqToIso (congrArg (fun I : Z.IdealSheafData ↦ Scheme.Modules.dual I.toModules)
              (D.comap_comp h g).symm)))

/-- Naturality under family isomorphisms carrying the supplied line and markings, allowing
any permutation of the markings. The same dual-frame formula fixes the natural comparison.
Source: Stacks, Divisors, Tag 0C4U, invariance of marking ideals.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def SmoothMarkingTwistNaturality {X S : Scheme.{u}} {n : ℕ} (f : X ⟶ S)
    (K : X.Modules)
    (a : Fin n → (S ⟶ X)) : Prop :=
  ∀ (Y T : Scheme.{u}) (p : Y ⟶ T) (b : Fin n → (T ⟶ Y)) (N : Y.Modules)
    (e : X ≅ Y) (q : S ≅ T)
    (perm : Equiv.Perm (Fin n))
    (kappa : (Scheme.Modules.tensorPullback e.hom).obj N ≅ K),
    e.hom ≫ p = f ≫ q.hom →
    (∀ i, a i ≫ e.hom = q.hom ≫ b (perm i)) →
    ∃! c : (Scheme.Modules.tensorPullback e.hom).obj (smoothMarkingTwist N b) ≅
        smoothMarkingTwist K a,
      IsSmoothMarkingTwistComparison e.hom N K kappa
        (smoothMarkingIdeal b) (smoothMarkingIdeal a) c

/-- The sum-of-divisors comparison takes the two inverse ideal frames to the inverse
of their product. This fixes the identification with `O(B+M)`, without arbitrary scalars.
Source: Stacks, Divisors, Tags 01WT and 01WU.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def IsSmoothMarkingSumComparison {C : Scheme.{u}} (A : C.Modules)
    (B M : C.IdealSheafData)
    (e : (A ⊗ Scheme.Modules.dual B.toModules) ⊗ Scheme.Modules.dual M.toModules ≅
      A ⊗ Scheme.Modules.dual (B * M).toModules) : Prop :=
  ∀ (U : C.Opens) (s : Γ(A, U))
    (tB : Γ(B.toModules, U)) (vB : Γ(Scheme.Modules.dual B.toModules, U))
    (tM : Γ(M.toModules, U)) (vM : Γ(Scheme.Modules.dual M.toModules, U))
    (tBM : Γ((B * M).toModules, U)) (vBM : Γ(Scheme.Modules.dual (B * M).toModules, U)),
    IsSmoothMarkingDualFrame B U tB vB → IsSmoothMarkingDualFrame M U tM vM →
    IsSmoothMarkingDualFrame (B * M) U tBM vBM →
    (Scheme.Modules.unitSectionsEquiv U).symm ((B * M).toModulesι.app U tBM) =
      (Scheme.Modules.unitSectionsEquiv U).symm (B.toModulesι.app U tB) *
        (Scheme.Modules.unitSectionsEquiv U).symm (M.toModulesι.app U tM) →
    e.hom.app U (Scheme.Modules.tmulSection (Scheme.Modules.tmulSection s vB) vM) =
      Scheme.Modules.tmulSection s vBM

open Classical in
/-- The component clauses, with `r` the canonical normalization followed by the component
inclusion. Branches and markings are reduced ideals with their actual supports, and the
comparison is the composite of the supplied fibre identification, normalized adjunction,
and the dual-frame marking and divisor-sum comparisons. All degrees are Euler degrees.
Source: Stacks, Curves, Tags 0C1A, 0BS6; normalization adjunction; Divisors, Tag 0C4U.
(blueprint: lem-sfb-smooth-marking-normalization-twist). -/
def SmoothMarkingNormalizationConclusion {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {Y C : Scheme.{u}} (p : Y ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation p] (r : C ⟶ Y) {n : ℕ}
    (a : Fin n → (Spec (.of Ω) ⟶ Y)) (K L : Y.Modules)
    (adj : SmoothMarkingFibreAdjunction p K)
    (e0 : L ≅ smoothMarkingTwist K a) : Prop :=
  IsProper (r ≫ p) ∧ Smooth (r ≫ p) ∧ IsConnectedCurve (r ≫ p) ∧
    (r ≫ p).genus = @Scheme.arithmeticGenus Ω _ C ⟨r ≫ p⟩ ∧
    ∃ B M : C.IdealSheafData,
      B.radical = B ∧ M.radical = M ∧ B.IsInvertible ∧ M.IsInvertible ∧
      (B.support : Set C) = {z | r z ∉ p.smoothLocus} ∧
      (M.support : Set C) = r ⁻¹' (⋃ i : Fin n, Set.range (a i)) ∧
      Disjoint (B.support : Set C) (M.support : Set C) ∧
      (B.support : Set C).Finite ∧ (M.support : Set C).Finite ∧
      (∀ z ∈ (B.support : Set C) ∪ (M.support : Set C),
        IsClosed ({z} : Set C) ∧
        ∃ s : Spec (.of Ω) ⟶ C, s ≫ (r ≫ p) = 𝟙 _ ∧ Set.range s = {z}) ∧
      (∀ i : Fin n, Nat.card {z : C // r z ∈ Set.range (a i)} =
        if (Set.range (a i) ∩ Set.range r).Nonempty then 1 else 0) ∧
      (∀ y : Y, y ∉ p.smoothLocus →
        Nat.card {z : C // r z = y} =
          if y ∈ Set.range r then
            if ∃ T ∈ irreducibleComponents Y, y ∈ T ∧ T ≠ Set.range r then 1 else 2
          else 0) ∧
      ∃ (eb : (Scheme.Modules.tensorPullback r).obj
          (adj.system.line (FlatLCIBaseChange.identity p)) ≅
            (r ≫ p).relativeDifferentials ⊗ Scheme.Modules.dual B.toModules)
        (em : (Scheme.Modules.tensorPullback r).obj (smoothMarkingTwist K a) ≅
          (Scheme.Modules.tensorPullback r).obj K ⊗ Scheme.Modules.dual M.toModules)
        (es : ((r ≫ p).relativeDifferentials ⊗ Scheme.Modules.dual B.toModules) ⊗
            Scheme.Modules.dual M.toModules ≅
          (r ≫ p).relativeDifferentials ⊗ Scheme.Modules.dual (B * M).toModules)
        (e : (Scheme.Modules.tensorPullback r).obj L ≅
          (r ≫ p).relativeDifferentials ⊗ Scheme.Modules.dual (B * M).toModules),
        IsNodalNormalizationAdjunctionComparison p adj.system r B eb ∧
        IsSmoothMarkingTwistComparison r K _ (Iso.refl _)
          (smoothMarkingIdeal a) M em ∧
        IsSmoothMarkingSumComparison (r ≫ p).relativeDifferentials B M es ∧
        @Scheme.Modules.degree Ω _ C ⟨r ≫ p⟩ ((Scheme.Modules.tensorPullback r).obj L) =
          (2 * (r ≫ p).genus : ℤ) - 2 + ((B.support : Set C).ncard : ℤ) +
            ((M.support : Set C).ncard : ℤ) ∧
        (∀ (N : C.Modules) (E F : C.IdealSheafData),
          E.IsInvertible → F.IsInvertible →
          Nonempty (N ≅ Scheme.Modules.dual E.toModules ⊗ F.toModules) →
          @Scheme.Modules.degree Ω _ C ⟨r ≫ p⟩ N =
            ((E.subschemeι ≫ r ≫ p).finrankΓ : ℤ) -
              ((F.subschemeι ≫ r ≫ p).finrankΓ : ℤ)) ∧
        e = (Scheme.Modules.tensorPullback r).mapIso e0 ≪≫ em ≪≫
          (((Scheme.Modules.tensorPullback r).mapIso adj.identification ≪≫ eb) ⊗ᵢ
            Iso.refl (Scheme.Modules.dual M.toModules)) ≪≫ es

/-- Smooth markings define a relative Cartier divisor and its canonical adjunction twist;
normalization gives differentials plus ambient nodal branches and marked points.

Source: Stacks, Divisors, Tags 067R, 062T, 0C4U; Curves, Tags 0C1A and 0BS6;
normalization adjunction from lem-trf-nodal-normalization-adjunction.
(blueprint: lem-sfb-smooth-marking-normalization-twist).

Proof, following all eight DAG steps:
1. Properness makes every section closed. Geometric purity gives relative dimension one
   on the smooth locus. The smooth-curve finite-flat Cartier criterion applies there;
   off the section the ideal is the unit ideal, so the Cartier property holds on X.
2. Disjoint section ideals are comaximal. Their product cuts out their disjoint union,
   finite flat over S with algebra A^n on Spec A. Its dual and its tensor with K are
   invertible. For n=0 the product is the unit ideal and the divisor is empty.
3. Relative Cartier pullback identifies the pulled divisor with the pulled sections;
   the tensor pullback comparison identifies the twisted line.
4. A local ideal generator t has inverse dual frame t^-1. Pullback sends this to
   (g#t)^-1; changing t by a unit changes both frames by its inverse. These maps glue,
   preserve tensor products, compose, and are invariant under marked-family isomorphisms.
5. The proper reduced geometric fibre is Noetherian. Over its perfect field its smooth
   locus is dense and contains every generic point. In pure dimension one every
   nonclosed point is generic. Nodal normalization adjunction therefore applies; it
   gives a proper smooth connected normalization, its reduced ambient-branch divisor,
   and the normalized adjunction comparison. Closed branch points are rational.
6. A smooth marked point has a domain local ring and lies on one component; remove the
   other finitely many components. Normalization is an isomorphism near it, so the
   pulled marking ideal is its reduced point ideal, with multiplicity one. Branch and
   marking supports are disjoint, and their reduced point sums are Cartier.
7. Compose the supplied fibre identification with branch adjunction and the marking
   comparison. The inverse product frame identifies O(B) tensor O(M) with O(B+M).
8. Riemann--Roch gives differential degree 2g-2 and identifies Euler and divisor degree.
   Each reduced rational branch or marking contributes one. Tensor degree additivity
   gives 2g-2+#B+#M, including the empty marking set. No positivity is asserted. -/
theorem smooth_marking_normalization_twist
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
      IsSmoothMarkingGeometricFibre (pullback.snd f t))
    (K : X.Modules) [K.IsInvertible]
    (adj : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S),
      SmoothMarkingFibreAdjunction (pullback.snd f t)
        ((Scheme.Modules.tensorPullback (pullback.fst f t)).obj K))
    (n : ℕ) (a : Fin n → (S ⟶ X)) (ha : ∀ i, a i ≫ f = 𝟙 S)
    (hdisjoint : Pairwise (fun i j : Fin n ↦ Disjoint (Set.range (a i)) (Set.range (a j))))
    (hsmooth : ∀ i, Set.range (a i) ⊆ (f.smoothLocus : Set X)) :
    (smoothMarkingIdeal a).IsRelativeEffectiveCartier f ∧
    (∃ e : (∐ fun _ : Fin n ↦ S) ≅ (smoothMarkingIdeal a).subscheme,
      e.hom ≫ (smoothMarkingIdeal a).subschemeι = Sigma.desc a) ∧
    (smoothMarkingTwist K a).IsInvertible ∧
    SmoothMarkingTwistComposition f K (smoothMarkingIdeal a) ∧
    SmoothMarkingTwistNaturality f K a ∧
    (∀ (T : Scheme.{u}) (b : T ⟶ S),
      (smoothMarkingIdeal a).comap (pullback.fst f b) =
        smoothMarkingIdeal (fun i ↦ f.baseChangeSection (a i) (ha i) b) ∧
      (smoothMarkingIdeal (fun i ↦ f.baseChangeSection (a i) (ha i) b)).IsRelativeEffectiveCartier
        (pullback.snd f b) ∧
      ∃! e : (Scheme.Modules.tensorPullback (pullback.fst f b)).obj
          (smoothMarkingTwist K a) ≅
        smoothMarkingTwist ((Scheme.Modules.tensorPullback (pullback.fst f b)).obj K)
          (fun i ↦ f.baseChangeSection (a i) (ha i) b),
        IsSmoothMarkingTwistComparison (pullback.fst f b) K _ (Iso.refl _)
          (smoothMarkingIdeal a)
          (smoothMarkingIdeal (fun i ↦ f.baseChangeSection (a i) (ha i) b)) e) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)
      (Z : Scheme.{u}) [IsIntegral Z] (i : Z ⟶ pullback f t) [IsClosedImmersion i],
      Set.range i ∈ irreducibleComponents (pullback (C := Scheme.{u}) f t) →
      ∃ e0 : (Scheme.Modules.tensorPullback (pullback.fst f t)).obj
          (smoothMarkingTwist K a) ≅
        smoothMarkingTwist ((Scheme.Modules.tensorPullback (pullback.fst f t)).obj K)
          (fun j ↦ f.baseChangeSection (a j) (ha j) t),
        IsSmoothMarkingTwistComparison (pullback.fst f t) K _ (Iso.refl _)
          (smoothMarkingIdeal a)
          (smoothMarkingIdeal (fun j ↦ f.baseChangeSection (a j) (ha j) t)) e0 ∧
        SmoothMarkingNormalizationConclusion (pullback.snd f t) (Z.fromNormalization ≫ i)
          (fun j ↦ f.baseChangeSection (a j) (ha j) t)
          ((Scheme.Modules.tensorPullback (pullback.fst f t)).obj K)
          ((Scheme.Modules.tensorPullback (pullback.fst f t)).obj (smoothMarkingTwist K a))
          (adj Ω t) e0) ∧
    (n = 0 → smoothMarkingIdeal a = ⊤) := by
  sorry

end AlgebraicGeometry
