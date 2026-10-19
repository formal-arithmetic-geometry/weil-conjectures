/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Sheaf.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.RingTheory.MiracleFlatness
import WeilConjectures.Mathlib.RingTheory.Flat.Localization
import Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen

/-! # Parameter tuples and germs of flat quasi-finite charts

Source: SGA 4, Exposé XVIII, Lemma 2.6, p. 552, first proof paragraph;
Stacks Project, Tags 00R4, 01TH, 01TI, 00RC
(blueprint: lem-pur-parameter-chart-germ-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Prescribed coordinate sections define a flat quasi-finite chart near a closed point
exactly when their centered germs form a system of parameters. The chart neighbourhood
can be affine, and the parameter-ideal condition is equivalent to its quotient being
nonzero of dimension zero. The explicit equations define the residue-field identification,
the coordinate map `f`, its values `a`, its centered germs `t`, and their generated ideal `I`.

Source: SGA 4, Exposé XVIII, Lemma 2.6, p. 552, first proof paragraph;
Stacks Project, Tags 00R4, 01TH, 01TI, 00RC.
(blueprint: lem-pur-parameter-chart-germ-criterion)

Proof:
1. Choose an affine basic neighbourhood W of x inside V. Its section ring B is finite
type over k: localize a finitely generated algebra and add the inverted element to its
generators. Identify the stalk with B_q, where q corresponds to x. The given sections
define the finite-type map P = k[T_1,...,T_d] to B. Use the pointwise affine-pair
criterion to obtain local finite type of the coordinate morphism; B is Noetherian.
2. The inverse image of q is n = (T_i-a_i), by the evaluation-kernel calculation.
The ring A = P_n is regular Noetherian local of dimension d. The induced local map
A to R = B_q sends T_i-a_i to t_i, so its closed-fibre ideal is I.
3. The affine fibre ring is B tensor_P k = B/(f_i-a_i). Localizing at the point x
gives R/I, compatibly with all germs. This quotient is nonzero since I is contained
in the maximal ideal and the quotient surjects onto k.
4. Primes of R/I correspond to primes of R containing I, all contained in m.
The radical-intersection formula shows radical I = m iff this is the singleton m,
which is equivalent to dimension zero of the nonzero quotient.
5. Apply the ring quasi-finiteness/zero-fibre-dimension criterion, the closed-point
dimension/local-ring theorem, and the independence of affine pairs (via isolation
in the fibre). Thus quasi-finiteness at x is equivalent to dimension zero of R/I.
6. A flat quasi-finite neighbourhood gives radical I = m by steps 4 and 5.
The flat local dimension formula gives dim R = dim A + dim(R/I) = d.
7. Conversely, the parameter-ideal condition gives a zero-dimensional closed fibre
and dim R = dim A + dim(R/I). Miracle flatness applies: A is regular Noetherian
local, and R is Noetherian local Cohen--Macaulay. This gives flatness at x, while
step 5 gives quasi-finiteness there.
8. Use flatness over a localization to regard B_q as flat over P. The Noetherian
flat-locus neighbourhood theorem supplies a basic neighbourhood where all B_q'
are flat over P, hence over the corresponding localizations of P. The affine-stalk
identifications then give flatness of the coordinate map throughout that open.
9. Intersect with the open quasi-finite locus and choose a further affine basic
neighbourhood U. Its points remain isolated in their fibres. Its coordinate ring
is finite type over P, and its Noetherian topology makes the morphism quasi-compact.
It is therefore quasi-finite and flat. All sections are only restricted, preserving
the original germs and values. For d = 0 the tuple is empty, P = A = k and I = 0;
the same argument applies without reducedness or separability assumptions. -/
theorem flat_quasiFinite_parameterChart_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    (x : X) (hx : x ∈ closedPoints X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hCM : (IsLocalRing.depth (R := X.presheaf.stalk x) (X.presheaf.stalk x) :
      WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (e : X.residueField x ≃+* k)
    (he : ∀ c : k,
      e (X.Γevaluation x ((X ↘ Spec (CommRingCat.of k)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) = c)
    (d : ℕ) (V : X.Opens) (hxV : x ∈ V)
    (s : ULift.{u} (Fin d) → Γ(X, V))
    (f : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)))
    (hf : f = AffineSpace.homOfVector (V.ι ≫ X ↘ Spec (CommRingCat.of k))
      (fun i ↦ V.topIso.inv (s i)))
    (a : ULift.{u} (Fin d) → k)
    (ha : ∀ i, a i = e (X.evaluation V x hxV (s i)))
    (t : ULift.{u} (Fin d) → X.presheaf.stalk x)
    (ht : ∀ i, t i = X.presheaf.germ V x hxV (s i) -
      X.presheaf.germ ⊤ x trivial ((X ↘ Spec (CommRingCat.of k)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (a i))))
    (I : Ideal (X.presheaf.stalk x)) (hI : I = Ideal.span (Set.range t)) :
    (∀ i, t i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
    ((∃ (U : X.Opens) (_hxU : x ∈ U) (hUV : U ≤ V),
      (X.homOfLE hUV ≫ f).IsQuasiFinite ∧ Flat (X.homOfLE hUV ≫ f)) ↔
      ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
        I.radical = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
    ((∃ (U : X.Opens) (_hxU : x ∈ U) (hUV : U ≤ V),
      IsAffineOpen U ∧ (X.homOfLE hUV ≫ f).IsQuasiFinite ∧
        Flat (X.homOfLE hUV ≫ f)) ↔
      ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
        I.radical = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
    ((ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
      I.radical = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ↔
      ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
        Nontrivial ((X.presheaf.stalk x) ⧸ I) ∧
        ringKrullDim ((X.presheaf.stalk x) ⧸ I) = 0) := by
  sorry

end AlgebraicGeometry
