/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.TensorPower.Symmetric

import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import Sheaf.AlgebraicGeometry.ProperReducedGlobalSectionsProduct
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Numerical normal generation on a nodal curve

Source: Franciosi--Tenni, The canonical ring of a 3-connected curve (2014),
Section 4, Theorem 4.2, printed p. 49
(blueprint: lem-sfb-nodal-numerical-section-multiplication).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace AlgebraicGeometry

/-- Numerical normal generation on a projective nodal curve.
Source: Franciosi--Tenni (2014), Theorem 4.2, printed p. 49
(blueprint: lem-sfb-nodal-numerical-section-multiplication).

The map is specified uniquely on all pure symmetric tensors. Its value is the
corresponding product of degree-one sections in the existing graded section ring,
evaluated in degree j. The right unitor identifies L with its first tensor power.

Proof plan (the ten steps of the DAG node):
1. Projectivity implies properness (lem-kun-projective-implies-proper), hence finite
   type and Noetherianness (def-weil-proper-morphism and
   lem-weil-pbc-finite-type-over-noetherian). Invertible sheaves are coherent by
   pqf-lem-coherent-ft-locnoeth. The same holds on closed subcurves by
   lem-weil-pbc-closed-immersion-proper and lem-weil-pbc-proper-composition.
   Use the module-sheaf cohomology long exact sequence from
   lem-weil-pbc-derived-functor-long-exact, with enough injectives from
   lem-weil-pbc-scheme-modules-enough-injectives and left exact sections from
   lem-sc-global-sections-left-exact.
2. On each connected reduced subcurve B, h0(O_B) = 1 by
   lem-weil-pbc-proper-reduced-algclosed-global-sections-product. Cohomology above
   dimension one vanishes by lem-sc-noetherian-cohomology-above-dimension, so
   p_a(B) = h1(O_B) is nonnegative. Degree additivity from
   lem-trf-curve-degree-tensor-additive shows that every positive tensor power of L
   retains the bound. A nonzero H1 of such a power would contradict that bound by
   lem-sfb-curve-ideal-h1-subcurve-obstruction with the empty test subscheme.
3. A closed point x has residue field k (lem-weil-pbc-closed-point-residue-field-base).
   Its intersection with any subcurve has length at most one. The same obstruction
   lemma gives H1(I_x tensor L) = 0. Tensor the ideal sequence
   (def-sbc-closed-immersion-ideal-sheaf) using lem-sc-ext-tensor-exact; its cohomology
   sequence makes evaluation onto the fibre at x surjective. Thus L is generated
   at every closed point. Its section space is finite dimensional by lem-pc-coherent-hi.
4. Choose s and its smooth reduced zero scheme S by
   lem-sfb-general-section-cluster-strict-bound. It supplies a section nonzero on
   every component and h0(I_T L) + h1(I_T L) < h0(L) for every nonempty T inside S.
5. If products V tensor V did not cover H0(S,L squared restricted to S),
   lem-sfb-cluster-product-obstruction would produce a nonempty T with the reverse
   inequality, since H1(L) = 0. For empty S the target is zero directly.
6. Locally s = a e with a a non-zero-divisor: it vanishes on no component of a
   reduced scheme. By def-pc-zero-scheme its zero ideal is (a). The sequence
   0 -> A --a--> A -> A/(a) -> 0 gives
   0 -> L --s--> L squared -> Q -> 0, where Q is the direct image of its
   restriction to S; Q has global sections H0(S,L squared restricted to S).
7. By Step 2 and the cohomology sequence, restriction of sections in degree two to
   S is onto with kernel s V. Step 5 expresses any such restriction by a sum of
   quadratic products. Subtract that sum and express the remainder as s c.
   Hence all sections in degree two are sums of quadratic products.
8. Choose t in V nonvanishing at the finite set S. Each forbidden condition is a
   proper linear hyperplane by Step 3. The algebraically closed field is infinite;
   the product of nonzero annihilating linear forms cannot vanish at every point
   of V. Thus a finite union of these hyperplanes does not exhaust V. The pair
   s,t generates L everywhere.
9. The pencil gives 0 -> L inverse -> O_X squared -> L -> 0 with maps
   c |-> (-t c,s c) and (a,b) |-> s a+t b. Locally one coefficient is a unit,
   which directly proves injectivity and identifies the kernel. Tensoring gives
   0 -> L power (n-1) -> (L power n) squared -> L power (n+1) -> 0.
   For n >= 2 Step 2 kills H1 of the left term, so every degree-(n+1) section
   is s u+t v for degree-n sections u,v.
10. Induct on j: degree one is the identity and Step 7 handles degree two;
    Step 9 handles every subsequent degree by substituting the inductive product
    expressions for u,v. The section ring of def-sc-invertible-section-ring is
    commutative, so tensor multiplication descends to the symmetric power in every
    characteristic. Its values on pure tensors are exactly the displayed products.
    Pure symmetric tensors span (SymmetricPower.span_tprod_eq_top), which also proves
    uniqueness of the specified linear map. No factorial is inverted.
-/
theorem nodal_numerical_section_multiplication
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsHProjective f]
    [ConnectedSpace X] [IsReduced X] (hpure : X.IsPureDimension 1)
    (hnodal : ∀ x : X, x ∉ f.smoothLocus →
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)}),
        ∀ a : k,
          e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)
            (X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C a))
    (L : X.Modules) [L.IsInvertible]
    (hdegree : ∀ (B : Scheme.{u}) (i : B ⟶ X),
      IsClosedImmersion i → IsReduced B → Nonempty B →
      (∃ S : Set (Set X), S ⊆ irreducibleComponents X ∧ Set.range i = ⋃₀ S) →
      2 * (1 - @Scheme.Modules.eulerChar k _ B ⟨i ≫ f⟩
        (SheafOfModules.unit B.ringCatSheaf)) + 1 ≤
        @Scheme.Modules.degree k _ B ⟨i ≫ f⟩
          ((Scheme.Modules.tensorPullback i).obj L)) :
    ∀ j : ℕ, 1 ≤ j →
      ∃! μ : SymmetricPower k (ULift.{u} (Fin j))
          ((ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
              (L.val.obj (Opposite.op ⊤))) →ₗ[k]
          ((ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
              ((L.tensorPow j).val.obj (Opposite.op ⊤))),
        (∀ s : ULift.{u} (Fin j) →
            ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
                (L.val.obj (Opposite.op ⊤))),
          μ (SymmetricPower.tprod k s) =
            (∏ i : ULift.{u} (Fin j),
              (DirectSum.of (Scheme.Modules.SectionRingComponent L) 1
                ((ρ_ L).inv.app ⊤ (s i)) : Scheme.Modules.InvertibleSectionRing L)) j) ∧
        Function.Surjective μ := by
  sorry

end AlgebraicGeometry
