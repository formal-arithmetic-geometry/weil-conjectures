/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.TraceFormula.StrictSemistableCurve
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.BinomialLaurentNormalForm
import WeilConjectures.AlgebraicGeometry.Dimension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Hartogs extension on the nodal trait surface after flat base change

Source: Alper--Halpern-Leistner--Heinloth, *Cartan--Iwahori--Matsumoto
Decompositions for Reductive Groups*, Section 2, Claim 2, printed p. 2;
the flat-base argument is the Laurent equalizer argument in the DAG proof
(blueprint: lem-sfb-nodal-surface-flat-hartogs).

The quotient and its spectrum are the existing strict semistable nodal model.
The inverse-image open realizes its base change along an arbitrary flat morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The punctured open `D(s) ∪ D(t)` in the existing nodal affine scheme.
Source: Alper--Halpern-Leistner--Heinloth, Section 2, Claim 2, p. 2
(blueprint: lem-sfb-nodal-surface-flat-hartogs). -/
def strictNodalPuncturedOpen (A : CommRingCat.{u}) (a : A) :
    (StrictSemistableModel.nodal a).scheme.Opens :=
  PrimeSpectrum.basicOpen
      (@id (strictNodalRing A a) (Ideal.Quotient.mk _ (MvPolynomial.X 0))) ⊔
    PrimeSpectrum.basicOpen
      (@id (strictNodalRing A a) (Ideal.Quotient.mk _ (MvPolynomial.X 1)))

/-- The nodal trait surface is integral, Noetherian, regular and two-dimensional,
with local dimension two at the origin. After every flat base change, its punctured
open preserves functions, homomorphisms of finite locally free modules, and sections
of every affine scheme over the base.

Source: Alper--Halpern-Leistner--Heinloth, Section 2, Claim 2, p. 2;
flat-base version by the exact Laurent equalizer argument in the DAG
(blueprint: lem-sfb-nodal-surface-flat-hartogs).

Proof:
1. Apply lem-sfb-dvr-binomial-local-geometry with e=1. Its distinguished ideal
   (pi,s,t) is (s,t). It gives Noetherianity and regularity at the origin and on
   D(s), D(t), and stalk dimension at most two with equality at the origin.
   The local-ring criterion gives IsRegularScheme, and
   lem-pc-scheme-dimension-local-rings gives dimension two. The injection of
   lem-sfb-binomial-laurent-normal-form into Frac(A)(T) makes the quotient a domain;
   lem-weil-pbc-spec-domain-stalks-function-field gives integrality of its spectrum.
2. The Laurent intersection identifies B with the kernel of the difference map
   B_s ⊕ B_t → B_st, with injective diagonal map. No surjectivity is required.
3. On every affine chart Spec C of T, the flat affine criterion
   lem-weil-pbc-flat-morphism-affine-criterion makes C flat over B. Tensor the
   sequence using lem-weil-pbc-flat-tensor-exact and identify its terms and maps
   by lem-weil-pbc-localization-tensor, obtaining the same exact equalizer for C.
4. Principal-open sections (lem-weil-pbc-spec-module-tilde-sections) identify that
   equalizer with the sheaf gluing equalizer on D(s), D(t). Thus the components
   of the canonical structure-sheaf map are isomorphisms on an affine basis.
   Unique affine-local extensions glue on all opens, proving the sheaf map invertible.
5. Trivialize M and N locally, using def-sc-finite-locally-free-sheaf. A homomorphism
   is a matrix of functions. Extend its entries by step 4. Uniqueness gives agreement
   on overlaps and hence unique gluing. This proves bijectivity, including zero ranks.
6. For affine q:Z→T, write q⁻¹(Spec C)=Spec D. By
   lem-a1-locally-ringed-space-affine-adjunction, a section over the punctured open
   is a C-algebra map D→Gamma(U_T intersect Spec C). Step 4 identifies the latter
   ring canonically with C. Its inverse gives a unique section over Spec C,
   compatible with the base map. These sections glue uniquely on affine overlaps.
   Empty opens and zero rings work in the same way. No Noetherianity of T is used. -/
theorem nodal_surface_flat_hartogs (A : CommRingCat.{u}) [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) (hπ : Irreducible π) :
    IsIntegral (StrictSemistableModel.nodal π).scheme ∧
    IsNoetherian (StrictSemistableModel.nodal π).scheme ∧
    IsRegularScheme (StrictSemistableModel.nodal π).scheme ∧
    topologicalKrullDim (StrictSemistableModel.nodal π).scheme = 2 ∧
    (∃ o : (StrictSemistableModel.nodal π).scheme,
      o.asIdeal = Ideal.span
        {Ideal.Quotient.mk _ (MvPolynomial.X 0), Ideal.Quotient.mk _ (MvPolynomial.X 1)} ∧
      ringKrullDim ((StrictSemistableModel.nodal π).scheme.presheaf.stalk o) = 2) ∧
    ∀ (T : Scheme.{u}) (f : T ⟶ (StrictSemistableModel.nodal π).scheme), Flat f →
      IsIso (f ⁻¹ᵁ strictNodalPuncturedOpen A π).ι.c ∧
      (∀ (M N : T.Modules), M.IsFiniteLocallyFree → N.IsFiniteLocallyFree →
        Function.Bijective
          (fun g : M ⟶ N ↦
            (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ strictNodalPuncturedOpen A π).ι).map g)) ∧
      (∀ (Z : Scheme.{u}) (q : Z ⟶ T), IsAffineHom q →
        Function.Bijective
          (fun σ : Over.mk (𝟙 T) ⟶ Over.mk q ↦
            (Over.homMk (f ⁻¹ᵁ strictNodalPuncturedOpen A π).ι :
              Over.mk (f ⁻¹ᵁ strictNodalPuncturedOpen A π).ι ⟶ Over.mk (𝟙 T)) ≫ σ)) := by
  sorry

end AlgebraicGeometry
