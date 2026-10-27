/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Sheaf.AlgebraicGeometry.AffineAssociatedPointsPrimes
import Sheaf.AlgebraicGeometry.HenselianFlatPointFreeAffineNeighbourhood
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyAffineSections
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineSectionAssociatedStalk
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Free colimit presentations over a henselian local base

Source: Stacks Project, flat.tex, Tag 05U7
(lemma-flat-finite-type-local-colimit-free), first assertion.
(blueprint: lem-sfb-henselian-flat-finite-module-residue-free-colimit).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- A finite module over an essentially finite type local algebra, flat over a henselian
local base, is a small filtered colimit of free base modules with injective reductions
of all transition maps modulo the maximal ideal. No finite rank is required.

Source: Stacks Project, flat.tex, Tag 05U7
(lemma-flat-finite-type-local-colimit-free), first assertion.
(blueprint: lem-sfb-henselian-flat-finite-module-residue-free-colimit).

The reduced map is written using `TensorProduct.quotTensorEquivQuotSMul` on each side
of tensoring the transition with `A / m`. This is precisely the quotient map
`F_d / m F_d → F_e / m F_e`: the equivalence sends `1 ⊗ x` to the class of `x`, so
its conjugate sends the class of `x` to the class of the transition applied to `x`.
Here `m F_d` is `IsLocalRing.maximalIdeal A • ⊤`.

Proof:
1. Write B as the localization C_q of a finite type A-algebra C. Choose B-generators
   p_1,...,p_r of P and put M = C^r / ker(C^r → P). Localizing this quotient at q
   gives P: the generators give surjectivity and the kernel gives injectivity. Set
   X = Spec C, F = tilde M and x = q. Then F_x is P as an A-module and x lies over
   the closed point. No finite presentation of P or finite generation of the kernel is used.
   Use def-weil-pbc-essentially-finite-type-algebra, def-weil-finitely-generated-module,
   lem-weil-pbc-spec-module-tilde-sections, lem-weil-pbc-quasi-coherent-finite-type-affine
   and def-weil-pbc-module-stalk.
2. The closed fibre has ring R = C / m C, finite type over the residue field and hence
   Noetherian (lem-weil-pbc-finite-type-algebra-noetherian). Its sheaf F_s is the tilde
   of the finite module M tensor_A k (lem-weil-pbc-tilde-pullback-base-change), so its
   associated primes are finite (lem-weil-pbc-noetherian-associated-primes-finite).
   Identify these with associated points by lem-sfb-affine-associated-points-primes.
3. For every associated prime not specializing to x, choose an element in that prime
   outside q. The product of their lifts is outside q; restrict to its principal open.
   Every remaining associated point of the closed fibre now specializes to x.
4. Apply lem-sfb-henselian-flat-point-free-affine-neighbourhood inside every open
   neighbourhood of x. The affine neighbourhoods with A-free sections form a small
   nonempty filtered poset under reverse inclusion: intersect two neighbourhoods and
   apply the same theorem there. Restrictions give F and germs give the compatible v.
5. By lem-pc-flat-affine-base-change-sections and
   lem-weil-pbc-fibre-product-affine-spectra, reduction of a restriction is the restriction
   between the corresponding affine opens in the closed fibre. The pure tensor formula
   identifies this reduction with the quotient transition written in the statement.
6. These affine fibre opens are locally Noetherian by lem-weil-pbc-localization-noetherian
   and pqf-def-locnoeth. A nonzero section killed by restriction has a nonzero germ at an
   associated point (lem-sbc-affine-section-associated-stalk and the affine finite-type
   criterion). Such a point specializes to x and therefore lies in every open containing
   x, contradicting that the restricted section is zero. Thus each reduction is injective.
7. Germs exhibit P as the colimit (def-weil-pbc-module-stalk and
   def-weil-pbc-category-colimit): every germ has a representative on a free affine
   neighbourhood; equal germs agree on a smaller such neighbourhood. A compatible family
   of linear maps therefore gives a unique linear map on P, using a common refinement
   to check addition and scalar multiplication.

Universes: A, B and P live in independent universes; the diagram, its index category
and the free terms live in the universe of P. This is no restriction: if P is nonzero it
is faithfully flat over A, so A embeds in End(P) and every module occurring in the
proof is small relative to P. -/
theorem exists_free_filtered_colimit_residue_injective
    (A : Type u) (B : Type v) (P : Type w)
    [CommRing A] [CommRing B] [HenselianLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    [Module.Finite B P] [Module.Flat A P] :
    ∃ (D : Type w) (_catD : SmallCategory D) (_filteredD : IsFiltered D)
      (F : D ⥤ ModuleCat.{w} A)
      (ι : F ⟶ (Functor.const D).obj (ModuleCat.of A P)),
      (∀ d : D, Module.Free A (F.obj d)) ∧
      Nonempty (IsColimit (Cocone.mk (ModuleCat.of A P) ι)) ∧
      ∀ (d e : D) (a : d ⟶ e),
        Function.Injective
          (((TensorProduct.quotTensorEquivQuotSMul (F.obj e)
              (IsLocalRing.maximalIdeal A)).toLinearMap).comp
            (((F.map a).hom.lTensor (A ⧸ IsLocalRing.maximalIdeal A)).comp
              (TensorProduct.quotTensorEquivQuotSMul (F.obj d)
                (IsLocalRing.maximalIdeal A)).symm.toLinearMap)) := by
  sorry

end Module
