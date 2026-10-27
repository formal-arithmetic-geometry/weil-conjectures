/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Sheaf.AlgebraicGeometry.AffineAssociatedPointsPrimes
import Sheaf.TraceFormula.FibreAssociatedPrimesModuleRing
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-! # Fibre generic points near a relative associated point

Source: Stacks Project, More on Morphisms, Tag 05F1,
`lemma-relative-assassin-in-neighbourhood`
(blueprint: lem-sfb-relative-assassin-neighbourhood).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A nonempty open of the reduced closure of a relative associated point has associated
component generic points on each fibre. No flatness or Noetherian assumption is made.
The `pullback.map` is the canonical morphism from the open's fibre to the ambient fibre.

Source: Stacks Project, More on Morphisms, Tag 05F1,
`lemma-relative-assassin-in-neighbourhood`
(blueprint: lem-sfb-relative-assassin-neighbourhood).

Proof:
1. Choose affine neighbourhoods of f(xi) and xi. By [lem-weil-pbc-lft-affine-pairs]
   and [lem-weil-pbc-quasi-coherent-finite-type-affine], write these as Spec A and
   Spec B with B finite type over A and F represented by a finite B-module M.
   Use [lem-weil-pbc-affine-chart-base-change-iso] and
   [lem-weil-pbc-tilde-pullback-base-change] to identify the fibre ring and module.
   These fibre rings are Noetherian by [lem-wf-affine-noetherian-components].
   Thus [lem-sfb-affine-associated-points-primes] turns relative association into
   association of the corresponding prime q in M tensor_A kappa(p), p = q intersect A.
2. Replace A, B, M by A/p, B/pB, M/pM. This preserves the closed subscheme Spec(B/q)
   and all relevant fibres. The domain A/p injects into B/q, and its fraction field
   is kappa(p). By [lem-trf-fibre-associated-primes-module-ring], q/pB is an
   element annihilator in the generic-fibre module, regarded as a B/pB-module.
3. By [lem-trf-algebra-module-simultaneous-generic-flatness], invert a nonzero a in
   the domain A to make M_a flat over A. B_a remains finite type over A and M_a
   remains finite over B_a. The generic-fibre module and its associated prime persist.
4. Choose an element with annihilator q in the generic fibre and clear its denominator.
   Flatness gives torsion-freeness by [lem-trf-flat-module-torsionfree-domain], so
   M_a injects into its generic fibre. The cleared element therefore has annihilator
   qB_a in M_a itself, using [def-weil-pbc-annihilator-associated-primes]. This gives
   an injection B_a/qB_a into M_a with finite cokernel Q.
5. Apply [lem-trf-algebra-module-simultaneous-generic-flatness] to Q and invert another
   nonzero b in A. Localization preserves the short exact sequence: the fraction-zero
   criterion shows that a kernel fraction comes from the original image after
   multiplying its numerator by a power of b. Its cokernel Q_b is now flat over A.
6. By [lem-weil-pbc-flat-quotient-tensor-injective], tensoring with any residue field
   preserves the injection from C = (B/q)[1/(ab)] into M[1/(ab)]. Set W = Spec C,
   the principal open D(ab) of the reduced closure in the chosen affine chart.
   By [lem-weil-pbc-affine-chart-base-change-iso] and
   [lem-weil-pbc-tilde-pullback-base-change], the injected fibre module is the quotient
   ring D_s = R_s/(qR_s), with R_s the ambient localized fibre ring.
7. A generic point of any component of Spec D_s is a minimal prime. D_s is Noetherian
   by [lem-wf-affine-noetherian-components], so
   [lem-weil-pbc-noetherian-minimal-prime-associated] realizes this prime as Ann(d).
   The injection into the ambient fibre module preserves its exact annihilator over
   R_s. By [lem-sfb-affine-associated-points-primes], the image is associated on the
   affine open fibre and hence in the full fibre, since the stalk condition is unchanged.
8. Both a and b remain nonzero in the domain B/q, so D(ab) contains xi and is nonempty.
   It is open in the original reduced closure. Transfer the fibre identifications
   through the quotient-base and affine-open reductions to obtain the assertion. -/
theorem relativeAssassin_neighbourhood {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) (hF : F.IsQuasiCoherentFiniteType)
    (ξ : X) (hξ : ξ ∈ relativeAssassin f F) :
    ∃ W : (Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({ξ} : Set X), isClosed_closure⟩).subscheme.Opens,
      W.carrier.Nonempty ∧
      ∀ s : S,
        s ∈ Set.range (W.ι ≫ (Scheme.IdealSheafData.vanishingIdeal
          ⟨closure ({ξ} : Set X), isClosed_closure⟩).subschemeι ≫ f) →
        ∀ C : Set ((W.ι ≫ (Scheme.IdealSheafData.vanishingIdeal
            ⟨closure ({ξ} : Set X), isClosed_closure⟩).subschemeι ≫ f).fiber s),
          C ∈ irreducibleComponents ((W.ι ≫ (Scheme.IdealSheafData.vanishingIdeal
            ⟨closure ({ξ} : Set X), isClosed_closure⟩).subschemeι ≫ f).fiber s) →
          ∀ y : (W.ι ≫ (Scheme.IdealSheafData.vanishingIdeal
              ⟨closure ({ξ} : Set X), isClosed_closure⟩).subschemeι ≫ f).fiber s,
            IsGenericPoint y C →
            (pullback.map _ _ f (S.fromSpecResidueField s)
              (W.ι ≫ (Scheme.IdealSheafData.vanishingIdeal
                ⟨closure ({ξ} : Set X), isClosed_closure⟩).subschemeι)
              (𝟙 _) (𝟙 S)
              (by simp only [Category.comp_id, Category.assoc])
              (by simp only [Category.comp_id, Category.id_comp])) y ∈
                associatedPoints ((tensorPullback (f.fiberι s)).obj F) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
