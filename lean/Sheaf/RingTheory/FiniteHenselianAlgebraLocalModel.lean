/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.StrictHenselizationFiniteLifts

import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Submodule

/-!
# Finite algebras over a local henselization have strict local models

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose V, proof 2.2.7,
and Expose XVII, final paragraph 6.5; Stacks Project, Tags 05WP and 04GH
(blueprint: lem-per-finite-henselian-algebra-local-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- A finite algebra over the henselization at a closed point with separably closed
residue field has a finite-type strict local model, provided its completed base change
is a nonzero local ring. The equation involving `e` is exactly the condition that the
ring isomorphism is over `R₀`, using the canonical strict-local structural morphism.
Source: ILO, Expose V, proof 2.2.7; Expose XVII, final paragraph 6.5;
Stacks Project, Tags 05WP and 04GH
(blueprint: lem-per-finite-henselian-algebra-local-model).

Proof:
1. Put A = (R₀)_q and k = κ(q). The henselization universal property, applied to
A → k (a henselian field), identifies κ(H) with k, including the structural map.
Thus H is henselian with separably closed residue field.
2. Finite-type permanence and localization make A Noetherian. Apply
`lem-wf-strict-henselization-finite-lifts` with the trivial separable closure k/k.
Together with `lem-weil-pbc-etale-local-ring-triples` and
`lem-weil-pbc-strict-henselization-triples`, this identifies H with the algebraic
strict henselization of A; `lem-sc-strict-henselization-noetherian` makes H
Noetherian. The affine strict-local comparison identifies it over R₀ with the
geometric strict local ring at an algebraic closure of k.
3. Completion is faithfully flat, so C embeds in its completed base change.
By `lem-weil-pbc-finite-over-henselian-local-product`, C is a finite product of
henselian local finite H-algebras. Nonzeroness excludes the empty product.
Two or more factors would give a nontrivial idempotent in the completed local
ring, which is impossible. Thus C is henselian local and H → C is local.
4. Its residue field L is finite over k, hence separably closed by
`lem-kun-sep-closed-finite-extension-sep-closed`. Thus C is strictly henselian.
Finite module generators are algebra generators; Noetherian permanence makes
C Noetherian, and finite type over Noetherian H makes C finitely presented.
5. Present H as the filtered colimit of pointed etale R₀-algebras by the triples
and etale-local-ring theorems. Apply `lem-kun-fp-algebra-descent` to descend C
to a finitely presented algebra F over one such S. Since S is finitely presented
over R₀, F is finite type over R₀, and H ⊗_S F is C.
6. The selected point p of S has residue field k. Ind-etale strict-local
invariance identifies its strict local ring with H. The neighbourhood-leg
clause of `lem-weil-pbc-strict-henselization-functoriality` makes this
identification compatible with S → H. Applying the trivial-residue finite-lift
comparison again shows S → H is the ordinary henselization at p.
7. By `lem-trf-henselization-prime-ind-etale`, S → H is ind-etale.
Its base change F → C therefore induces isomorphisms of strict localizations
by `lem-trf-ind-etale-strict-local-invariance`.
8. Contract the maximal ideal of C to z in F. It contracts further to q in R₀.
The domain F/z embeds as a k-algebra in the finite extension L/k; hence it is
finite dimensional over k and is a field. Thus z is maximal. An algebraic
closure of L gives a geometric point of Spec C and its image barZ over z.
9. A strictly henselian local ring is its own strict local ring at this closed
geometric point: use its identity henselization, the trivial residue extension,
and the affine comparison. Combine with Step 7 to obtain the R₀-algebra
isomorphism C ≅ O^sh_(Spec F,barZ). Joining generators for R₀/D and F/R₀ makes
F finite type over D, giving the asserted finite-type scheme morphism. -/
theorem finite_henselian_algebra_local_model
    (D R₀ : Type u) [CommRing D] [CommRing R₀] [IsNoetherianRing D]
    [Algebra D R₀] [Algebra.FiniteType D R₀]
    (q : Ideal R₀) [q.IsMaximal] [IsSepClosed q.ResidueField]
    (H : Type u) [CommRing H] [Algebra (Localization.AtPrime q) H]
    [HenselianLocalRing H] (hH : Algebra.IsHenselizationAtPrime' R₀ q H)
    (C : Type u) [CommRing C] [Algebra H C] [Module.Finite H C]
    [IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal H) H ⊗[H] C)] :
    IsNoetherianRing C ∧ IsStrictlyHenselianLocalRing C ∧
      ∃ (F : Type u) (_ : CommRing F) (_ : Algebra R₀ F),
        Algebra.FiniteType R₀ F ∧
        ∃ (z : Ideal F) (_ : z.IsMaximal),
          z.comap (algebraMap R₀ F) = q ∧
          ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
            (barZ : Spec (.of Ω) ⟶ Spec (.of F)),
            (barZ (IsLocalRing.closedPoint Ω)).asIdeal = z ∧
            ∃ e : C ≃+* strictHenselizationRing barZ,
              Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
                  strictHenselizationStructuralMap barZ ≫
                    Spec.map (CommRingCat.ofHom (algebraMap R₀ F)) =
                Spec.map (CommRingCat.ofHom ((algebraMap H C).comp
                  ((algebraMap (Localization.AtPrime q) H).comp
                    (algebraMap R₀ (Localization.AtPrime q))))) ∧
              ((algebraMap R₀ F).comp (algebraMap D R₀)).FiniteType := by
  sorry

end AlgebraicGeometry.Scheme
