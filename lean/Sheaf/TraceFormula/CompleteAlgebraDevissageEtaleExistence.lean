/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.TraceFormula.CompleteAlgebraDevissage
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.PointedAffineDevissage
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.TraceFormula.ElementaryModuleDevissage
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.Topology.FiniteTypeSurjectiveNearStalk
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Nakayama

/-!
# Complete algebraic dévissage after elementary étale localization

Source: Stacks Project, flat.tex, Tag 05I1, lemma-existence-algebra, forgetting the
additional pointing of the dévissage at the source prime, via Tags 05HR and 05I0
(blueprint: lem-trf-complete-algebra-devissage-etale-existence).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finite module over a finite type algebra admits complete dévissage over the
marked base prime after elementary étale localization of both rings. The tensor
is written with the scalar extension on the left; `TensorProduct.comm` identifies
it canonically with the source's `N ⊗[S] S₀`. All residue-field maps are the induced
maps of the specified ring homomorphisms, rather than arbitrary field isomorphisms.

Source: Stacks Project, Tag 05I1, lemma-existence-algebra, with the extra pointing
forgotten, via Tag 05HR, proposition-existence-complete-at-x, and Tag 05I0
(blueprint: lem-trf-complete-algebra-devissage-etale-existence).

Proof plan:
1. Pass to `Spec S → Spec R` and the associated quasi-coherent sheaf of `N`.
   The affine finite-type criterion makes the morphism locally finite type and
   the sheaf finite type. Use the affine translation of pointed dévissage data.
2. Induct strongly on the dimension at the marked point of the fibre support,
   for all affine input data. This dimension is finite: the fibre algebra is
   finite type over its residue field and the finite module has closed support.
3. If the fibre stalk vanishes, Nakayama makes the original stalk vanish. Finite
   type then gives a zero neighbourhood; choose an affine open therein and use
   its elementary étale inclusion with the length-zero chain and unchanged base.
4. Otherwise apply lem-trf-elementary-module-devissage. It gives elementary
   étale source and base changes, a finite map Z → Y, a finitely presented closed
   immersion Z → X, the original module as the pushforward, a singleton marked
   fibre, a purely transcendental residue extension, and a smooth geometrically
   integral target Y of relative dimension d. These give one-step pointed data.
5. Apply lem-trf-devissage-generic-basis-drop to the finite quasi-coherent module
   on Y obtained by finite pushforward. Its generic basis map has a finite-type
   quasi-coherent cokernel whose fibre support has dimension less than d. When
   its marked fibre stalk is zero, shrink to a principal zero neighbourhood as
   in Step 3 and restrict the first datum by lem-trf-devissage-pointed-restriction.
   The basis map is then surjective, yielding a complete chain of length one;
   this also finishes d = 0.
6. If the cokernel fibre stalk is nonzero, apply induction to this cokernel on Y,
   whose structural map is locally finite type because it is smooth. The new
   elementary étale square and its pointed chain may change the base again.
7. Apply lem-trf-devissage-pointed-etale-refinement to the first datum and this
   square. The singleton fibre and purely transcendental extension ensure its
   hypotheses. Finite-pushforward comparison transports the basis map, preserves
   its generic-fibre isomorphism, and identifies its cokernel with the restricted
   pullback of the inductive cokernel. Pull the tail chain to the new base by the
   pointed base-change clause of lem-trf-devissage-pointed-restriction.
8. Use the initial-open shrinking clause of that restriction lemma to fit the
   tail into the new target. Its principal open is also principal in the first
   target. Restrict the first datum to the new base, shrink its target to this
   principal open, and pull back the tail once more to the final base. Its first
   module is exactly the cokernel of the first map. Concatenate: all generic
   maps are isomorphisms and the final cokernel is zero. This proves induction.
9. Return to affine coordinate rings. The pointed elementary étale maps give
   the commutative square, the three prime contractions and the two canonical
   residue-field isomorphisms. These properties compose. The tilde pullback
   comparison identifies the final module with `S₀ ⊗[S] N`; tensor symmetry
   identifies it with `N ⊗[S] S₀`.
10. Put C = S ⊗[R] R₀. The map Spec C → Spec S is étale by base change, so
    cancellation makes Spec S₀ → Spec C étale. Its finite presentation, together
    with finite type of C/R₀, gives finite type of S₀/R₀. Tensor the original
    finite generating list to see the final module is finite. Apply
    lem-trf-pointed-devissage-affine-translation and forget the marked
    intermediate points to obtain the complete algebra dévissage. No flatness
    of the input module or algebra has been used.
-/
theorem exists_completeAlgebraDevissage_etale
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (N : Type v) [AddCommGroup N] [Module S N] [Module.Finite S N]
    (q : Ideal S) [q.IsPrime] (p : Ideal R) [p.IsPrime]
    (_hp : p = q.comap (algebraMap R S)) :
    ∃ (R₀ : CommAlgCat.{u} R) (S₀ : CommAlgCat.{u} S) (φ : R₀ →+* S₀)
      (q₀ : PrimeSpectrum S₀) (p₀ : PrimeSpectrum R₀)
      (hq : q = q₀.asIdeal.comap (algebraMap S S₀))
      (hp : p = p₀.asIdeal.comap (algebraMap R R₀)),
      φ.comp (algebraMap R R₀) = (algebraMap S S₀).comp (algebraMap R S) ∧
      p₀.asIdeal = q₀.asIdeal.comap φ ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap R R₀))) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap S S₀))) ∧
      Function.Bijective (Ideal.ResidueField.map p p₀.asIdeal (algebraMap R R₀) hp) ∧
      Function.Bijective (Ideal.ResidueField.map q q₀.asIdeal (algebraMap S S₀) hq) ∧
      ∃ (hft : @Algebra.FiniteType R₀ S₀ _ _ φ.toAlgebra)
        (hN : Module.Finite S₀ (S₀ ⊗[S] N)),
        Nonempty (@CompleteAlgebraDevissage R₀ S₀ _ _ φ.toAlgebra hft
          p₀.asIdeal inferInstance (S₀ ⊗[S] N) inferInstance inferInstance hN) := by
  sorry

end AlgebraicGeometry
