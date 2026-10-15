/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.RingTheory.StrictWCover
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.RingTheory.PrincipalWLocalizationPoints
import Sheaf.RingTheory.EtaleContractionProperties
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.RingTheory.RetainedLocalizationProperties
import Sheaf.RingTheory.PrincipalWLocalization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Properties of the strict w-local cover

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1229;
Stacks Project, Tag 097X, first paragraph of proof, properties (1), (3), (7), (9)
(blueprint: lem-weil-pbc-strict-w-cover).
-/

@[expose] public section

universe u

namespace PrincipalWLocalization.StrictWCover

/-- The specified strict w-local cover is faithfully flat and ind-etale over its base,
its spectrum is w-local, its maximal local rings are strictly henselian, and its closed
points map onto the whole base spectrum.
Source: blueprint order 1229; Stacks Project, Tag 097X, first proof paragraph
(blueprint: lem-weil-pbc-strict-w-cover).

Proof: Put W = A^w, E = W^e, I the closed-point ideal of W, and T = V(IE).
The point description of `PrincipalWLocalization.points` shows that V(I) consists of
closed points and maps onto Spec A, since the diagonal pair (x,x) maps to x.
The etale-contraction properties make W -> E faithfully flat and ind-etale, with strictly
henselian maximal local rings. A prime q in T contracts to a maximal ideal m of W.
The fibre E/mE is ind-etale over the residue field, by ind-etale base-change stability;
`Algebra.weaklyEtale_field` makes each finitely generated subalgebra finite etale.
Thus E/q is an algebraic domain over that field. A least-degree monic relation for a
nonzero element has nonzero constant coefficient (otherwise cancel the element), and
dividing this relation by the element expresses its inverse. Hence E/q is a field and
q is maximal. Apply retained-localization properties to this closed set of closed points:
C_A is w-local, with closed points T and unchanged local rings E_q there. Transfer
henselianity along these local-ring isomorphisms by unique lifting of residue idempotents
in finite algebras, and transfer separable closedness by the residue-field isomorphism.
For every x in Spec A choose a closed point m of W above it. Faithful flatness of E/W
gives a prime q above m; it contains IE and belongs to T. The retained closed point (q,q)
therefore maps to x. Finally A -> W and E -> C_A are ind-Zariski, hence ind-etale.
Composition with W -> E is ind-etale by stability, hence weakly etale and flat.
The closed-point surjectivity just proved implies spectrum surjectivity, so the flat
surjective-spectrum criterion gives faithful flatness. -/
theorem properties (A : Type u) [CommRing A] :
    Module.FaithfullyFlat A (algebra A) ∧
    Algebra.IndEtale A (algebra A) ∧
    IsWLocalRing (algebra A) ∧
    (∀ (m : Ideal (algebra A)) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m)) ∧
    Function.Surjective
      (fun q : closedPoints (PrimeSpectrum (algebra A)) ↦
        PrimeSpectrum.comap (algebraMap A (algebra A)) q.val) := by
  sorry

end PrincipalWLocalization.StrictWCover
