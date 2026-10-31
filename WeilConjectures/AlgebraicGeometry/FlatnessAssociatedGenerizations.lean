/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeAssassin
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleStalkFinite
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.Localization

/-! # Flatness detected at associated generalizations in the fibre

Source: Stacks Project, More on Flatness, Tag 05UA,
`theorem-check-flatness-at-associated-points`, conditions (1) and (2).
(blueprint: lem-sfb-scheme-flatness-associated-generizations).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite type quasi-coherent module is flat at a point over the base exactly when
its stalks at the associated generalizations in the same fibre are base-flat.
The right-hand stalk is on the original scheme, not on the fibre. Its base ring is
literally the base stalk at `f v`: `stalkCongr` transports along the equality supplied
by the fibre homeomorphism, then `f.stalkMap` supplies the structure action.

Source: Stacks Project, More on Flatness, Tag 05UA.
(blueprint: lem-sfb-scheme-flatness-associated-generizations).

Proof, following the seven steps of the node:
1. On an affine neighbourhood write the module as tilde L. The local-spectrum map
and tilde-stalk localization identify N_v with L_r and N_a with its localization
at the prime of a. These identifications are linear over the same base stalk.
Localization preserves base-flatness, proving the forward direction.
2. Set A = O_{T,t}, B = O_{V,v}, P = N_v. The stalk map is local and essentially
of finite type and P is finite over B. Write B as a localization of a finite type
A-algebra. Its quotient C = B/m_A B is a localization of a finite type algebra over
kappa(t), hence Noetherian. The quotient Pbar = P/m_A P is finite over C. Neither
A nor B is required to be Noetherian.
3. The fibre-stalk quotient and pullback-stalk tensor formula identify C with the
fibre local ring and Pbar with the fibre module stalk. An associated prime q of
Pbar over B descends to an associated prime qbar over C: take an element z with
annihilator q. The local-spectrum map sends qbar to a generalization a of v in the
fibre. The localized element z/1 is nonzero, and its annihilator is qbar C_qbar:
if h c z = 0 with h outside qbar, primality forces c into qbar. Thus a is associated.
The image in V corresponds to q, so P_q = N_a is A-flat by hypothesis.
4. Let Sigma be the multiplicative set of elements acting injectively on Pbar,
B' = Sigma^{-1}B and M = Sigma^{-1}P. By
lem-sfb-fibre-regular-localization-spectrum, every prime of B' contracts to a prime
p of B contained in an associated prime q of Pbar. Step 2 checks its hypotheses.
5. Successive fraction identifications give M_p' = P_p, a localization of P_q.
Step 3 and localization preservation give A-flatness at every prime of B'. Flatness
over A agrees with flatness over the corresponding localization of A. The affine
local criterion therefore gives A-flatness of M, including when B' is zero.
6. The quotient/localization isomorphism sends [p/s] to [p]/s and has the reverse
fraction formula as inverse. It identifies the reduction of P -> M with
Pbar -> Sigma^{-1}Pbar. If [p]/1 = 0, some s in Sigma kills [p]; its injective action
forces [p] = 0. Thus this reduction is injective.
7. Apply lem-sfb-finite-source-fibre-injective-flat-target to P -> M. The local map
A -> B is essentially finite type, P is finite, M is A-flat by Step 5, and the
closed-fibre map is injective by Step 6. The lemma gives A-flatness of P, as required.
-/
theorem flat_stalk_iff_associated_generizations {V T : Scheme.{u}}
    (f : V ⟶ T) [LocallyOfFiniteType f] (N : V.Modules)
    (hN : N.IsQuasiCoherentFiniteType) (v : V) :
    Module.Flat (T.presheaf.stalk (f v))
      ((ModuleCat.restrictScalars (f.stalkMap v).hom).obj
        ((RingedSpace.moduleStalkFunctor V.toRingedSpace v).obj N)) ↔
    ∀ a : f.fiber (f v),
      a ∈ associatedPoints ((tensorPullback (f.fiberι (f v))).obj N) →
      a ⤳ f.asFiber v →
      Module.Flat (T.presheaf.stalk (f v))
        ((ModuleCat.restrictScalars
          ((T.presheaf.stalkCongr (.of_eq (f.fiberHomeo (f v) a).property)).inv ≫
            f.stalkMap (f.fiberι (f v) a)).hom).obj
          ((RingedSpace.moduleStalkFunctor V.toRingedSpace (f.fiberι (f v) a)).obj N)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
