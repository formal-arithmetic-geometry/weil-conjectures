module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.AlgebraicGeometry.HenselianClopenRestriction
import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Lifting a proper clopen part of a henselian closed fibre

Source: Stacks Project, More on Morphisms, Tag 0CT9,
lemma-split-off-proper-part-henselian
(blueprint: lem-sfb-scheme-henselian-proper-clopen-lift).

Opens carry their ambient scheme's restricted structure sheaf via `Scheme.Opens.toScheme`.
Equality of opens in the closed fibre therefore gives equality of its open subschemes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper clopen part of the closed fibre lifts to a proper clopen subscheme.
Source: Stacks Project, More on Morphisms, Tag 0CT9,
lemma-split-off-proper-part-henselian
(blueprint: lem-sfb-scheme-henselian-proper-clopen-lift).

Proof:
1. The affine base is quasi-compact and quasi-separated
   (lem-weil-pbc-qcqs-over-affine). Nagata compactification
   (thm-nagata-compactification, def-nagata-compactification,
   def-nagata-compactifiable) embeds X openly in a scheme Xbar proper over Spec A.
2. Base change preserves the open immersion (lem-weil-pbc-open-immersion-base-change)
   and properness (lem-weil-pbc-proper-fp-permanence). Thus Y is open in Xbar's
   closed fibre. It is also closed: its map to that separated fibre is proper by
   lem-weil-pbc-proper-over-separated and def-weil-proper-morphism.
3. The proper henselian clopen restriction theorem
   (lem-weil-pbc-henselian-clopen-restriction) lifts this clopen to Wbar in Xbar.
   With the restricted structure sheaf it is a closed subscheme, hence proper
   (lem-weil-pbc-closed-immersion-proper). Its closed fibre is exactly Y as an
   open subscheme, by open-immersion base change.
4. The boundary Wbar minus X is closed and misses the closed fibre. If nonempty,
   the closure of one of its points is a nonempty irreducible closed subset of
   the proper Wbar. Stein connectedness (lemma-weil-pbc-stein-connectedness) says
   that this closure meets the closed fibre, a contradiction. Hence Wbar lies in X.
5. Pull Wbar back along the open immersion X into Xbar. This gives a clopen W in X,
   isomorphic to Wbar and therefore proper over Spec A. The base change is Y,
   including its restricted structure sheaf (def-weil-open-immersion and
   lem-weil-pbc-open-immersion-base-change). In Mathlib, the restriction pullback
   square is `isPullback_morphismRestrict`; equality of the resulting opens is
   precisely equality of the open subschemes in the closed fibre.
-/
theorem Scheme.exists_proper_clopen_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Y : (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Opens)
    (hY : IsClosed (Y : Set ↥(pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))))
    [IsProper (Y.ι ≫ pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ W : X.Opens, IsClosed (W : Set X) ∧ IsProper (W.ι ≫ f) ∧
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⁻¹ᵁ W = Y := by
  sorry

end AlgebraicGeometry
