/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Existence of a fine log structure inducing prescribed étale descent data

Source: ILO VI 1.1 and VIII 3.3.8; Stacks, Tags 04TR and 04TQ
(blueprint: lem-trf-fine-log-etale-descent-existence).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Construct a fine log structure inducing the prescribed labelled local data.
The same construction is fs when every local log structure is fs.

Source: ILO, Exposé VI 1.1, printed p. 69; Exposé VIII 3.3.4(ii), 3.3.8,
printed pp. 107--108; Stacks Project, sites.tex, Tags 04TR and 04TQ
(blueprint: lem-trf-fine-log-etale-descent-existence).

Proof:
1. Identify the localized small étale sites with the small étale sites of the
   covering schemes by `Scheme.Etale.overEquiv`. Both structure presheaves evaluate
   a test scheme W at Γ(W, O_W); the identifications respect repeated restriction.
2. Forget the monoid operations. The transition maps in D define set-sheaf descent
   data, with the triple cocycle given by D.cocycle. Apply Tag 04TR to obtain a
   sheaf F and labelled local isomorphisms inducing exactly D.transition. To keep
   its sections in Type u even when the cover index is larger, pull the covering
   back to each test scheme W and choose one lift above each point of W. This is
   a jointly surjective subcover indexed by a Type u. Compatible tuples for that
   subcover form a Type u, and restriction identifies them with compatible tuples
   for the full cover, by the local sheaf conditions. Use these small models for
   F(W), transporting restrictions through the identifications.
3. Transport local products and identity elements through the labelled maps.
   Their overlap agreement follows from multiplicativity of D.transition.
   Tag 04TQ glues them. Associativity, commutativity, identity, and naturality are
   checked on the pulled-back covering by separatedness. Glue the structural
   maps in the same way; D.alpha is exactly their overlap equation. Check their
   multiplicativity and identity preservation locally. This gives a prelog
   structure with multiplicative labelled identifications and their naturality,
   structural-map, and transition equations.
4. The log-unit axiom is local: a section mapping to a unit has locally a unique
   preimage under the local unit isomorphisms, and these local inverses agree and
   glue. Thus the constructed prelog structure is log. Transport every local fine
   chart by the inverse labelled isomorphism. Compose its étale neighborhood with
   the covering map to T. These neighborhoods cover every geometric point of T,
   and the stalk chart pushout map is the original one followed by the stalk
   isomorphism, so it is still an isomorphism. The monoids are unchanged, hence
   remain finitely generated and integral. If the local structures are fs, choose
   their saturated charts instead; the same argument proves the conditional fs
   conclusion for the same global log structure. These are the log-condition and
   fine-chart locality statements of lem-trf-log-condition-fine-chart-locality.

This is only the existence part of descent. It asserts neither gluing of maps
between arbitrary prelog structures nor uniqueness of the labelled global object.
For the empty covering of the empty scheme, compatible tuples have one section
on each test object, and both chart conditions have no geometric points to test. -/
theorem fineLogEtaleDescent_exists
    {T : Scheme.{u}} [IsLocallyNoetherian T] {ι : Type v} (U : ι → T.Etale)
    (hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    (D : FineLogEtaleDescentDatum U) :
    ∃ (M : EtaleLogStructure T) (_hM : M.IsFine) (e : D.Gluing M),
      (∀ a : ι, (D.localLog a).IsFineSaturated) → M.IsFineSaturated := by sorry

end AlgebraicGeometry
