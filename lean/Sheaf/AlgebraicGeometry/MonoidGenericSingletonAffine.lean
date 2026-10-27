/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.FineFanBlowup

/-!
# The affine generic singleton of a fine monoid chart

Source: ILO, Travaux de Gabber, VIII 3.1.2--3.1.4 and 3.1.10(ii), pp.98--100
(blueprint: lem-trf-monoid-generic-singleton-affine).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Monoscheme

/-- The generic point of one ordinary fine monoid chart has an affine singleton
neighborhood in the ambient sheafed space.

Source: ILO VIII 3.1.2--3.1.4 and 3.1.10(ii), pp.98--100
(blueprint: lem-trf-monoid-generic-singleton-affine).

Proof: transport the point into Spec P using the given chart. It is the empty
prime: it generalizes the empty prime, and prime contraction along specialization
is inclusion. Choose finite generators of P and let a be their product, with a=1
for the empty list. A prime avoids a exactly when it avoids all generators, hence
is empty. Thus D(a) is the singleton in question. Localizing at a inverts every
generator, so P[a^-1]=P^gp, which is fine (the generators and their inverses form a
finite generating set). Evaluation at the unique point identifies the local-fraction
sections on D(a) with P^gp. Every cover of this singleton contains the singleton,
so the sheafification unit is bijective there. On the empty open both sheaves have
one section by the sheaf axiom. The spectrum of Q=P^gp is also a singleton; the
same evaluation identifies its sections with Q. These identifications commute
with the only restrictions (identities and restriction to the empty open), giving
an isomorphism of sheaves over the unique homeomorphism of the singletons.
Transport it along the original chart and compose the two open restrictions.
This gives W and its required isomorphism. Group monoids, including those with torsion,
already have a singleton spectrum; the trivial monoid uses the empty product and the whole chart. -/
theorem monoid_generic_singleton_affine (X : SheafedSpace CommMonCat.{u})
    (U : Opens X) (P : CommMonCat.{u}) (hP : FineFan.IsFine P)
    (e : X.restrict U.isOpenEmbedding ≅
      { carrier := TopCat.of (FineFan.MonoidPrime P)
        presheaf := (FineFan.spectrumSheaf P).obj
        IsSheaf := (FineFan.spectrumSheaf P).property })
    (η : X) (hη : η ∈ U) (hgen : ∀ x : X, x ∈ U → η ⤳ x) :
    ∃ (W : Opens X) (Q : CommMonCat.{u}), FineFan.IsFine Q ∧
      (W : Set X) = {η} ∧ Nonempty
        (X.restrict W.isOpenEmbedding ≅
          { carrier := TopCat.of (FineFan.MonoidPrime Q)
            presheaf := (FineFan.spectrumSheaf Q).obj
            IsSheaf := (FineFan.spectrumSheaf Q).property }) := by
  sorry

end AlgebraicGeometry.Monoscheme
