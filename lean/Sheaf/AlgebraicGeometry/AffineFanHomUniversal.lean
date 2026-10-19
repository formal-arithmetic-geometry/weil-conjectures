/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.AffineFanLocalizationSections

/-!
# The universal property of a sharp affine monoid spectrum

Source: ILO, Exposé VIII, Lemma 3.1.8(ii), printed p.99, and Definitions 3.1.3 and 3.1.6
(blueprint: lem-trf-affine-fan-hom-universal).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.FineFan

/-- Pull back the canonical monoid sections along a sheafed-space morphism. This uses
Mathlib's global-sections functor and the dependency's canonical `affineSection`, including
both sheafification units and the quotient by units. Locality is imposed on the morphism
in the universal property below, rather than needed to define this section map.
Source: ILO VIII 3.1.8(ii), p.99 (blueprint: lem-trf-affine-fan-hom-universal). -/
noncomputable def affinePullback {P : Type u} [CommMonoid P]
    {T : SheafedSpace CommMonCat.{u}} (f : T ⟶ affine P) :
    P →* T.presheaf.obj (op ⊤) :=
  (SheafedSpace.Γ.map f.op).hom.comp (affineSection P)

/-- The sharp affine monoid spectrum represents homomorphisms into global sections,
naturally in the sharp monoidal space and the fine sharp monoid. We use multiplicative
notation, so the additive zero in the source is `1`. Morphisms are sheafed-space morphisms
with local stalk maps. The first clause is bijectivity of the prescribed canonical map.
The second is naturality under precomposition by local morphisms of sharp monoidal spaces.
The third constructs the unique spectrum morphism associated to each monoid homomorphism
by its canonical sections, and states naturality under postcomposition with that morphism.

Source: ILO VIII 3.1.8(ii), p.99 (blueprint: lem-trf-affine-fan-hom-universal).

Proof: (1) Sharp stalks imply sharp sections by sheaf separation. For a homomorphism
`φ : P → Γ(T)`, the elements whose germ at `x` is not `1` form a prime ideal; this defines
the point map. (2) The inverse image of `D(a)` is the open locus where the germ of `φ(a)`
is `1`. On that open, extend `φ` to the localization by sending denominators to `1`.
(3) The maps kill units, hence descend to sharpening. The localization-section description
of `lem-trf-affine-fan-localization-sections` makes them compatible on intersections and
inclusions of basic opens. Glue them to a sheaf map. (4) The same lemma identifies stalks
with sharpened face localizations: a numerator maps to `1` exactly when it is outside the
prime. Thus the stalk maps are local. (5) Locality recovers a given morphism's point map
from its canonical sections. (6) Every basic-open section is represented by a numerator
modulo units, so its pullback is determined as well. Sheaf gluing gives uniqueness, and
on the whole space the constructed map pulls back each numerator to `φ` of that numerator.
This proves bijectivity. (7) Pullback of sections respects composition, proving source
naturality. Apply bijectivity to `affine Q` and `affineSection Q ∘ u` to obtain the unique
local spectrum morphism for `u : P → Q`; its pullback formula gives target naturality.
Identity and composite spectrum morphisms follow from the same formula and uniqueness. -/
theorem affine_hom_universal (P : Type u) [CommMonoid P]
    (hP : IsFine P) (sP : IsSharp P) :
    (∀ (T : SheafedSpace CommMonCat.{u}),
      (∀ x : T, IsSharp (stalk T.presheaf x)) →
      Function.Bijective
        (fun f : {f : T ⟶ affine P // IsLocalMorphism f} ↦ affinePullback f.val)) ∧
    (∀ (T T' : SheafedSpace CommMonCat.{u}),
      (∀ x : T, IsSharp (stalk T.presheaf x)) →
      (∀ x : T', IsSharp (stalk T'.presheaf x)) →
      ∀ (k : {k : T' ⟶ T // IsLocalMorphism k})
        (f : {f : T ⟶ affine P // IsLocalMorphism f}),
      affinePullback (k.val ≫ f.val) =
        (SheafedSpace.Γ.map k.val.op).hom.comp (affinePullback f.val)) ∧
    (∀ (Q : Type u) [CommMonoid Q], IsFine Q → IsSharp Q → ∀ (v : P →* Q),
      ∃! g : {g : affine Q ⟶ affine P // IsLocalMorphism g},
        affinePullback g.val = (affineSection Q).comp v ∧
        ∀ (T : SheafedSpace CommMonCat.{u}),
          (∀ x : T, IsSharp (stalk T.presheaf x)) →
          ∀ (f : {f : T ⟶ affine Q // IsLocalMorphism f}),
          affinePullback (f.val ≫ g.val) = (affinePullback f.val).comp v) := by
  sorry

end AlgebraicGeometry.FineFan
