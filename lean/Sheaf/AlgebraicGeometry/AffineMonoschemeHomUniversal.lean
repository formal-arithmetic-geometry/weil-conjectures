/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/

module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Sheaf.AlgebraicGeometry.AffineMonoschemeHomExistence
import Sheaf.AlgebraicGeometry.AffineMonoschemeHomExt

/-!
# The universal property of an unsharpened affine monoid spectrum

Source: ILO, Travaux de Gabber, Exposé VIII, Lemma 3.1.8(i), printed p.99,
using 3.1.2--3.1.6, printed pp.98--99
(blueprint: lem-trf-affine-monoscheme-hom-universal).

Monoids use multiplicative notation, so `1` represents the source's additive zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Monoscheme

/-- Pullback of canonical unsharpened numerator sections. The global-sections functor
includes the canonical identification of the inverse image of the whole space with the
whole source. No choice of homomorphism or affine chart enters this construction.
Source: ILO VIII 3.1.8(i), p.99
(blueprint: lem-trf-affine-monoscheme-hom-universal). -/
noncomputable def affinePullback {P : Type u} [CommMonoid P]
    {T : SheafedSpace CommMonCat.{u}} (f : T ⟶ affine P) :
    P →* T.presheaf.obj (op ⊤) :=
  (SheafedSpace.Γ.map f.op).hom.comp (affineSection P)

private theorem affinePullback_comp {P : Type u} [CommMonoid P]
    {T T' : SheafedSpace CommMonCat.{u}} (k : T' ⟶ T) (f : T ⟶ affine P) :
    affinePullback (k ≫ f) = (SheafedSpace.Γ.map k.op).hom.comp (affinePullback f) := by
  unfold affinePullback
  rw [op_comp, Functor.map_comp]
  rfl

/-- Local morphisms to an unsharpened affine fine monoid spectrum correspond bijectively
to monoid homomorphisms into global sections. The source is any monoidal space; neither
its stalks nor the fine monoid are assumed sharp. The second clause is naturality in the
source under local morphisms. The third specifies the spectrum map associated to a monoid
homomorphism by its canonical numerator sections and asserts naturality in the monoid.
Its uniqueness also gives compatibility of spectrum maps with identities and composition.

Source: ILO VIII 3.1.8(i), p.99, with 3.1.2--3.1.6, pp.98--99
(blueprint: lem-trf-affine-monoscheme-hom-universal).

Proof: (1) For a homomorphism phi into global sections, the elements whose germs at t
are nonunits form a prime ideal, possibly empty: a product is a unit exactly when each
factor is a unit. The locus V_a where the germ of phi(a) is a unit is open, since an inverse
germ can be represented and the inverse identity holds on a smaller neighborhood. Thus
the nonunit prime defines a continuous map, with inverse image of D(a) equal to V_a.
(2) Inverse sections on V_a are unique, hence glue. Send p/a^n to phi(p) times the nth
power of this inverse. Integrality of P proves well-definedness without cancellation in
the target. Uniqueness of inverses makes these maps compatible on all basic inclusions.
(3) The pushforward of the source sheaf is a sheaf. Apply clause (a) of
lem-weil-pbc-sheaf-morphism-on-basis to extend the compatible localization maps uniquely.
(4) By lem-trf-monoid-prime-minimal-neighborhood, the stalk at a prime is its face
localization. The stalk map sends a fraction to the corresponding quotient of germs;
a numerator is a unit exactly when it is outside the prime. The same criterion holds in
the target by construction of the prime, so every stalk homomorphism is local.
(5) Conversely locality recovers the prime map of a local morphism from its canonical
sections. Its basic-open section maps are forced on numerators and inverses. Basis
uniqueness then recovers the whole sheaf map.
(6) On D(1), which is the whole spectrum, the constructed pullback of numerators is phi.
Together with (5) this gives the two inverse identities and hence bijectivity.
(7) Pullback respects composition, proving source naturality. For v : P to Q apply the
bijection to the canonical sections of affine Q composed with v. This gives its unique
local spectrum map and the target naturality formula. Uniqueness gives identity and
composition compatibility. These are exactly the seven steps of the node's accepted split. -/
theorem affine_hom_universal (P : Type u) [CommMonoid P] (hP : FineFan.IsFine P) :
    (∀ T : SheafedSpace CommMonCat.{u},
      Function.Bijective
        (fun f : {f : T ⟶ affine P // FineFan.IsLocalMorphism f} ↦ affinePullback f.val)) ∧
    (∀ (T T' : SheafedSpace CommMonCat.{u})
      (k : {k : T' ⟶ T // FineFan.IsLocalMorphism k})
      (f : {f : T ⟶ affine P // FineFan.IsLocalMorphism f}),
      affinePullback (k.val ≫ f.val) =
        (SheafedSpace.Γ.map k.val.op).hom.comp (affinePullback f.val)) ∧
    (∀ (Q : Type u) [CommMonoid Q], FineFan.IsFine Q → ∀ v : P →* Q,
      ∃! g : {g : affine Q ⟶ affine P // FineFan.IsLocalMorphism g},
        affinePullback g.val = (affineSection Q).comp v ∧
        ∀ (T : SheafedSpace CommMonCat.{u})
          (f : {f : T ⟶ affine Q // FineFan.IsLocalMorphism f}),
          affinePullback (f.val ≫ g.val) = (affinePullback f.val).comp v) := by
  have bijective (T : SheafedSpace CommMonCat.{u}) : Function.Bijective
      (fun f : {f : T ⟶ affine P // FineFan.IsLocalMorphism f} ↦ affinePullback f.val) := by
    constructor
    · intro f g h
      apply Subtype.ext
      exact local_affine_hom_ext P hP T f.val g.val f.property g.property h
    · intro φ
      obtain ⟨f, hf, hφ⟩ := exists_local_affine_hom P hP T φ
      exact ⟨⟨f, hf⟩, hφ⟩
  refine ⟨bijective, ?_, ?_⟩
  · intro T T' k f
    exact affinePullback_comp k.val f.val
  · intro Q _ _ v
    obtain ⟨g, hg⟩ := (bijective (affine Q)).surjective ((affineSection Q).comp v)
    refine ⟨g, ⟨hg, ?_⟩, ?_⟩
    · intro T f
      calc
        affinePullback (f.val ≫ g.val) =
            (SheafedSpace.Γ.map f.val.op).hom.comp (affinePullback g.val) :=
          affinePullback_comp f.val g.val
        _ = (SheafedSpace.Γ.map f.val.op).hom.comp ((affineSection Q).comp v) :=
          congrArg (fun φ : P →* (affine Q).presheaf.obj (op ⊤) ↦
            (SheafedSpace.Γ.map f.val.op).hom.comp φ) hg
        _ = (affinePullback f.val).comp v := rfl
    · intro g' hg'
      exact (bijective (affine Q)).injective (hg'.1.trans hg.symm)

end AlgebraicGeometry.Monoscheme
