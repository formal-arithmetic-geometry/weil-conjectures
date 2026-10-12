/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Étale-origin witnesses

A bounded below complex `K` of pro-étale sheaves on a scheme `T` *comes from the étale site* if
it is equipped with a bounded below complex `L` of étale sheaves and an isomorphism
`α : ν^* L ≅ K` (blueprint `def-weil-pbc-etale-origin-witness`). The pair `(L, α)` is data, not
only its existence, and it is transported along isomorphisms of `K`.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {T : Scheme.{u}}

/-- Blueprint `def-weil-pbc-etale-origin-witness`: an explicit étale-origin witness for a
bounded below complex `K` of pro-étale sheaves on `T`: a bounded below complex `L` of étale
sheaves together with an isomorphism `α : ν_T^* L ≅ K`. -/
structure EtaleOriginWitness (K : DerivedCategory.Plus (Sheaf (ProEt.topology T) A)) where
  /-- The bounded below complex of étale sheaves. -/
  L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology A)
  /-- The identification of its comparison pullback with `K`. -/
  α : D+(ν^*(T)[A]).obj L ≅ K

namespace EtaleOriginWitness

/-- The tautological étale-origin witness of `ν_T^* L`. -/
@[simps]
noncomputable def self (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology A)) :
    EtaleOriginWitness (D+(ν^*(T)[A]).obj L) where
  L := L
  α := Iso.refl _

/-- Transport of an étale-origin witness along an isomorphism `K ≅ K'`. -/
@[simps]
def ofIso {K K' : DerivedCategory.Plus (Sheaf (ProEt.topology T) A)}
    (w : EtaleOriginWitness K) (e : K ≅ K') : EtaleOriginWitness K' where
  L := w.L
  α := w.α ≪≫ e

@[simp]
lemma ofIso_refl {K : DerivedCategory.Plus (Sheaf (ProEt.topology T) A)}
    (w : EtaleOriginWitness K) : w.ofIso (Iso.refl K) = w := by
  cases w
  simp [ofIso]

lemma ofIso_trans {K K' K'' : DerivedCategory.Plus (Sheaf (ProEt.topology T) A)}
    (w : EtaleOriginWitness K) (e : K ≅ K') (e' : K' ≅ K'') :
    w.ofIso (e ≪≫ e') = (w.ofIso e).ofIso e' := by
  simp [ofIso]

/-- A complex with an étale-origin witness is of étale origin. -/
lemma plusEtaleOrigin {K : DerivedCategory.Plus (Sheaf (ProEt.topology T) A)}
    (w : EtaleOriginWitness K) :
    DerivedCategory.TStructure.t.plus.map D(ν^*(T)[A]) (DerivedCategory.Plus.ι.obj K) :=
  ⟨DerivedCategory.Plus.ι.obj w.L, w.L.2,
    ⟨((ν^*(T)[A]).mapDerivedCategoryPlusCompatibility.app w.L).symm ≪≫
      DerivedCategory.Plus.ι.mapIso w.α⟩⟩

end EtaleOriginWitness

end AlgebraicGeometry.ProEtale
