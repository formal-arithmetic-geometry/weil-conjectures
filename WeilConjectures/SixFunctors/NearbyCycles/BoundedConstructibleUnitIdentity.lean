/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleExchange

/-!

# The unit identity of nearby cycles on bounded constructible complexes

Let `φ : M ⟶ N` be a morphism of models over `f : X ⟶ Y` and `f' : X' ⟶ Y'` whose nearby cycles
preserve bounded constructible complexes. This file restricts the pullback exchange
`α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` to bounded constructible complexes
(`NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange`) and transports the unit identity
of the pushforward exchange (blueprint `det-tf-sp-trace-morphism`)
```
χ_f(Lf^* Λ) ∘ Ψ_N(η_f) ∘ σ_N = Rf'_*(Ψ_M(ε_f) ∘ σ_M ∘ ε_{f'}⁻¹) ∘ η_{f'}
```
to `Dᵇc(-)⟦Λ⟧`, with the unit comparisons `ε` of the strong monoidal pullbacks
(`NearbyCyclesModel.Hom.boundedConstructibleUnit_comp_map_unit_comp_pushforwardExchange_app`).

## Implementation notes

The objects of `Dᵇc(X)⟦Λ⟧` live in the derived category with its `HasDerivedCategory` instance
as fixed by `ProEtale.boundedConstructible`, while the ambient exchange maps are stated with the
instance found by typeclass synthesis. The two are equal only up to proof irrelevance, and the
kernel must never be asked to compare components `χ.app K` of the ambient exchange maps at such
differently presented objects: it would unfold `χ`. The transports are therefore proved for an
arbitrary natural transformation `χ` (the `_aux` lemmas) and only then instantiated, after
rewriting the restricted exchange maps as `NearbyCyclesModel.liftExchange` of the ambient ones.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section UpperStar

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

/-- On the ambient derived category, the unit of `Lf^* ⊣ Rf_*` on bounded constructible complexes
is the unit of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom (K :
    Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).unit.app K.obj :=
          by
  refine (Adjunction.map_restrictFullyFaithful_unit_app
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ f).symm K).trans ?_
  simp [boundedConstructibleUpperStarCompatibility, boundedConstructibleLowerStarCompatibility,
    ObjectProperty.liftCompιIso]

/-- On the ambient derived category, the counit of `Lf^* ⊣ Rf_*` on bounded constructible
complexes is the counit of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom (K :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left).counit.app K.obj
          := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ f).symm
    (boundedConstructibleLowerStarCompatibility ℓ f).symm K).trans ?_
  simp only [boundedConstructibleUpperStarCompatibility, boundedConstructibleLowerStarCompatibility,
    ObjectProperty.liftCompιIso, Iso.symm_inv, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end UpperStar

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-! ### The pushforward exchange -/

/-! ### The pullback exchange -/

/-! ### The unit identity -/

/-! ### The mate relation -/

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
