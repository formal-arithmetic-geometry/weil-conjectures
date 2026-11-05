/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ClopenCounit
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClass
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity

/-!

# The unit identity of fact (III) on a clopen component

Fact (III) of `ComponentClassReduction` was reduced
(`unitClass_comp_map_comp_lowerShriekCompOfEq_inv`) to the identity
`s ≫ ψ = η_r(ℚ̄_ℓ) ≫ Rr_*(ε⁻¹ ≫ σ_B)` on the special fixed locus `F'`, where
`s = σ_F ≫ Ψ_F(e)⁻¹`, `ψ = Lι'^*(χ_{ιj}) ≫ counit`. This file proves it:

* abstractly (`specializationUnit_comp_inv_map_comp_eq_aux`), for adjunctions standing for
  `Lj^* ⊣ Rj_*`, `Lι^* ⊣ Rι_*`, `L(ιj)^* ⊣ R(ιj)_*`, `Lr^* ⊣ Rr_*`, `Lι'^* ⊣ Rι'_*`,
  `Lb''^* ⊣ Rb''_*`: `Ψ_F(e)` is inverted by `Ψ_F(η_j ≫ Rj_*(ε⁻¹) ≫ (Rj_! ≅ Rj_*)⁻¹)`
  (`ProEtale.CondensedRing.homEquiv_symm_unitIso_inv_comp_unit`), the units of the adjunctions
  compose (`ProEtale.CondensedRing.lowerStarUnit_comp`), and the unit identity of the pushforward
  exchange `χ` and the triangle identity of `Lι'^* ⊣ Rι'_*` conclude;
* for any morphism `φ` of nearby cycles models over `ι ∘ j` whose morphism of special fibres is
  `ι' ∘ r` (`ProEtale.CondensedRing.specializationUnit_comp_inv_map_comp_exchange_eq`), and then
  fact (III) itself (`ProEtale.CondensedRing.unitClass_comp_map_comp_exchange_eq`).

## Implementation notes

For the concrete data (`φ = componentModelHom`, `r = componentSpecialLift`, `ι'` the inclusion of
the special fixed locus) the two theorems are obtained inside a proof by
`have h := unitClass_comp_map_comp_exchange_eq ℓ j F.ι (componentModelHom k' j hb) hM hN
(hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').ι
(hc.componentSpecialLift_ι k' j hb) hI`
(about 10 seconds). Stating the concrete instance as a public theorem did not finish: the header
`type_of% …` of a public theorem (but not of a `private theorem` or an `example`) runs for more
than 5 minutes. The composition isomorphism `Rb''_* ≅ Rr_* ⋙ Rι'_*` must be the named
`boundedConstructibleLowerStarCompOfEq`: with an inline `eqToHom (by rw [w]) ≫ …` in both the
data and the lemma, the kernel times out comparing the two `eqToHom` terms. With the objects of
the units `eB, …` left implicit (determined by `Functor.Monoidal.εIso`), the kernel times out on
the unit identity of `χ`, so they are passed as `𝟙_ _`. These units then use the monoidal structure
of the full subcategory, while the objects of `εIso` use the projection of
`monoidalCategory_boundedConstructible`; the kernel does not finish comparing the statement of
`lowerStarUnit_comp_of_eq` with the hypothesis `hc'` (it does for `lowerStarUnit_comp` and `hc`),
so `hc'` is proved in place by the proof of `lowerStarUnit_comp_of_eq`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Abstract

variable {DB DF DC DB' DF' DC' : Type*} [Category DB] [Category DF] [Category DC]
  [Category DB'] [Category DF'] [Category DC']

end Abstract

open Scheme

section LowerStarUnit

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ Rh_*` for a morphism `h` equal to `f ≫ g`. -/
noncomputable def boundedConstructibleLowerStarCompOfEq (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (w : f ≫ g = h) :
    boundedConstructibleLowerStar ℓ f ⋙
        boundedConstructibleLowerStar ℓ g ≅
      boundedConstructibleLowerStar ℓ h :=
  boundedConstructibleLowerStarComp ℓ f g ≪≫ eqToIso (by rw [w])

end LowerStarUnit

section Generic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {B F C : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  {B' F' C' : Over (Spec (.of k'))} [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom]
  [IsSeparated B'.hom] [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom] [IsSeparated F'.hom]
  [LocallyOfFiniteType C'.hom] [QuasiCompact C'.hom] [IsSeparated C'.hom]
  (j : B ⟶ F) [IsOpenImmersion j.left] [IsProper j.left] (ι : F ⟶ C)
  {M : NearbyCyclesModel B.left B'.left} {N : NearbyCyclesModel C.left C'.left} {g' : B' ⟶ C'}
  (φ : M.Hom N (j ≫ ι).left g'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (r : B' ⟶ F') (ι' : F' ⟶ C') (w : r ≫ ι' = g')

end Generic

end AlgebraicGeometry.ProEtale.CondensedRing
