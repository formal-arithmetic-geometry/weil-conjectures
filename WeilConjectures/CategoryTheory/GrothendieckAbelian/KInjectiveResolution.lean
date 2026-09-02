/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeGeneratingSet
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Every Grothendieck abelian category has K-injective resolutions

Let `C` be a Grothendieck abelian category. In this file we show that every cochain complex in
`C` admits a monomorphic quasi-isomorphism into a K-injective complex, i.e. that
`CategoryTheory.Abelian.HasKInjectiveResolutions C` holds. This is a theorem of
Alonso Tarrío–Jeremías López–Souto Salorio and of Serpé.

The proof runs the small object argument in `CochainComplex C ℤ` for the Serpé generating set
`CochainComplex.serpeGeneratingSet C`, exactly as
`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean` runs it for the
generating monomorphisms of `C`. Since that set has the same right lifting property as the
class of all monomorphic quasi-isomorphisms, and since the retracts of transfinite compositions
of pushouts of coproducts of monomorphic quasi-isomorphisms are again monomorphic
quasi-isomorphisms, the monomorphic quasi-isomorphisms are the maps with the left lifting
property with respect to their own right lifting property. Hence any morphism factors
functorially as a monomorphic quasi-isomorphism followed by a morphism with the right lifting
property with respect to all monomorphic quasi-isomorphisms; applying this to `K ⟶ 0` gives a
monomorphic quasi-isomorphism `K ⟶ L` with `L ⟶ 0` in the right class, and such an `L` is
K-injective by `CochainComplex.isKInjective_of_rlp`.

## Main results

- `CochainComplex.llp_rlp_monoQuasiIso`: the monomorphic quasi-isomorphisms of cochain
  complexes in a Grothendieck abelian category are exactly the morphisms with the left lifting
  property with respect to the morphisms with the right lifting property with respect to them.
- `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`: every Grothendieck
  abelian category has K-injective resolutions.

## References

* L. Alonso Tarrío, A. Jeremías López, M. J. Souto Salorio, *Localization in categories of
  complexes and unbounded resolutions*
* C. Serpé, *Resolution of unbounded complexes in Grothendieck categories*
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MorphismProperty HomologicalComplex ZeroObject

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The Serpé generating set has the same right lifting property as the class of all
monomorphic quasi-isomorphisms. This is `CochainComplex.serpeGeneratingSet_rlp`, spelled with
`HomologicalComplex.monoQuasiIso`. -/
private lemma serpeGeneratingSet_rlp' :
    (serpeGeneratingSet C).rlp = (monoQuasiIso C (ComplexShape.up ℤ)).rlp := by
  dsimp only [monoQuasiIso]
  exact serpeGeneratingSet_rlp.{w} C

/-- In a Grothendieck abelian category, the monomorphic quasi-isomorphisms of cochain complexes
are exactly the morphisms having the left lifting property with respect to the morphisms having
the right lifting property with respect to all monomorphic quasi-isomorphisms. -/
lemma llp_rlp_monoQuasiIso :
    (monoQuasiIso C (ComplexShape.up ℤ)).rlp.llp = monoQuasiIso C (ComplexShape.up ℤ) := by
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← serpeGeneratingSet_rlp' C, llp_rlp_of_hasSmallObjectArgument]
  refine le_trans ?_ (transfiniteCompositions_coproducts_pushouts_le.{w} C)
  apply retracts_monotone
  apply transfiniteCompositions_monotone
  apply pushouts_monotone
  apply coproducts_monotone
  exact serpeGeneratingSet_le C

instance hasFunctorialFactorization_monoQuasiIso :
    HasFunctorialFactorization (monoQuasiIso C (ComplexShape.up ℤ))
      (monoQuasiIso C (ComplexShape.up ℤ)).rlp := by
  rw [← serpeGeneratingSet_rlp' C, ← llp_rlp_monoQuasiIso.{w} C, ← serpeGeneratingSet_rlp' C]
  infer_instance

/-- A (functorial) factorization of any morphism of cochain complexes in a Grothendieck abelian
category as a monomorphic quasi-isomorphism followed by a morphism which has the right lifting
property with respect to all monomorphic quasi-isomorphisms. -/
noncomputable abbrev monoQuasiIsoMapFactorizationDataRlp {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    MapFactorizationData (monoQuasiIso C (ComplexShape.up ℤ))
      (monoQuasiIso C (ComplexShape.up ℤ)).rlp f :=
  (functorialFactorizationData _ _).factorizationData f

end CochainComplex

namespace CategoryTheory.Abelian

/-- Every Grothendieck abelian category has K-injective resolutions: any cochain
complex admits a monomorphic quasi-isomorphism into a K-injective complex. This is a
theorem of Alonso Tarrío–Jeremías López–Souto Salorio and Serpé. -/
instance hasKInjectiveResolutions_of_isGrothendieckAbelian
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasKInjectiveResolutions C where
  exists_isKInjective K := by
    let fac := CochainComplex.monoQuasiIsoMapFactorizationDataRlp.{w} C (0 : K ⟶ 0)
    have hL : CochainComplex.IsKInjective fac.Z :=
      CochainComplex.isKInjective_of_rlp fac.p (isZero_zero _) fac.hp
    obtain ⟨h₁, h₂⟩ := (monoQuasiIso_iff fac.i).mp fac.hi
    exact ⟨fac.Z, hL, fac.i, h₁, h₂⟩

end CategoryTheory.Abelian
