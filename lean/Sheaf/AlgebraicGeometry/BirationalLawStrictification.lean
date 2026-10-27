/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NZ
-/
module

public import Sheaf.AlgebraicGeometry.RelativeBirationalGroupLaw
public import Sheaf.AlgebraicGeometry.StrictBirationalLaw
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.SmoothFibrewiseDenseOpenBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Strictification of a birational group law

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §5.2 Proposition 2,
printed pp.115--117; generic-fibre preservation by the same construction, as used in
§5.1 Theorem 5 (blueprint: lem-sfb-birational-law-strictification).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Agreement of the strict law on an open subscheme with the original rational law.
The two projection equations fix the factorization through the original domain uniquely.
Source: BLR 2.5 and 5.2 Proposition 2 (blueprint: lem-sfb-birational-law-strictification). -/
def RelativeGroupLaw.Representative.AgreesWithStrictRestriction
    {S : Scheme.{u}} {X : Over S} (m : RelativeGroupLaw.Representative (X ⊗ X) X)
    (A : X.left.Opens) (n : RelativeBirational.StrictLaw (Over.mk (A.ι ≫ X.hom))) : Prop :=
  ∃ (E : (RelativeBirational.square (Over.mk (A.ι ≫ X.hom))).left.Opens)
    (hE : E ≤ n.mul.domain),
    RelativeBirational.FibrewiseDense
      (RelativeBirational.square (Over.mk (A.ι ≫ X.hom))).hom E ∧
    ∃ k : E.toScheme ⟶ m.domain.toScheme,
      k ≫ m.domain.ι ≫ pullback.fst X.hom X.hom =
        E.ι ≫ pullback.fst (A.ι ≫ X.hom) (A.ι ≫ X.hom) ≫ A.ι ∧
      k ≫ m.domain.ι ≫ pullback.snd X.hom X.hom =
        E.ι ≫ pullback.snd (A.ι ≫ X.hom) (A.ι ≫ X.hom) ≫ A.ι ∧
      (RelativeBirational.square (Over.mk (A.ι ≫ X.hom))).left.homOfLE hE ≫
        n.mul.hom ≫ A.ι = k ≫ m.hom.left

/-- The representative is defined on the whole base-changed square and gives a group law.
This uses the given representative and the canonical base-changed projections.
Source: BLR 5.1 Theorem 5 (blueprint: lem-sfb-birational-law-strictification). -/
def RelativeGroupLaw.Representative.IsGroupBaseChange
    {S T : Scheme.{u}} {X : Over S} (m : RelativeGroupLaw.Representative (X ⊗ X) X)
    (g : T ⟶ S) : Prop :=
  IsIso ((Over.pullback g).map m.inclusion) ∧
  ∃ (_group : GrpObj ((Over.pullback g).obj X)),
    (Over.pullback g).map m.hom =
      CartesianMonoidalCategory.lift
        ((Over.pullback g).map (m.inclusion ≫ CartesianMonoidalCategory.fst X X))
        ((Over.pullback g).map (m.inclusion ≫ CartesianMonoidalCategory.snd X X)) ≫
        MonObj.mul

/-- A birational group law over a field or a discrete valuation ring becomes strict on a
fibrewise dense open. If its generic fibre is an everywhere-defined group law, that open
can contain the whole generic fibre. `FractionRing B` is a canonical choice of fraction
field; the image condition is independent of its choice.

Source: BLR §5.2 Proposition 2 and §5.1 Theorem 5
(blueprint: lem-sfb-birational-law-strictification).

Proof plan (the node's six steps):
1. Intersect base-dense isomorphism charts for the two translations and the domain of `m`.
   Smooth base change and composition (lem-pc-proper-base-change, lem-trf-smooth-composition)
   make the product smooth. Fibrewise schematic density
   (lem-sfb-smooth-fibrewise-dense-open-base-change) and separated-target uniqueness
   (lemma-nagata-ext-scheme-theoretically-dominant-separated) make representatives agree.
   Obtain common charts `U ≅ V`, `U ≅ W` and put `Z = U ∩ V ∩ W`.
2. Apply lem-sfb-product-projection-density-shrink to `Z`, obtaining `A`. Base change of
   smooth fibrewise density allows imposing that the other coordinate belongs to `A`.
   Work on each projection fibre over the residue field of its point.
3. Set `U' = U ∩ (A × A) ∩ m⁻¹(A)`, `V' = Φ(U')`, `W' = Ψ(U')`. Slice the first chart
   over its fixed first coordinate, and the second over its fixed second coordinate.
   Intersect dense opens and transport density through these isomorphisms. This gives
   both densities of `U'`, first-projection density of `V'` and second-projection density
   of `W'`.
4. For the remaining two conditions, slice `m` over a point `a ∈ A`. Its fibre is
   isomorphic both to `V ∩ (X × {a})` and to `W ∩ ({a} × X)`. Pull back their dense
   intersections with `A` and intersect. Push forward through the other isomorphism.
   This gives first-projection density of `W'` and second-projection density of `V'`.
5. The resulting law on `A` is strict, inherits associativity, and represents the
   restricted original rational law. Smoothness, separatedness and finite type hold on `A`.
6. If the generic fibre is a group scheme, its translation inverses are morphisms
   everywhere. Glue the initial charts to these full generic-fibre charts; uniqueness
   on dense overlaps justifies gluing. The preservation clause of projection-density
   shrinking then gives `A` containing the generic fibre, and steps 3--5 still apply. -/
theorem exists_strict_birational_law_open
    (B : Type u) [CommRing B] [IsDomain B]
    (hB : IsField B ∨ IsDiscreteValuationRing B)
    (X : Over (Spec (CommRingCat.of B)))
    [Smooth X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (hX : ∀ s : Spec (CommRingCat.of B), Nonempty (X.hom.fiber s))
    (m : RelativeGroupLaw.Representative (X ⊗ X) X)
    (hm : RelativeGroupLaw.IsBirationalGroupLaw m) :
    ∃ A : X.left.Opens,
      RelativeGroupLaw.IsFiberwiseDense X (A : Set X.left) ∧
      Smooth (A.ι ≫ X.hom) ∧ IsSeparated (A.ι ≫ X.hom) ∧
      LocallyOfFiniteType (A.ι ≫ X.hom) ∧ QuasiCompact (A.ι ≫ X.hom) ∧
      (∃ n : RelativeBirational.StrictLaw (Over.mk (A.ι ≫ X.hom)),
        m.AgreesWithStrictRestriction A n) ∧
      (IsDiscreteValuationRing B →
        m.IsGroupBaseChange (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))) →
        Set.range (pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))) ⊆ (A : Set X.left)) :=
  sorry

end AlgebraicGeometry
