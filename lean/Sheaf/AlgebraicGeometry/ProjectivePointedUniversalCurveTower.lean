/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition

/-! # Projective iteration of the universal stable pointed curve

Source: Knudsen, The projectivity of the moduli space of stable curves II (1983),
§2, Corollary 2.6, and Stacks Tags 087S, 01WE and 01T3
(blueprint: lem-sfb-projective-pointed-universal-curve-tower).

The structure `KnudsenPointedCurveDatum` packages precisely the witnesses of the recorded
Knudsen theorem. It specifies the forgetful morphism and its stabilization convention;
it does not choose a family from an arbitrary existence assertion. Tower bases are
encoded by the bases of actual `StablePointedModuli` objects. The transition base is
the preceding family's total scheme, and the extra section is the actual diagonal.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The chosen contraction and stabilization convention, packaged without any new
construction: these are exactly the witnesses and clauses of
`exists_knudsen_pointed_forgetful_universal_curve`. In particular the representing
functor is normalized by the contracted extra point, with all ordered labels kept.
Source: Knudsen II §2, Corollary 2.6 and Theorem 2.7
(blueprint: lem-sfb-projective-pointed-universal-curve-tower). -/
structure KnudsenPointedCurveDatum (S : Scheme.{u}) (g r : ℕ) where
  contraction : BasedFunctor (StablePointedModuli.based S g (r + 1))
    (StablePointedUniversalCurve.based S g r)
  stabilization : BasedFunctor (StablePointedUniversalCurve.based S g r)
    (StablePointedModuli.based S g (r + 1))
  unitIso : ModuliTwoIso (BasedFunctor.id (StablePointedModuli.based S g (r + 1)))
    (contraction.comp stabilization)
  counitIso : ModuliTwoIso (stabilization.comp contraction)
    (BasedFunctor.id (StablePointedUniversalCurve.based S g r))
  curveMap : ∀ Y : StablePointedModuli S g (r + 1),
    Y.curve ⟶ (contraction.obj Y).family.curve
  curveMap_over : ∀ Y : StablePointedModuli S g (r + 1),
    curveMap Y ≫ (contraction.obj Y).family.projection =
      Y.projection ≫ eqToHom (congrArg Over.left (contraction.w_obj Y).symm)
  naturality : ∀ {Y Z : StablePointedModuli S g (r + 1)} (h : Y ⟶ Z),
    h.map ≫ curveMap Z = curveMap Y ≫ (contraction.map h).val.map
  old_markings : ∀ (Y : StablePointedModuli S g (r + 1)) (i : Fin r),
    Y.sections i.castSucc ≫ curveMap Y =
      eqToHom (congrArg Over.left (contraction.w_obj Y).symm) ≫
        (contraction.obj Y).family.sections i
  last_marking : ∀ Y : StablePointedModuli S g (r + 1),
    Y.sections (Fin.last r) ≫ curveMap Y =
      eqToHom (congrArg Over.left (contraction.w_obj Y).symm) ≫ (contraction.obj Y).extra
  geometry : ∀ Y : StablePointedModuli S g (r + 1),
    StablePointedUniversalCurve.HasFiberGeometry Y (contraction.obj Y)
      (eqToHom (congrArg Over.left (contraction.w_obj Y).symm)) (curveMap Y) (curveMap_over Y)
  representation : ∀ X : StablePointedModuli S g r,
    ∃ R : BasedFunctor
        (moduliTwoFiberProduct X.familyMap
          (StablePointedUniversalCurve.forgetful contraction))
        (discreteModuli (yoneda.obj X.totalScheme)),
      R.toFunctor.IsEquivalence ∧
      (∀ Z, (yoneda.preimage (R.obj Z).hom).left =
        eqToHom (congrArg Over.left (R.w_obj Z)) ≫
          StablePointedUniversalCurve.representedPoint contraction X Z) ∧
      (∀ Z, (yoneda.preimage (R.obj Z).hom).left ≫ X.projection =
        eqToHom (congrArg Over.left (R.w_obj Z)) ≫
          (yoneda.preimage Z.obj.left.hom).left) ∧
      IsProjectiveBundle X.projection ∧ Flat X.projection ∧
        LocallyOfFinitePresentation X.projection ∧ QuasiCompact X.projection ∧
        QuasiSeparated X.projection
  smooth_disjoint : ∀ X : StablePointedUniversalCurve S g r,
    Smooth X.family.projection →
    (∀ i : Fin r, Disjoint (Set.range X.extra) (Set.range (X.family.sections i))) →
    IsIso (curveMap (stabilization.obj X) ≫ (counitIso.val.hom.app X).val.map)
  base_change : ∀ (X : StablePointedModuli S g r) (T : Over S) (a : T ⟶ X.base),
    IsStablePointedCurve (X.pullback T a).projection (X.pullback T a).sections
      (X.pullback T a).section_projection

/-- The pulled-back old family over its own total scheme, with the unrestricted
extra section given by the diagonal. The second factor of `X ×_T X` is the base;
the old labelled sections are the recorded paired pullback sections.
Source: Knudsen II §2, the universal-curve identification
(blueprint: lem-sfb-projective-pointed-universal-curve-tower). -/
def StablePointedModuli.tautologicalExtra {S : Scheme.{u}} {g r : ℕ}
    (X : StablePointedModuli S g r) : StablePointedUniversalCurve S g r where
  family := X.pullback X.totalScheme (Over.homMk X.projection)
  extra := pullback.diagonal X.projection
  extra_projection := pullback.diagonal_snd X.projection

/-- Finite iteration of the chosen Knudsen universal curve over a specified
finite-type H-projective field scheme. The family at the next stage is the
stabilization of the diagonal extra section, up to a labelled isomorphism over the
specified base identification. The normalized representing equivalence states the
2-cartesian property over every test scheme and retains its comparison isomorphism.

Source: Knudsen II §2, Corollary 2.6; Stacks 087S, 01WE and 01T3
(blueprint: lem-sfb-projective-pointed-universal-curve-tower).

Proof:
1. Induct on the tower length, retaining every earlier family, transition and square.
At zero retain the specified `a₀`; there are no transitions or squares.
2. Apply lem-sfb-knudsen-pointed-forgetful-universal-curve to the last family.
Take its total scheme as the next base, its projection as the transition, and
stabilize `tautologicalExtra`. Contraction and stabilization, with their isomorphisms
over schemes, give the comparison and the normalized representing equivalence.
Evaluating that equivalence at a test scheme gives exactly the groupoid of a base
map, a new labelled family and an isomorphism of its contraction with the old
pullback. The diagonal is allowed to meet a marking or a node.
3. Choose an H-projective embedding of the old base over the field. Apply
lem-weil-pbc-projective-ample-invertible to obtain an ample invertible sheaf.
Apply lem-trf-projective-bundle-to-h-projective to the bundle-projective universal
curve, then lem-trf-h-projective-composition to its map to the field spectrum.
4. Finite presentation implies local finite type, and includes quasi-compactness.
Apply lem-sfb-finite-type-composition-base-change to the transition and the old
structure map. This extends the invariant and finite induction gives all stages.
5. Apply the arbitrary-base-change clause of Knudsen to every constructed family.
Its stable predicate spells out nodal geometric fibres, disjoint smooth labelled
sections and component stability inequalities. Projectivity and the finite
presentation conditions persist under arbitrary base change, and the recorded
moduli pullback retains arithmetic genus. No finiteness assumption is made on the
test scheme. -/
theorem exists_projective_pointed_universal_curve_tower
    (k : Type u) [Field k] (g n : ℕ) (hg : 2 ≤ g)
    (T₀ : Over (Spec (.of k))) (a₀ : StablePointedModuli (Spec (.of k)) g 0)
    (ha₀ : a₀.base = T₀) (hft : LocallyOfFiniteType T₀.hom)
    (hqc : QuasiCompact T₀.hom) (hp : IsHProjective T₀.hom) :
    ∃ (D : (r : Fin n) → KnudsenPointedCurveDatum (Spec (.of k)) g r.val)
      (a : (r : Fin (n + 1)) → StablePointedModuli (Spec (.of k)) g r.val)
      (hb : ∀ r : Fin n, (a r.succ).base = (a r.castSucc).totalScheme),
      a ⟨0, Nat.zero_lt_succ n⟩ = a₀ ∧
      (∀ r : Fin (n + 1), LocallyOfFiniteType (a r).base.hom ∧
        QuasiCompact (a r).base.hom ∧ IsHProjective (a r).base.hom) ∧
      (∀ r : Fin n,
        IsHProjective (a r.castSucc).projection ∧ Flat (a r.castSucc).projection ∧
        LocallyOfFinitePresentation (a r.castSucc).projection ∧
        QuasiCompact (a r.castSucc).projection ∧ QuasiSeparated (a r.castSucc).projection ∧
        IsProjectiveBundle (a r.castSucc).projection ∧
        ∃ e : a r.succ ≅ (D r).stabilization.obj (a r.castSucc).tautologicalExtra,
          e.hom.base = eqToHom (hb r) ≫
            eqToHom ((D r).stabilization.w_obj (a r.castSucc).tautologicalExtra).symm) ∧
      (∀ r : Fin n,
        ∃ R : BasedFunctor
            (moduliTwoFiberProduct (a r.castSucc).familyMap
              (StablePointedUniversalCurve.forgetful (D r).contraction))
            (discreteModuli (yoneda.obj (a r.castSucc).totalScheme)),
          R.toFunctor.IsEquivalence ∧
          (∀ Z, (yoneda.preimage (R.obj Z).hom).left =
            eqToHom (congrArg Over.left (R.w_obj Z)) ≫
              StablePointedUniversalCurve.representedPoint
                (D r).contraction (a r.castSucc) Z) ∧
          (∀ Z, (yoneda.preimage (R.obj Z).hom).left ≫ (a r.castSucc).projection =
            eqToHom (congrArg Over.left (R.w_obj Z)) ≫
              (yoneda.preimage Z.obj.left.hom).left)) ∧
      (∀ (r : Fin (n + 1)) (B : Over (Spec (.of k))) (b : B ⟶ (a r).base),
        IsStablePointedCurve ((a r).pullback B b).projection ((a r).pullback B b).sections
          ((a r).pullback B b).section_projection ∧
        QuasiCompact ((a r).pullback B b).projection ∧
        QuasiSeparated ((a r).pullback B b).projection) := by
  sorry

end AlgebraicGeometry
