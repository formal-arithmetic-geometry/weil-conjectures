/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteComposition
import Sheaf.AlgebraicGeometry.GroupoidInvariantOpenRestrictionDegree

/-!
# Pointed affine etale quasi-splitting of a scheme groupoid

Source: Stacks Project, More on Groupoids in Spaces, Tags 04S0 and 04RK(3),
with Situation `situation-quasi-splitting`
(blueprint: lem-sfb-affine-groupoid-pointed-quasisplitting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry

/-- A flat locally finitely presented, locally quasi-finite separated groupoid on an
 affine scheme admits a pointed affine etale neighborhood whose restricted groupoid
 contains an open finite locally free subgroupoid on all its objects.

Source: Stacks Project, Tags 04S0, 04RK(3), using the proof of Tag 04RZ with
"strong splitting" replaced by "quasi-splitting"
(blueprint: lem-sfb-affine-groupoid-pointed-quasisplitting).

The restricted relation is the existing iterated pullback. Its operations are
specified by their middle coordinates. The universally quantified composition
compatibility is the equality with the induced map on composable pairs: the
pullback universal property supplies a unique `q` for each `p`. For the open
subgroupoid, `k` is that induced map, fixed by both projection equations.

Proof:
1. Apply lem-sfb-section-marked-finite-parts-scheme to `s` and `e`, obtaining a
   separated etale parameter scheme `M`, a point above `u` with the same residue
   field, and a universal finite clopen part `Q`. Local quasi-finiteness implies
   local finite type (lem-weil-pbc-lqf-locally-finite-type), so
   lem-sfb-universal-finite-parts-groupoid gives a groupoid on `M` with arrows `Q`
   and finite source and target projections.
2. Let `E = R ×_U M` and `H = M ×_U R ×_U M`. Forgetting the target lift gives a
   separated etale morphism `H → E`, by lem-weil-pbc-separated-lqf-base-change and
   lem-weil-pbc-etale-scheme-base-change. The graph of `Q → H` over `E` is clopen
   by lem-weil-pbc-etale-section-clopen-immersion. Its composite with the open
   base change of `Q → E` is open (lem-weil-pbc-open-immersion-base-change).
   Thus `Q` identifies with an open subgroupoid `P₀` of `H`, including all units.
3. The map `H → R` is etale by base change and composition
   (lem-weil-pbc-etale-scheme-base-change,
   lem-weil-pbc-etale-composition-cancellation). Apply
   lem-sfb-scheme-etale-source-target-properties to obtain flatness and local
   finite presentation of both endpoint maps. Their factorizations into base
   changes of the old endpoint maps and the etale neighborhood give local
   quasi-finiteness (lem-weil-pbc-unramified-quasi-finite-at-points,
   lem-weil-pbc-separated-lqf-base-change, lem-a1-scheme-lqf-composition).
   Restricting to `P₀` preserves flatness and local finite presentation; its
   already finite projections are finite locally free (def-pc-finite-locally-free).
4. The orbit of the marked point in `Q` is finite by
   lem-weil-pbc-finite-closed-map-finite-fibres, and contains that point by the unit.
   Since `M → U` is separated etale and `U` is affine,
   lem-sfb-separated-lqf-affine-finite-set puts the orbit in an affine open.
   Then lem-sfb-locally-free-groupoid-invariant-affine supplies an invariant affine
   open `W` containing the orbit.
5. Restrict `Q` to `W`. Invariance identifies its source restriction with its
   target restriction and its two-sided restriction. The operations restrict by
   lem-a1-groupoid-invariant-open-restriction-degree. The finite projections stay
   finite by lem-weil-pbc-finite-morphism-permanence, and flatness and local finite
   presentation stay true by lem-sfb-scheme-etale-source-target-properties and
   lem-weil-pbc-etale-composition-cancellation. Its open inclusion into the full
   restricted relation is the base change of `P₀ → H`
   (lem-weil-pbc-open-immersion-base-change, def-pc-fibre-product).
6. The restriction `g : W → U` is etale by
   lem-weil-pbc-etale-composition-cancellation. Its marked residue-field map is an
   isomorphism by lem-weil-pbc-residue-field-point-naturality and step 1.
   Repeat step 3 for the full relation on `W` to obtain all six projection
   properties. Parameter schemes, pullbacks and opens stay in universe `u`,
   as required by def-weil-size-convention. -/
theorem affine_groupoid_pointed_quasisplitting
    {S : Scheme.{u}} {R U : Over S}
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s.left t.left ⟶ R.left)
    (hG : IsGroupoidScheme s.left t.left e.left i.left c)
    [IsAffine U.left] [IsSeparated s.left] [IsSeparated t.left]
    [Flat s.left] [Flat t.left]
    [LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left]
    (hs : s.left.IsLocallyQuasiFinite) (ht : t.left.IsLocallyQuasiFinite)
    (u₀ : U.left) :
    ∃ (W : Over S) (g : W ⟶ U) (w : W.left),
      IsAffine W.left ∧ Etale g.left ∧ g.left w = u₀ ∧
      IsIso (g.left.residueFieldMap w) ∧
      Flat (restrictedEtaleRelationSource s t g).left ∧
      Flat (restrictedEtaleRelationTarget s t g).left ∧
      LocallyOfFinitePresentation (restrictedEtaleRelationSource s t g).left ∧
      LocallyOfFinitePresentation (restrictedEtaleRelationTarget s t g).left ∧
      (restrictedEtaleRelationSource s t g).left.IsLocallyQuasiFinite ∧
      (restrictedEtaleRelationTarget s t g).left.IsLocallyQuasiFinite ∧
      ∃ (eW : W.left ⟶ (restrictedEtaleRelation s t g).left)
        (iW : (restrictedEtaleRelation s t g).left ⟶ (restrictedEtaleRelation s t g).left)
        (cW : pullback (restrictedEtaleRelationSource s t g).left
          (restrictedEtaleRelationTarget s t g).left ⟶ (restrictedEtaleRelation s t g).left),
        IsGroupoidScheme (restrictedEtaleRelationSource s t g).left
          (restrictedEtaleRelationTarget s t g).left eW iW cW ∧
        eW ≫ (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.snd g s).left =
          g.left ≫ e.left ∧
        iW ≫ (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.snd g s).left =
          (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.snd g s).left ≫ i.left ∧
        (∀ (H : Scheme.{u})
          (p : H ⟶ pullback (restrictedEtaleRelationSource s t g).left
            (restrictedEtaleRelationTarget s t g).left)
          (q : H ⟶ pullback s.left t.left),
          p ≫ pullback.fst _ _ ≫
              (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.snd g s).left =
            q ≫ pullback.fst s.left t.left →
          p ≫ pullback.snd _ _ ≫
              (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.snd g s).left =
            q ≫ pullback.snd s.left t.left →
          p ≫ cW ≫ (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.snd g s).left =
            q ≫ c) ∧
        ∃ (P : (restrictedEtaleRelation s t g).left.Opens)
          (eP : W.left ⟶ P.toScheme) (iP : P.toScheme ⟶ P.toScheme)
          (cP : pullback (P.ι ≫ (restrictedEtaleRelationSource s t g).left)
            (P.ι ≫ (restrictedEtaleRelationTarget s t g).left) ⟶ P.toScheme)
          (k : pullback (P.ι ≫ (restrictedEtaleRelationSource s t g).left)
            (P.ι ≫ (restrictedEtaleRelationTarget s t g).left) ⟶
              pullback (restrictedEtaleRelationSource s t g).left
                (restrictedEtaleRelationTarget s t g).left),
          IsGroupoidScheme (P.ι ≫ (restrictedEtaleRelationSource s t g).left)
            (P.ι ≫ (restrictedEtaleRelationTarget s t g).left) eP iP cP ∧
          eP ≫ P.ι = eW ∧ iP ≫ P.ι = P.ι ≫ iW ∧
          k ≫ pullback.fst _ _ = pullback.fst _ _ ≫ P.ι ∧
          k ≫ pullback.snd _ _ = pullback.snd _ _ ≫ P.ι ∧
          cP ≫ P.ι = k ≫ cW ∧
          (P.ι ≫ (restrictedEtaleRelationSource s t g).left).IsFiniteLocallyFree ∧
          (P.ι ≫ (restrictedEtaleRelationTarget s t g).left).IsFiniteLocallyFree := by
  sorry

end AlgebraicGeometry
