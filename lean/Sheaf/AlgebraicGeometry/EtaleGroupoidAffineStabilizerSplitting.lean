/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

import Sheaf.AlgebraicGeometry.GroupoidInvariantOpenRestrictionDegree
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Affine etale splitting at a finite stabilizer

Source: Stacks Project, `spaces-more-groupoids.tex`, Tags 0DTE, 0DTB and 04RK(2),
with finite locally free projections as in Tag 02KB
(blueprint: lem-sfb-etale-groupoid-affine-stabilizer-splitting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine scheme groupoid admits a pointed affine etale splitting at a finite stabilizer.

Source: Stacks Project, Tags 0DTE (`lemma-splitting-affine-scheme`), 0DTB and 04RK(2)
(blueprint: lem-sfb-etale-groupoid-affine-stabilizer-splitting).

The equalizer of `s,t` is the stabilizer scheme: its test points are precisely loops.
Its map to `V` is `equalizer.ι s t ≫ s`. This is canonically the diagonal pullback
`R ×_(V ×_S V) V`, because `s ≫ p = t ≫ p`.
The two cartesian squares in the conclusion construct `A = R ×_(s,V,h) V'` and
`R' = A ×_(a ≫ t,V,h) V'`, hence exactly `R ×_(V ×_S V) (V' ×_S V')`.
The source, target and arrow projection of `R'` are `r ≫ b`, `t'` and `r ≫ a`.
Compatibility equations characterize all its induced operations. The open `P` has
its restricted structure sheaf; its operations commute with the inclusion `P.ι`.
The last clause contains the whole scheme-theoretic stabilizer fibre, also for
nonreduced fibres, and does not replace that fibre by set-theoretic endpoint fibres.

Proof plan:
1. Set `F = s.fiber v`. By lem-weil-pbc-separated-lqf-base-change and
   lem-weil-pbc-lqf-locally-finite-type it is locally quasi-finite and locally of finite
   type over the residue field. The singleton opens of
   lem-weil-pbc-quasi-finite-at-point-isolated make it discrete and zero-dimensional.
   By lem-sfb-zero-dimensional-field-space-components its components are finite local
   Artinian schemes. The finite stabilizer meets finitely many components by
   lem-weil-pbc-finite-closed-map-finite-fibres. Their union `Z_v` is clopen and finite
   by lem-weil-pbc-finite-coproduct, and the stabilizer factors surjectively through it.
2. Apply lem-sfb-scheme-groupoid-universal-finite-part to obtain the separated etale
   parameter scheme `M`, finite locally free groupoid `Q`, and open immersion into
   the restriction of `R`. The pair `(v,Z_v)` gives a residue-field-valued point `w`.
   The field maps from the residue field of `v` to that of `w` and back compose to
   the identity, so the first is an isomorphism.
3. For a field-valued loop over `w`, right translation preserves the stabilizer and
   the support of `Z_v`, also after field extension by lem-weil-pbc-surjective-base-change.
   It therefore preserves that open subscheme (def-weil-open-immersion). The target
   formula of lem-sfb-scheme-groupoid-universal-finite-part shows that the corresponding
   arrow of `Q` has both endpoints `w`. Pullback universality identifies it with the
   original loop. Thus the whole stabilizer fibre lies in `Q`.
4. The orbit of `w` under `Q` is finite by lem-weil-pbc-finite-closed-map-finite-fibres.
   The map `M` to the affine `V` is separated and locally quasi-finite by
   lem-weil-pbc-unramified-quasi-finite-at-points. Apply
   lem-sfb-separated-lqf-affine-finite-set and then
   lem-sfb-locally-free-groupoid-invariant-affine to find an invariant affine open `B`
   containing the orbit, hence containing `w` by the unit.
5. Take `V' = B`. The map to `V` is etale by
   lem-weil-pbc-etale-composition-cancellation. By
   lem-a1-groupoid-invariant-open-restriction-degree the groupoid restricts to `B`.
   Invariance makes both projections base changes of those of `Q`; they are finite,
   flat and locally of finite presentation by lem-weil-pbc-finite-morphism-permanence,
   lem-weil-pbc-flat-morphism-base-change and lem-weil-pbc-qcqs-morphism-permanence.
   Thus they satisfy def-pc-finite-locally-free without a Noetherian hypothesis.
6. The two pullback squares give the induced restriction of `R`. Pull back `Q` into
   it; lem-weil-pbc-open-immersion-base-change gives the open `P`. All operations
   restrict because this is a groupoid morphism identical on objects. Step 3 gives
   containment of the entire stabilizer fibre. Its inverse image of `P` has full
   underlying open and therefore its whole structure sheaf. Open restriction also
   preserves the residue field at `w`. -/
theorem IsGroupoidScheme.exists_affine_etale_stabilizer_splitting
    {S V R : Scheme.{u}} (p : V ⟶ S) (s t : R ⟶ V)
    (e : V ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : IsGroupoidScheme s t e i c) (hp : s ≫ p = t ≫ p)
    [IsAffine V] [IsClosedImmersion (pullback.diagonal s)]
    [IsClosedImmersion (pullback.diagonal t)] [Flat s] [Flat t]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t]
    (hqs : s.IsLocallyQuasiFinite) (hqt : t.IsLocallyQuasiFinite) (v : V)
    [IsFinite ((equalizer.ι s t ≫ s).fiberToSpecResidueField v)] :
    ∃ (V' : Scheme.{u}) (h : V' ⟶ V) (v' : V'),
      IsAffine V' ∧ Etale h ∧ h v' = v ∧ IsIso (h.residueFieldMap v') ∧
      ∃ (A R' : Scheme.{u}) (a : A ⟶ R) (b : A ⟶ V')
        (r : R' ⟶ A) (t' : R' ⟶ V'),
        IsPullback a b s h ∧ IsPullback r t' (a ≫ t) h ∧
        ∃ (e' : V' ⟶ R') (i' : R' ⟶ R') (c' : pullback (r ≫ b) t' ⟶ R')
          (hs : (r ≫ b) ≫ h = (r ≫ a) ≫ s)
          (ht : t' ≫ h = (r ≫ a) ≫ t),
          IsGroupoidScheme (r ≫ b) t' e' i' c' ∧
          e' ≫ (r ≫ a) = h ≫ e ∧
          i' ≫ (r ≫ a) = (r ≫ a) ≫ i ∧
          c' ≫ (r ≫ a) =
            pullback.map (r ≫ b) t' s t (r ≫ a) (r ≫ a) h hs ht ≫ c ∧
          ∃ (P : R'.Opens) (eP : V' ⟶ P.toScheme) (iP : P.toScheme ⟶ P.toScheme)
            (cP : pullback (P.ι ≫ (r ≫ b)) (P.ι ≫ t') ⟶ P.toScheme),
            IsGroupoidScheme (P.ι ≫ (r ≫ b)) (P.ι ≫ t') eP iP cP ∧
            eP ≫ P.ι = e' ∧ iP ≫ P.ι = P.ι ≫ i' ∧
            cP ≫ P.ι =
              pullback.map (P.ι ≫ (r ≫ b)) (P.ι ≫ t') (r ≫ b) t'
                P.ι P.ι (𝟙 V') (Category.comp_id _) (Category.comp_id _) ≫ c' ∧
            (P.ι ≫ (r ≫ b)).IsFiniteLocallyFree ∧ (P.ι ≫ t').IsFiniteLocallyFree ∧
            ∀ z : (equalizer.ι (r ≫ b) t' ≫ (r ≫ b)).fiber v',
              ((equalizer.ι (r ≫ b) t' ≫ (r ≫ b)).fiberι v' ≫
                equalizer.ι (r ≫ b) t') z ∈ P := by
  sorry

end AlgebraicGeometry
