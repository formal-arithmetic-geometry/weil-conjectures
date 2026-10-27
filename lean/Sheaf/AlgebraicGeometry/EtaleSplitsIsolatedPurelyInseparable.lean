module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Étale splitting of isolated fibre points with purely inseparable residue extensions

Source: Stacks Project, More on Morphisms, Tag 02LO,
`lemma-etale-splits-off-quasi-finite-part-technical-variant`; Morphisms, Tag 02GL
(blueprint: lem-sfb-etale-splits-isolated-purely-inseparable).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite list of distinct isolated fibre points splits into finite clopen pieces after
an étale neighbourhood, with singleton fibres and finite purely inseparable residue fields.
The clopen partition is the decomposition into open and closed subschemes.

Source: Stacks Project, More on Morphisms, Tag 02LO,
`lemma-etale-splits-off-quasi-finite-part-technical-variant`; Morphisms, Tag 02GL
(blueprint: lem-sfb-etale-splits-isolated-purely-inseparable).

Proof plan:
1. Use `def-pc-scheme-fibre` to view the given points in `X`. Apply
   `lem-weil-pbc-etale-local-finite-multiple-points` (02LM) to obtain finite open pieces
   with distinct singleton fibre points, purely inseparable residue fields, and exhaustion
   of all points over the prescribed points.
2. The neighbourhood residue extension is finite separable: on affine charts apply
   `lem-weil-pbc-etale-algebra-residue-field-separable`. Open restriction identifies the
   scheme stalks and residue fields (`def-weil-open-immersion`, `def-weil-residue-field`).
3. The projection is separated by `lem-weil-pbc-separated-base-change`. Each finite piece
   is proper by `lem-weil-pbc-finite-proper`; its inclusion is proper by
   `lem-weil-pbc-proper-over-separated`. Thus its image is closed by
   `def-weil-proper-morphism`, so each piece is clopen.
4. The pairwise intersections are closed in proper pieces, hence have closed images in
   the base. These images avoid the distinguished base point because the singleton fibre
   points are distinct. Remove their finite union to make the pieces disjoint.
5. Restrict the pieces to this open neighbourhood. Finiteness persists by
   `lem-weil-pbc-finite-morphism-permanence`; étaleness by
   `lem-weil-pbc-etale-composition-cancellation`. Open restriction preserves the singleton
   fibres and residue fields. Pullback pasting (`def-pc-fibre-product`) identifies the
   restricted total space with the new base change.
6. Take `W` to be the complement of the finite union of the pieces. It is clopen, and
   the disjoint open cover gives the scheme decomposition. With an empty list, `W` is
   the whole base change.
7. A point of `W` over the base point and an original listed point would, by the
   exhaustion in step 1, be the distinguished point of a retained piece, a contradiction.
   No finiteness of `W` and no flatness of `f` is used. -/
theorem exists_etale_splits_isolated_purelyInseparable
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    (s : S) (n : ℕ) (x : Fin n → f.fiber s)
    (hdistinct : Function.Injective x)
    (hisolated : ∀ i : Fin n, IsOpen ({x i} : Set (f.fiber s))) :
    ∃ (U : Scheme.{u}) (a : U ⟶ S) (u : U), Etale a ∧
      ∃ (hu : a u = s),
        ((S.residueFieldCongr hu.symm).hom ≫ a.residueFieldMap u).hom.Finite ∧
        @Algebra.IsSeparable (S.residueField s) (U.residueField u) _ _
          ((S.residueFieldCongr hu.symm).hom ≫ a.residueFieldMap u).hom.toAlgebra ∧
        ∃ (m : Fin n → ℕ) (W : (pullback a f).Opens)
          (V : (i : Fin n) → Fin (m i) → (pullback a f).Opens)
          (v : (i : Fin n) → (j : Fin (m i)) → (V i j).toScheme),
          IsCompl W (⨆ i : Fin n, ⨆ j : Fin (m i), V i j) ∧
          (∀ (i : Fin n) (j : Fin (m i)), IsClosed (V i j : Set ↥(pullback a f))) ∧
          Pairwise (fun b c : (i : Fin n) × Fin (m i) ↦
            Disjoint (V b.1 b.2) (V c.1 c.2)) ∧
          (∀ (i : Fin n) (j : Fin (m i)),
            IsFinite ((V i j).ι ≫ pullback.fst a f) ∧
            ∃ (hv : ((V i j).ι ≫ pullback.fst a f) (v i j) = u),
              (∀ w : (V i j).toScheme,
                ((V i j).ι ≫ pullback.fst a f) w = u → w = v i j) ∧
              ((V i j).ι ≫ pullback.snd a f) (v i j) = f.fiberι s (x i) ∧
              ((U.residueFieldCongr hv.symm).hom ≫
                ((V i j).ι ≫ pullback.fst a f).residueFieldMap (v i j)).hom.Finite ∧
              @IsPurelyInseparable (U.residueField u)
                ((V i j).toScheme.residueField (v i j)) _ _
                ((U.residueFieldCongr hv.symm).hom ≫
                  ((V i j).ι ≫ pullback.fst a f).residueFieldMap (v i j)).hom.toAlgebra) ∧
          (∀ w : W.toScheme, (W.ι ≫ pullback.fst a f) w = u →
            ∀ i : Fin n, (W.ι ≫ pullback.snd a f) w ≠ f.fiberι s (x i)) := by
  sorry

end AlgebraicGeometry
