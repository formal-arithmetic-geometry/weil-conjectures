/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import WeilConjectures.Compactification.Triangle
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Compactification.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Compatible compactification towers over arbitrary bases

Source: Stacks Project, Tag 0F7J, proof of `lemma-shriek-composition`, with supplied
compactifications over arbitrary bases as in `WeilConjectures.Compactification.Comp` and
`WeilConjectures.Compactification.Triangle`
(blueprint: lem-cbc-compactifiable-compatible-tower).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Supplied compactifications extend to a compatible tower; towers survive arbitrary base
change and any two have a common refinement. `Triangle` records the intermediate scheme up to
its unique isomorphism with the displayed fibre product; the first clause uses the literal
fibre product via `restrict`. Its field `q` is the arrow called `b` in the node.

Source: Stacks Project, Tag 0F7J, proof of `lemma-shriek-composition`, and the supplied-data
construction in upstream `Compactification/Comp.lean` and `Triangle.lean`.
(blueprint: lem-cbc-compactifiable-compatible-tower)

Proof plan:
1. Embed `X` in `W ×_Z Ybar` by `(a₀, f ≫ i)`. The projection to `W` is separated;
   quasi-compact immersion cancellation (`lem-cbc-qc-immersion-cancellation`) applies.
2. Take its scheme-theoretic image, using `def-nagata-immersion-compactification` and
   `lemma-nagata-immersion-into-proper`. The closed image inclusion and proper projections
   make both ambient maps proper (`lem-pc-proper-base-change`,
   `lem-weil-pbc-closed-immersion-proper`, `lem-weil-pbc-proper-composition`).
3. Restrict over `Y`. Fibre-product uniqueness (`def-pc-fibre-product`) and monicity of `i`
   identify the induced open map as a base change of `a`; openness and quasi-compactness
   follow from `lem-weil-pbc-open-immersion-base-change` and `lem-pc-quasi-compact-base-change`.
4. Pull back the diagram over any `Z'`. The same properties and equations survive;
   `lem-pod-separated-finite-type-base-change` supplies the properties of `f'` and `h'`.
   No claim that scheme-theoretic image commutes with arbitrary base change is needed.
5. For two towers, `lem-cbc-compactifiable-cofiltered` gives a common compactification `D`
   of `Y` over `Z`, with proper maps to both original ambient schemes of `Y`.
6. Close `X` in the product over `D` of the two pulled-back ambient schemes of `X`.
   Cancellation and the immersion construction again give the new compactification.
   Maps to the old ambient schemes are proper by `lemma-nagata-proper-to-separated-target`.
7. Restrict to `Y`. The projection identities give all seven refinement equations;
   properness of the intermediate maps follows from the same proper-to-separated lemma.
-/
theorem exists_compactifiable_compatible_tower
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (d : Compactification h) (c : Compactification (f ≫ h)) :
    (∃ (e : Compactification (f ≫ d.i)) (v : e.Z ⟶ c.Z),
      IsProper v ∧ e.i ≫ v = c.i ∧ v ≫ c.g = e.g ≫ d.g ∧
      QuasiCompact e.i ∧ QuasiCompact (pullback.fst e.g d.i) ∧
      QuasiCompact e.restrict.i ∧ IsOpenImmersion (pullback.fst e.g d.i) ∧
      IsOpenImmersion e.restrict.i ∧ IsProper e.restrict.g ∧
      e.restrict.i ≫ pullback.fst e.g d.i = e.i ∧
      e.restrict.i ≫ e.restrict.g = f ∧ IsProper (e.g ≫ d.g) ∧
      IsPullback e.restrict.g (pullback.fst e.g d.i) d.i e.g) ∧
    (∀ (T : Compactification.Triangle f h) (v : T.cfg.Z ⟶ c.Z),
      IsProper v → T.cfg.i ≫ v = c.i → v ≫ c.g = T.cfg.g →
      ∀ (Z' : Scheme.{u}) (k : Z' ⟶ Z),
      ∃ (f' : pullback (f ≫ h) k ⟶ pullback h k),
        IsPullback (pullback.fst (f ≫ h) k) f' f (pullback.fst h k) ∧
        IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧
        IsSeparated (pullback.snd h k) ∧ LocallyOfFiniteType (pullback.snd h k) ∧
        QuasiCompact (pullback.snd h k) ∧
        ∃ (T' : Compactification.Triangle f' (pullback.snd h k))
          (rA : T'.cfg.Z ⟶ T.cfg.Z) (rB : T'.cg.Z ⟶ T.cg.Z)
          (rU : T'.cf.Z ⟶ T.cf.Z) (v' : T'.cfg.Z ⟶ (c.baseChange k).Z),
          IsPullback rA T'.cfg.g T.cfg.g k ∧
          IsPullback rB T'.cg.g T.cg.g k ∧
          IsPullback rU (T'.cf.g ≫ pullback.snd h k) (T.cf.g ≫ h) k ∧
          T'.cfg.i ≫ rA = pullback.fst (f ≫ h) k ≫ T.cfg.i ∧
          T'.cg.i ≫ rB = pullback.fst h k ≫ T.cg.i ∧
          T'.cf.i ≫ rU = pullback.fst (f ≫ h) k ≫ T.cf.i ∧
          T'.q ≫ rA = rU ≫ T.q ∧ T'.p ≫ rB = rA ≫ T.p ∧
          T'.cf.g ≫ pullback.fst h k = rU ≫ T.cf.g ∧
          QuasiCompact T'.cfg.i ∧ QuasiCompact T'.cg.i ∧
          QuasiCompact T'.cf.i ∧ QuasiCompact T'.q ∧
          IsProper v' ∧ T'.cfg.i ≫ v' = (c.baseChange k).i ∧
          v' ≫ (c.baseChange k).g = T'.cfg.g ∧
          v' ≫ pullback.fst c.g k = rA ≫ v) ∧
    (∀ (T : Fin 2 → Compactification.Triangle f h),
      ∃ (R : Compactification.Triangle f h),
      ∀ (j : Fin 2), ∃ (v : R.cfg.Z ⟶ (T j).cfg.Z)
        (u : R.cg.Z ⟶ (T j).cg.Z) (w : R.cf.Z ⟶ (T j).cf.Z),
        IsProper v ∧ IsProper u ∧ IsProper w ∧
        R.cfg.i ≫ v = (T j).cfg.i ∧ R.cg.i ≫ u = (T j).cg.i ∧
        R.cf.i ≫ w = (T j).cf.i ∧ R.q ≫ v = w ≫ (T j).q ∧
        v ≫ (T j).p = R.p ≫ u ∧ w ≫ (T j).cf.g = R.cf.g ∧
        u ≫ (T j).cg.g = R.cg.g) := by
  sorry

end AlgebraicGeometry
