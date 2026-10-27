module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Sheaf.AlgebraicGeometry.FibrewiseFlatnessCriterion

/-! # Fibrewise flatness after arbitrary parameter base change

Source: Stacks Project, More on Morphisms, Tags 05VJ and 039C, structure-sheaf case;
Morphisms, Tags 01U9, 01TS and 01T4.
(blueprint: lem-sfb-relative-flat-fibre-test)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flatness of a map from a flat, locally finitely presented family to a locally finite
type family is equivalent to flatness on the scheme-theoretic fibre. The hypotheses
and the test persist after every parameter base change.

Source: Stacks Project, More on Morphisms, Tag 05VJ,
`lemma-base-change-criterion-flatness-fibre`, and Tag 039C,
`theorem-criterion-flatness-fibre`, specialized to the structure sheaf.
(blueprint: lem-sfb-relative-flat-fibre-test)

Proof:
1. The square of fibre inclusions and the induced fibre map is cartesian by the
   universal property of the fibre product (def-pc-fibre-product, def-pc-scheme-fibre).
   The fibre homeomorphism identifies x with p.asFiber x; commutativity identifies
   its image with the fibre point over f(x).
2. If f is flat at x, lem-sfb-pointwise-flatness-base-change (1), applied to the
   fibre inclusion of Y, gives flatness of the fibre map at p.asFiber x.
3. Conversely p is flat at x by def-weil-flat-morphism. The hypotheses of
   lem-sfb-fibrewise-flatness-criterion hold, so fibre flatness implies flatness
   of f at x (and flatness of q at f(x), which is not needed here).
4. For arbitrary h : T → S, lem-weil-pbc-flat-morphism-base-change gives flatness
   of pullback.snd p h; clause (3) of lem-weil-pbc-qcqs-morphism-permanence gives
   its local finite presentation; lem-weil-pbc-lft-base-change gives local finite
   type of pullback.snd q h. None imposes any condition on h or T.
5. The induced pullback map commutes with the projections to T. Repeat steps 1–3
   over T, at each x' in pullback p h, using the properties in step 4. Its unique
   fibre point is (pullback.snd p h).asFiber x'. This gives the last equivalence.
-/
theorem Scheme.Hom.relative_flat_fibre_test {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ q = p)
    [Flat p] [LocallyOfFinitePresentation p] [LocallyOfFiniteType q] :
    (∀ x : X, (f.stalkMap x).hom.Flat ↔
      ((pullback.map p (S.fromSpecResidueField (p x))
        q (S.fromSpecResidueField (p x)) f (𝟙 _) (𝟙 S)
        (by simpa only [Category.comp_id] using hf.symm) (by simp)).stalkMap
          (p.asFiber x)).hom.Flat) ∧
    (∀ (T : Scheme.{u}) (h : T ⟶ S),
      Flat (pullback.snd p h) ∧ LocallyOfFinitePresentation (pullback.snd p h) ∧
      LocallyOfFiniteType (pullback.snd q h) ∧
      ∀ x' : ↥(pullback p h),
        ((pullback.map p h q h f (𝟙 T) (𝟙 S)
          (by simpa only [Category.comp_id] using hf.symm) (by simp)).stalkMap x').hom.Flat ↔
        ((pullback.map (pullback.snd p h)
          (T.fromSpecResidueField ((pullback.snd p h) x')) (pullback.snd q h)
          (T.fromSpecResidueField ((pullback.snd p h) x'))
          (pullback.map p h q h f (𝟙 T) (𝟙 S)
            (by simpa only [Category.comp_id] using hf.symm) (by simp))
          (𝟙 _) (𝟙 T) (by simp) (by simp)).stalkMap
            ((pullback.snd p h).asFiber x')).hom.Flat) := by
  sorry

end AlgebraicGeometry
