/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence

/-! # Smooth local polarizations of proper flat curve families

Source: Stacks Project, moduli-curves.tex, Tag 0DQ0, and the first proof paragraph of
Tag 0E6F; family conventions in section-stack-curves
(blueprint: lem-sfb-curve-smooth-polarization-cover).

The source remains an algebraic space. A cartesian square of presheaves expresses that
its base change is represented by a scheme. The polarization is an ordinary invertible
module on that scheme, ample on the inverse image of every affine open of the new base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper flat finitely presented algebraic-space family with geometric fibres of
Krull dimension at most one has a smooth surjective scheme base change represented by
a scheme with a relatively ample invertible module. `IsProperCurveFamily` includes
precisely these family hypotheses; its fibre dimension agrees with the supremum over
affine etale charts, with the empty fibre of dimension bottom.

Source: Stacks Project, moduli-curves.tex, Tag 0DQ0 and the first proof paragraph of
Tag 0E6F (blueprint: lem-sfb-curve-smooth-polarization-cover).

Proof:
1. By lem-sfb-space-picard-stack-smooth choose a smooth surjective scheme atlas `V` of
   the relative Picard stack, with smooth composite to `T` and universal line module
   `M` on `X_V`. The geometric-fibre bound includes the empty fibre.
2. Properness is preserved by base change (lem-sfb-space-flat-proper-fp-locality).
   Apply lem-sfb-space-relative-ample-locus to `M` and restrict `V` to its open ample
   locus `U`. The scheme-test characterization supplies a scheme `Y` representing
   `X_U` and its ordinary invertible module `L`, ample over every affine open of `U`.
   The composite `U → V → T` is smooth by lem-pc-open-immersion-smooth-composition.
3. At any geometric point of `T`, the fibre is proper and has dimension at most one.
   By lem-sfb-separated-space-dimension-one-scheme it is a scheme, and by
   lem-sc-proper-dim-one-projective it is projective. Pulling back `O(1)` gives an
   ample invertible module, still ample after field extension by lem-pc-very-ample-ample.
   Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence to regard it as a line
   module in the Picard stack. Empty, nonreduced and disconnected fibres are allowed.
4. Surjectivity of the Picard atlas lifts this line module after a field extension to
   a point of `V`. Pullback compatibility of the module comparison identifies its
   line module with the ample one, so the test characterization of the ample locus
   factors the point through `U`. Every point of `T` has a geometric representative,
   proving surjectivity of `U → T`. For empty `T` this assertion is vacuous. The
   fibre-product universal property gives the displayed cartesian square, as in
   lem-trf-space-fibre-products-etale-covers. -/
theorem exists_smooth_polarization_cover {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Over S) (f : X.obj.obj ⟶ yoneda.obj T) (hf : IsProperCurveFamily X T f) :
    ∃ (U : Over S) (p : U ⟶ T), Smooth p.left ∧ Surjective p.left ∧
      ∃ (Y : Over S) (q : Y ⟶ U) (a : yoneda.obj Y ⟶ X.obj.obj),
        IsPullback a (yoneda.map q) f (yoneda.map p) ∧
          ∃ L : Y.left.Modules, L.IsInvertible ∧
            ∀ W : U.left.Opens, IsAffineOpen W →
              ∃ h : ((Scheme.Modules.tensorPullback (q.left ⁻¹ᵁ W).ι).obj L).IsInvertible,
                @Scheme.Modules.IsAmple (q.left ⁻¹ᵁ W).toScheme
                  ((Scheme.Modules.tensorPullback (q.left ⁻¹ᵁ W).ι).obj L) h := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
