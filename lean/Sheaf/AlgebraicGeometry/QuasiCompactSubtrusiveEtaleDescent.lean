/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.SpaceSubtrusive
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType
import Sheaf.AlgebraicGeometry.FppfSpaceDatumSheafRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SubtrusiveFlatProperRefinement
import Sheaf.AlgebraicGeometry.SubtrusiveTopologicalDescentCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Mathlib.AlgebraicGeometry.Limits

/-! # Quasi-compact subtrusive descent of étale algebraic spaces

Source: Rydh, Submersions and effective descent of étale morphisms,
Theorem (5.17), Remark (5.2), Definition (2.2), and Remark (2.5)(2c)
(blueprint: lem-sfb-space-qc-subtrusive-etale-descent).

Descent data use the existing Yoneda transport form of the overlap isomorphism:
identity transport is the diagonal identity and composition of transports is the
triple cocycle. The pullback square and transport invariance in the conclusion
specify the isomorphism with the original object together with its datum.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-compact universally subtrusive maps are effective for quasi-compact étale
algebraic spaces; universally open point-surjective maps satisfy subtrusiveness.
Source: Rydh, Theorem (5.17), Remark (5.2), and Remark (2.5)(2c)
(blueprint: lem-sfb-space-qc-subtrusive-etale-descent).

Proof, following the ten steps of the node:
1. Identify quasi-compact étale maps with quasi-separated sources over a
   quasi-separated base with the finite-presentation étale category, by
   [lem-kun-etale-lfp], [lem-sfb-space-qcqs-permanence], and
   [lem-sfb-space-flat-proper-fp-locality]. Factor absolute diagonals to pass
   between relative and absolute quasi-separatedness.
2. [lem-sfb-subtrusive-topological-descent-calculus] gives universal submersiveness;
   [lem-sfb-submersive-etale-space-morphism-descent] gives full faithfulness after
   every base change, hence uniqueness of all comparison maps and equalities.
3. For a surjective flat finitely presented scheme map, realize the datum using
   [lem-sfb-space-finite-type-fppf-effectivity] and
   [lem-sfb-fppf-space-datum-sheaf-realization]. Descend étaleness with
   [lem-sfb-representable-fppf-etale-open-descent] and finite presentation with
   [lem-sfb-space-flat-proper-fp-locality]. This is universal effective descent.
4. Refine a finitely presented subtrusive affine map into a flat finitely
   presented surjection followed by a proper finitely presented surjection,
   using [lem-sfb-subtrusive-fp-flat-proper-refinement]. Apply step 3 and
   [lem-sfb-proper-surjection-etale-space-effectivity]; then use composition and
   right-factor descent [lem-sfb-etale-descent-composition-refinement-calculus].
5. For an arbitrary subtrusive affine map use [lem-sfb-space-affine-fp-limit].
   Every finite-presentation stage is subtrusive by the right-factor clause of
   [lem-sfb-subtrusive-topological-descent-calculus].
6. Descend the object, the overlap isomorphism and inverse, and all their
   equations to one common stage by [lem-sfb-fp-space-limit-category] and
   [lem-sfb-space-etaleness-eventual-stage]. Pair and triple limits are supplied
   by [lem-sfb-space-affine-limits-schematic-stages]; the finitely many equations
   include the inverse, diagonal, and cocycle equations.
7. Apply step 4 at that stage and pull its specified effective realization back
   to the original affine source. The pulled-back datum is the original datum.
8. Over an affine chart of the base, the source pullback is qcqs. Choose an
   affine étale atlas by [lem-sfb-qc-space-affine-etale-atlas], use
   [lem-sfb-space-qcqs-permanence] for its quasi-compactness and
   [lem-sfb-subtrusive-topological-descent-calculus] for the subtrusive composite.
   Apply step 7. Descend the resulting isomorphism to the source pullback using
   [lem-sfb-etale-space-single-cover-effective-descent]; its compatibility is
   detected after the étale cover. Base-change permanence uses
   [lem-sfb-space-quasicompact-affine-tests] and
   [lem-trf-space-chartwise-etale-permanence].
9. Choose the affine étale presentation [lem-a1-space-affine-etale-cover].
   Assemble the component realizations using [lem-trf-algebraic-space-coproduct]
   and [lem-weil-pbc-scheme-coproduct-family] within [def-weil-size-convention].
   Step 2 uniquely descends the overlap comparisons and their equations.
   Glue by [lem-sfb-etale-space-single-cover-effective-descent]. Finite
   presentation descends over affine tests by [lem-sfb-space-flat-proper-fp-locality];
   the absolute diagonal factorization gives quasi-separatedness of the result.
   The glued pullback square and transport invariance recover the specified datum.
10. The universally open, point-surjective criterion is
    [lem-sfb-subtrusive-topological-descent-calculus]. No flatness or finite
    presentation hypothesis on the original map is used. -/
theorem quasiCompact_subtrusive_etale_descent {S : Scheme.{u}}
    (H H' : AlgebraicSpace S) (p : H' ⟶ H)
    (_hH : IsAbsolutelyQuasiSeparated H) (_hH' : IsAbsolutelyQuasiSeparated H') :
    (MapIsQuasiCompact p.hom.hom → MapIsUniversallySubtrusive p.hom.hom →
      ∀ (E' : AlgebraicSpace S) (f : E' ⟶ H'),
        MapIsQuasiCompact f.hom.hom → IsChartwiseEtale f →
        IsAbsolutelyQuasiSeparated E' → ∀ D : Over.DescentDatum p (Over.mk f),
          ∃ (E : AlgebraicSpace S) (g : E ⟶ H) (q : E' ⟶ E),
            IsAbsolutelyQuasiSeparated E ∧ MapIsQuasiCompact g.hom.hom ∧
              IsChartwiseEtale g ∧ IsPullback q f g p ∧
              ∀ (T : AlgebraicSpace S) (a b : T ⟶ H') (h : a ≫ p = b ≫ p)
                (x : Over.mk a ⟶ Over.mk f),
                (D.transport a b h x).left ≫ q = x.left ≫ q) ∧
    (MapIsUniversallyOpen p → Function.Surjective (mapPoint p.hom.hom) →
      MapIsUniversallySubtrusive p.hom.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
