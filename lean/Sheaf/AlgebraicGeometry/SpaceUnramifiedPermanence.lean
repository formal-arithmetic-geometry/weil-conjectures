/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen

/-! # Permanence of unramified morphisms of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 03ZI, 03ZJ, 06G6 and 06CR
(blueprint: lem-sfb-space-unramified-permanence).

Unramifiedness and etaleness are the existing universal compatible-etale-chart test
`MapIsLocally`, specialized to the recorded scheme properties. Base change uses the
existing bundled sheaf fibre product and its actual projection.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Unramified space maps compose, cancel on the left without any condition on the
second map, and remain unramified after every base change. Etale space maps are unramified.
Source: Stacks Project, Morphisms of Spaces, Tags 03ZI, 03ZJ, 06G6 and 06CR
(blueprint: lem-sfb-space-unramified-permanence).

Proof, following the six steps of the node:
1. Choose a surjective etale scheme atlas W of Z. Apply
   [lem-sfb-unramified-etale-compatible-charts] with this prescribed target atlas to g,
   then with the resulting atlas V of Y to f. This gives compatible surjective etale
   charts U -> V -> W of X -> Y -> Z [def-trf-algebraic-space].
2. If f and g are unramified, chart recognition makes U -> V and V -> W unramified.
   Their composite is unramified by [lem-sfb-scheme-unramified-composition-cancellation].
   Recognize this composite chart to conclude that f followed by g is unramified.
3. If the composite is unramified, its chart U -> W is unramified. Scheme left
   cancellation in [lem-sfb-scheme-unramified-composition-cancellation] makes U -> V
   unramified without any condition on V -> W. Chart recognition gives the claim for f.
4. For t : Y' -> Y choose a surjective etale scheme atlas Q of Y'. Form V' = V x_Y Q
   and U' = U x_V V'. These are schemes by representability and scheme fibre products.
   The induced source and target charts of X x_Y Y' -> Y' are surjective etale:
   they are composites of pullbacks of the original atlases. Use
   [lem-trf-space-fibre-products-etale-covers],
   [lem-weil-pbc-etale-composition-cancellation], and
   [lem-trf-surjective-morphism-composition]. The identification
   U x_V (V x_Y Q) = U x_Y Q inserts or forgets the forced V component on sections.
5. The new chart U' -> V' is the scheme base change of U -> V, so it is unramified
   by [lem-weil-pbc-unramified-base-change-open], clause (1). Chart recognition gives
   unramifiedness of the actual sheaf-pullback projection, for arbitrary t.
6. If f is chartwise etale, its compatible scheme chart is etale, hence unramified
   by [def-weil-etale-morphism] and [def-weil-unramified-morphism]. Apply chart
   recognition again. All constructions and tests allow empty schemes and spaces. -/
theorem space_unramified_permanence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (MapIsLocally (@AlgebraicGeometry.IsUnramified) f →
      MapIsLocally (@AlgebraicGeometry.IsUnramified) g →
      MapIsLocally (@AlgebraicGeometry.IsUnramified) (f ≫ g)) ∧
    (MapIsLocally (@AlgebraicGeometry.IsUnramified) (f ≫ g) →
      MapIsLocally (@AlgebraicGeometry.IsUnramified) f) ∧
    (MapIsLocally (@AlgebraicGeometry.IsUnramified) f →
      ∀ (Y' : AlgebraicSpace S) (t : Y' ⟶ Y),
        MapIsLocally (@AlgebraicGeometry.IsUnramified) (enlargedFibreProductFst t f)) ∧
    (MapIsLocally (@AlgebraicGeometry.Etale) f →
      MapIsLocally (@AlgebraicGeometry.IsUnramified) f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
