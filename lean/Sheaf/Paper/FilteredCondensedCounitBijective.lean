module

public import Sheaf.Paper.FilteredCondensedRepresentingPairData

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- Finite representing bijections make the global extended-counit map bijective.
Source: blueprint/latest, sec-smooth-purity/sk-thm-sp-qbar, filtered Hom display
and descent of morphisms and relations; parent proof Steps 1 and 4.
(blueprint: lem-pur-filtered-condensed-counit-bijective).

Proof: finite type over a field makes X and Y Noetherian. Apply the recorded
constructible two-colimit on each scheme. Fields containing E are cofinal, since
a compositum with E is again finite. Model C at one such field H. For a morphism
from P(C) to the extended L, the projection comparison identifies its source with
the extension of P_H(C_H). Morphism descent on Y gives a representative at a
larger common field. Its inverse under the supplied finite beta extends to a
preimage by counit_finite_formula, proving surjectivity. For injectivity, descend
two maps on X simultaneously. Equality of their counit images descends on Y after
a further enlargement. The finite formula and finite beta injectivity give equality
of their representatives there and hence equality over the closure. Transport both
arguments along the model isomorphism and its support image. The same argument
covers zero objects and the empty scheme; no arbitrary model enters the map itself. -/
theorem counit_map_bijective {s : ScalarComparisons l k c}
    (hs : s.IsCanonical l k c) {E : PadicAlgCl.FiniteIntermediateField l}
    (d : Pair l k c s E) (hd : d.IsCompatible l k c)
    (C : PadicAlgClConstructible X.left l) :
    Function.Bijective (fun u : C ⟶ d.omegaM l k c ↦
      (omegaSupport l k c).map u ≫ d.omegaCounit l k c) := by sorry

end WeilConjectures.FilteredCondensedRepresentingPair
