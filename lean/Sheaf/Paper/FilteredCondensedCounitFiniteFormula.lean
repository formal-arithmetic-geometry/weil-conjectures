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

/-- The global extended-counit map agrees with the finite representing maps.
Source: blueprint/latest, sec-smooth-purity/sk-thm-sp-qbar, filtered Hom display;
parent proof Steps 2--3 and the projection composition equation.
(blueprint: lem-pur-filtered-condensed-counit-finite-formula).

Proof: substitute the finite counit formula Pair.IsCompatible into the right side.
Naturality of the closure scalar comparison moves the scalar extension of the test
map to the left. The projection composition equation identifies the two successive
inverse projection comparisons, followed by the tensor transitivity comparison,
with the single inverse comparison at E. The scalar-transitivity isomorphism on Y
is natural in t. These two equalities give the displayed equation by associativity.
The IsCanonical equations transfer the original projection coherence through the
faithful constructible inclusions. For H=E the same composition equation applies;
no identity scalar functor is treated as a definitional identity. -/
theorem counit_finite_formula {s : ScalarComparisons l k c}
    (hs : s.IsCanonical l k c) {E : PadicAlgCl.FiniteIntermediateField l}
    (d : Pair l k c s E) (hd : d.IsCompatible l k c)
    (H : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ H)
    (C : PadicSubfieldConstructible X.left l H)
    (a : C ⟶ (constructibleExtendScalars X.left l h).obj d.M) :
    (omegaSupport l k c).map
        ((constructibleToPadicAlgCl X.left l H).map a ≫
          (constructibleToPadicAlgClCompIso X.left l h).hom.app d.M) ≫
        d.omegaCounit l k c =
      (s.omega H).inv.app C ≫
        (constructibleToPadicAlgCl Y.left l H).map (d.beta H h C a) ≫
          (constructibleToPadicAlgClCompIso Y.left l h).hom.app d.L := by sorry

end WeilConjectures.FilteredCondensedRepresentingPair
