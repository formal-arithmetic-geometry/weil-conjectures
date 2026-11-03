/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteComposition.CondensedFiniteCompositionCoordinates

/-! # Geometry of the finite native compositor

Source: latest blueprint sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, composition and coherence sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteProjectionComposition

open CompactificationReindexing

/-- The specified native forward maps form invertible, associative compact-support
comparisons on bounded constructible finite coefficients, and their functors preserve
that domain. No tensor projection morphism occurs in this assertion.
Source: latest blueprint sk-thm-sf-comp-composition, construction, canonicity and
associativity paragraphs; finite etale realization in thm-sf-pf-proetale
(blueprint: lem-sf-finite-native-compositor-geometry).

Proof:
1. Encode modules over the discrete condensed quotient as ordinary modules over the
constant ring sheaf, then choose bounded constructible etale origins. Open extension
is exact and preserves constructibility; the finite-coefficient proper direct-image
theorem proves bounded constructibility after the proper factor. Transport back through
the normalized section-action equivalence to prove the first clause.
2. Identify towerRestriction with the counit-normalized open restriction map. The open
unit is invertible, so its displayed total inverse is the categorical inverse. The
adjunction Hom bijection identifies towerInterchange with the normalized proper/open
interchange. Uniqueness of adjoints identifies jComp, and the normalized direct-image
compositor identifies the last proper comparison, including equality transport.
3. The finite site comparison identifies this tower word with the canonical etale
compact-support compositor on D+. The common-refinement counit normalization identifies
each native refinement component with the corresponding finite etale refinement. These
are invertible on bounded constructible origins. Thus change is exactly the usual
common-refinement comparison and forward is the canonical etale compositor expressed
in the supplied compactifications; all three factors are invertible.
4. On a three-map staircase, canonical etale associativity gives the two equal tower
words. The binary site normalization and common-refinement cocycle transport the equality
to the four specified native forward maps. Naturality cancels all internal comparison
pairs. The last equality transport is precisely the copied compactification in the
statement. The first clause ensures that the intermediate F_cf K is still in the same
domain. No finite Tor hypothesis on K, density of the chosen opens, or nonemptiness of a
scheme is used. Identity factors obey the same adjunction triangle identities. -/
theorem finite_compositor_geometry
    (B : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ B.p) (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (_hn : 1 ≤ n) :
    (∀ {X Y : SepFinType B.k} (f : X ⟶ Y)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      (cf : Compactification f.hom.left) (K : D (coefficient ell E n) X.obj.left),
      boundedConstructible (condensedRingObj (coefficient ell E n) X.obj.left) K →
        boundedConstructible (condensedRingObj (coefficient ell E n) Y.obj.left)
          ((F (coefficient ell E n) cf).obj K)) ∧
    (∀ {X Y Z : SepFinType B.k} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
      (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cfg : Compactification (f.hom.left ≫ g.hom.left))
      (K : D (coefficient ell E n) X.obj.left)
      (_hK : boundedConstructible (condensedRingObj (coefficient ell E n) X.obj.left) K),
      IsIso (NativeFiniteComposition.forward (coefficient ell E n) cf cg cfg K)) ∧
    (∀ {X Y Z W : SepFinType B.k} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
      [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
      (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (ch : Compactification h.hom.left)
      (cfg : Compactification (f.hom.left ≫ g.hom.left))
      (cgh : Compactification (g.hom.left ≫ h.hom.left))
      (cfgh : Compactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
      (K : D (coefficient ell E n) X.obj.left)
      (_hK : boundedConstructible (condensedRingObj (coefficient ell E n) X.obj.left) K),
      (F (coefficient ell E n) ch).map
          (NativeFiniteComposition.forward (coefficient ell E n) cf cg cfg K) ≫
          NativeFiniteComposition.forward (coefficient ell E n) cfg ch cfgh K =
        NativeFiniteComposition.forward (coefficient ell E n) cg ch cgh
            ((F (coefficient ell E n) cf).obj K) ≫
          NativeFiniteComposition.forward (coefficient ell E n) cf cgh
            (cfgh.copy (Category.assoc f.hom.left g.hom.left h.hom.left).symm) K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteProjectionComposition
