/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteComposition.CondensedFiniteCompositionCoordinates

/-! # The finite forward projection square

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

/-- The forward projection square before cancellation of the compact-support compositors.
The tensor input is bounded constructible, although K need not have finite Tor amplitude.
Source: latest blueprint fix-prop-projection-formula coherence sentence, and
prop-sf-pf-coherence proof, tensor-composition paragraph
(blueprint: lem-sf-finite-native-forward-projection).

Proof:
1. Use the finite discrete section-action encoding and bounded constructible etale origins
of K and L. Finite Noetherian coefficient comparison preserves L's Tor interval. Pullback
preserves that interval. A bounded flat model of the pullback tensored with a bounded
representative of K proves the first assertion. The intermediate proper/open images and
tensor inputs lie in D+; this requires no Tor bound on K.
2. The counit-normalized comparison for the proper factor commutes with its projection
map by ringed exchange/tensor coherence. The canonical open comparison commutes with the
open tensor map. Compose the squares, using naturality at the open tensor component.
Under the internal section-action equivalence this identifies exactly pf, rather than
merely an unspecified projection isomorphism.
3. Apply the ordinary etale shriek/tensor composition equation. Conjugate by the signed
tensor symmetries to put K first. Pullback comparison respects the symmetries and the
canonical pullback compositor.
4. In a compatible compactification triangle, substitute the counit-normalized site
comparison squares and the binary tower normalization. Cancel the internal site
isomorphisms. The remaining last pullback comparison is the inverse of the displayed
leftDerivedUpperStarComp, so the result has the stated tensor input.
5. Pass to arbitrary supplied compactifications using common proper refinements. The
native change_projection square, and the normalization and independence of the binary
compositor, conjugate the same equation. Cancel endpoint comparisons. Neither this
argument nor its displayed equation inverts a projection component. Identity morphisms,
empty schemes, n=1, and nonperfect bounded constructible K use the same argument. -/
theorem finite_forward_projection
    (B : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ B.p) (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (_hn : 1 ≤ n) :
    ∀ {X Y Z : SepFinType B.k} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
      (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cfg : Compactification (f.hom.left ≫ g.hom.left))
      (K : D (coefficient ell E n) X.obj.left)
      (_hK : boundedConstructible (condensedRingObj (coefficient ell E n) X.obj.left) K)
      (L : CondensedConstructibleFiniteTor (coefficient ell E n) Z.obj.left),
      boundedConstructible (condensedRingObj (coefficient ell E n) X.obj.left)
          (K ⊗ (P (coefficient ell E n) (f.hom.left ≫ g.hom.left)).obj L.obj) ∧
      pf (coefficient ell E n) cg ((F (coefficient ell E n) cf).obj K) L.obj ≫
          (F (coefficient ell E n) cg).map
            (pf (coefficient ell E n) cf K ((P (coefficient ell E n) g.hom.left).obj L.obj)) ≫
          (F (coefficient ell E n) cg).map ((F (coefficient ell E n) cf).map
            (K ◁ (leftDerivedUpperStarComp (coefficient ell E n)
              f.hom.left g.hom.left).inv.app L.obj)) ≫
          NativeFiniteComposition.forward (coefficient ell E n) cf cg cfg
            (K ⊗ (P (coefficient ell E n) (f.hom.left ≫ g.hom.left)).obj L.obj) =
        (NativeFiniteComposition.forward (coefficient ell E n) cf cg cfg K ▷ L.obj) ≫
          pf (coefficient ell E n) cfg K L.obj := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteProjectionComposition
