/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteScalarMateData

/-! # Normalized finite scalar evaluations

Source: current blueprint coefficient-extension exceptional-image proof,
sec-six-functors-basics/sk-prop-scalar-six; Stacks 0941, 079P and 07A6
(blueprint: lem-coef-finite-scalar-normalized-evaluations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteScalarMate

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

variable {l E L i D hl f c}

/-- Finite scalar evaluations with their quotient squares and canonical support arrow.
These data contain no integral limit comparisons or integral transpose.
Source: the finite scalar-extension paragraph of lem-coef-rational-operations,
extracted finite-evaluation part of lem-coef-finite-scalar-mate-realization
(blueprint: lem-coef-finite-scalar-normalized-evaluations). -/
structure FiniteCompatibility (a : Context l E L i D hl f c) (h : IsIso a.alpha)
    (e : ℕ) (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e) where
  finiteX : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E X n).FullSubcategory),
    FiniteExceptional.domain l L X (retainedIndex e n)
      ((finiteTensor l E L i e he hp X n).obj K.obj)
  finiteY : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E Y n).FullSubcategory),
    FiniteExceptional.domain l L Y (retainedIndex e n)
      ((finiteTensor l E L i e he hp Y n).obj K.obj)
  evalX : ∀ n : ℕ,
    a.TX ⋙ FiniteAdjunctionDiagram.evaluation l L X (retainedIndex e n) ≅
      FiniteAdjunctionDiagram.evaluation l E X n ⋙
        finiteTensorRestricted l E L i e he hp X n (finiteX n)
  evalY : ∀ n : ℕ,
    a.TY ⋙ FiniteAdjunctionDiagram.evaluation l L Y (retainedIndex e n) ≅
      FiniteAdjunctionDiagram.evaluation l E Y n ⋙
        finiteTensorRestricted l E L i e he hp Y n (finiteY n)
  transitionX : ∀ (m n : ℕ) (hnm : n ≤ m)
      (N : (FiniteAdjunctionDiagram.domain l E X).FullSubcategory),
    (FiniteExceptional.reduction l L X (retainedIndex_mono e hnm)).map
        (((evalX m).hom.app N).hom) ≫
      (quotientTensorSquare l E L i e he hp X hnm).hom.app
        ((FiniteAdjunctionDiagram.evaluation l E X m).obj N).obj ≫
      (finiteTensor l E L i e he hp X n).map
        (FiniteAdjunctionDiagram.transition l E X a.r.quotientRestrictionX hnm N).hom =
    (FiniteAdjunctionDiagram.transition l L X a.s.quotientRestrictionX
      (retainedIndex_mono e hnm) (a.TX.obj N)).hom ≫ ((evalX n).hom.app N).hom
  transitionY : ∀ (m n : ℕ) (hnm : n ≤ m)
      (N : (FiniteAdjunctionDiagram.domain l E Y).FullSubcategory),
    (FiniteExceptional.reduction l L Y (retainedIndex_mono e hnm)).map
        (((evalY m).hom.app N).hom) ≫
      (quotientTensorSquare l E L i e he hp Y hnm).hom.app
        ((FiniteAdjunctionDiagram.evaluation l E Y m).obj N).obj ≫
      (finiteTensor l E L i e he hp Y n).map
        (FiniteAdjunctionDiagram.transition l E Y a.r.quotientRestrictionY hnm N).hom =
    (FiniteAdjunctionDiagram.transition l L Y a.s.quotientRestrictionY
      (retainedIndex_mono e hnm) (a.TY.obj N)).hom ≫ ((evalY n).hom.app N).hom
  alphaFinite : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E X n).FullSubcategory),
    IsIso (finiteAlpha l E L i D hl f c e he hp n K)
  finiteSupport : ∀ (n : ℕ) (K : (FiniteAdjunctionDiagram.domain l E X).FullSubcategory),
    ((FiniteAdjunctionDiagram.evaluation l L Y (retainedIndex e n)).map
        (a.alpha.app K) ≫ (a.s.supportEvaluation (retainedIndex e n)).hom.app (a.TX.obj K) ≫
      (FiniteExceptional.F l L D hl f c (retainedIndex e n)).map ((evalX n).hom.app K)).hom =
    ((evalY n).hom.app (a.r.F.obj K) ≫
      (finiteTensorRestricted l E L i e he hp Y n (finiteY n)).map
        ((a.r.supportEvaluation n).hom.app K)).hom ≫
      finiteAlpha l E L i D hl f c e he hp n
        ((FiniteAdjunctionDiagram.evaluation l E X n).obj K)
  finite_transpose : ∀ (n : ℕ) (N : (FiniteAdjunctionDiagram.domain l E Y).FullSubcategory),
    ((FiniteAdjunctionDiagram.evaluation l L X (retainedIndex e n)).map
        ((a.beta h).app N) ≫
      (a.s.exceptionalEvaluation (retainedIndex e n)).hom.app (a.TY.obj N) ≫
      (FiniteExceptional.G l L D hl f c (retainedIndex e n)).map
        ((evalY n).hom.app N)).hom =
    ((evalX n).hom.app (a.r.G.obj N)).hom ≫
    (((FiniteExceptional.adjunction l L D hl f c (retainedIndex e n)).homEquiv _ _)
      (ObjectProperty.homMk (Y :=
          (finiteTensorRestricted l E L i e he hp Y n (finiteY n)).obj
            ((FiniteAdjunctionDiagram.evaluation l E Y n).obj N))
        (((FiniteExceptional.F l L D hl f c (retainedIndex e n)).map
          ((finiteTensorRestricted l E L i e he hp X n (finiteX n)).map
            ((a.r.exceptionalEvaluation n).hom.app N))).hom ≫
        (@asIso _ _ _ _
          (finiteAlpha l E L i D hl f c e he hp n
            ((FiniteAdjunctionDiagram.evaluation l E Y n ⋙
              FiniteExceptional.G l E D hl f c n).obj N))
          (alphaFinite n _)).inv ≫
          (finiteTensor l E L i e he hp Y n).map
            ((FiniteExceptional.adjunction l E D hl f c n).counit.app
              ((FiniteAdjunctionDiagram.evaluation l E Y n).obj N)).hom))).hom

variable (l E L i D hl f c)

/-- Choose the scalar evaluations that identify the actual proper/open comparison.
Source: current blueprint finite scalar-extension paragraph of
lem-coef-rational-operations; Stacks 0941, 079P and 07A6
(blueprint: lem-coef-finite-scalar-normalized-evaluations).

Proof: on a simultaneous K-flat strict-system resolution, identify evaluation at
upper exponent e(n+1) of scalar extension with tensor from A_(n+1) to B_(n+1).
Use the tensor reassociation map, normalized by its scalar-adjunction unit, for
both X and Y. Finite freeness preserves constructibility and each input Tor
interval, so these maps restrict to the displayed full subcategories. They are
invertible because the input systems are normalized. Reassociation with each
actual quotient transition gives transitionX and transitionY; the ring square
is quotientSquare, including m=n. Evaluate the actual proper projection followed
by open balancing that defines Context.alpha. The canonical supportEvaluation
of each system realization is assembled from those same proper/open adjunctions.
Naturality and the scalar-adjunction triangle identities cancel the intervening
model isomorphisms. The remaining arrow is exactly finiteAlpha, with its two
finiteImageIso factors, giving finiteSupport. This is an equality of localized
strict-system maps and does not infer equality from finite evaluations. The same
formulas cover e=1, identity scalar extension, zero objects and empty schemes.
For alphaFinite, use finiteComparison_isIso and the two finiteImageIso factors.
Finally evaluate the system mate through the normalized finite adjunctions.
Substitute finiteSupport into evaluation_mate for the inverse scalar comparison.
The component mate is the displayed finite Hom transpose: move the exceptional
evaluation through the finite comparison by naturality, and use the finite
adjunction counit. This is the finite_transpose equation, with the same chosen
scalar evaluations and without reconstructing any system map from its levels. -/
theorem finiteScalarNormalizedEvaluations (a : Context l E L i D hl f c) (h : IsIso a.alpha)
    (e : ℕ) (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e) :
    Nonempty (FiniteCompatibility a h e he hp) := by sorry

end WeilConjectures.FiniteScalarMate
