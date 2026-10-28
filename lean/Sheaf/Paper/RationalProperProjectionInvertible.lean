/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The proper projection mate over one finite coefficient field

Source: thm-sf-pf-field; BS 6.8.14--6.8.15.
(blueprint: lem-sf-rational-proper-projection-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The normalized counit projection at a finite rational coefficient stage.
Source: def-exchange-projection, with the identity open factor.
(blueprint: lem-sf-rational-proper-projection-invertible). -/
def rationalProperProjection (f : X ⟶ Y)
    (G : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y)
    (a : rationalDerivedPullback l E f ⊣ G)
    (K : sfRationalConstructibleCategory l E X)
    (L : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedTensor l E Y).obj (G.obj K, L) ⟶
      G.obj ((rationalDerivedTensor l E X).obj
        (K, (rationalDerivedPullback l E f).obj L)) :=
  a.homEquiv _ _ ((canonicalRationalPullbackTensor l E f (G.obj K) L).hom ≫
    (rationalDerivedTensor l E X).map (Prod.mkHom (a.counit.app K) (𝟙 _)))

/-- The proper counit projection is invertible at a finite rational coefficient field.
Source: thm-sf-pf-field.proof.md, rational stage and compatibility;
BS Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-rational-proper-projection-invertible).

Proof: every object of the raw rational constructible category is the image of
its integral object. The integral residue-field Tor criterion supplies a uniform
Tor interval for each constructible derived-complete representative. Apply the
integral projection formula and rationalize its map and inverse. Use the
compactification (identity,f). The identity extension and its tensor comparison
cancel by the adjunction unit identity. The integral/rational pullback and tensor
normalizations identify the resulting transpose with the canonical rational
pullback tensor comparison followed by the counit. The localized integral
pullback/direct-image adjunction supplies one right adjoint. For any supplied a,
the unique right-adjoint comparison intertwines the counits; transposing this
equation identifies rationalProperProjection with the preceding isomorphism
conjugated by that comparison and its tensor. Hence it too is invertible.
This is a statement at one finite coefficient field, with no common-stage descent
or continuous-coefficient realization. Zero complexes and empty schemes use the
same localization and identity-open calculation. -/
theorem rationalProperProjection_isIso
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (G : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y)
    (a : rationalDerivedPullback l E f ⊣ G)
    (K : sfRationalConstructibleCategory l E X)
    (L : sfRationalConstructibleCategory l E Y) :
    IsIso (rationalProperProjection l E f G a K L) := by sorry

end WeilConjectures
