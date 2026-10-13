/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso

/-! # Transport of tensor base change to a specified cartesian square

Source: Stacks Project, Tag 0A1D, displayed cartesian-square comparison.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Tensor base change in a specified cartesian square, with identified tensor factors.
Source: Stacks Project, Tag 0A1D, displayed cartesian square and its isomorphism.
Proof: the cartesian square identifies X' with the canonical pullback of f and p.
Apply relativelyFlat_tensor_baseChange_iso to f, p, E and G. Transport its right side
along this scheme isomorphism, using composition of derived pullbacks and of derived
direct images and the identity comparisons; pushforward along a scheme isomorphism
is inverse to pullback. The given degreewise isomorphisms e commute with differentials,
so define an isomorphism of complexes from the ordinary tensor pullback of G to G'.
Apply DerivedCategory.Q to this complex isomorphism. Tensor it with the given derived
identification of E, and apply the direct-image functor. Composing gives the displayed
isomorphism. Only ordinary pullback is used on G; relative flatness, rather than
O_X-flatness, is exactly the assumption of Tag 0A1D. There are no support, finite
presentation, perfectness or Noetherian assumptions. Empty schemes and zero complexes
are included by the same categorical construction.
(blueprint: lem-pc-cartesian-tensor-data-comparison). -/
theorem cartesian_tensor_data_comparison
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S X' T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (p : T ⟶ S) (g : X' ⟶ X) (f' : X' ⟶ T) (sq : IsPullback g f' f p)
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (G.X n))
    (hGqc : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (E' : schemeDerivedCategory X')
    (hEE' : Nonempty ((derivedPullback g).obj E ≅ E'))
    (G' : CochainComplex X'.Modules ℤ)
    (e : ∀ n : ℤ, Scheme.Modules.tensorPullbackObj g (G.X n) ≅ G'.X n)
    (he : ∀ n m : ℤ, Scheme.Modules.tensorPullbackMap g (G.d n m) ≫ (e m).hom =
      (e n).hom ≫ G'.d n m) :
    Nonempty ((derivedPullback p).obj
        ((schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)) ≅
      (schemeDerivedDirectImage f').obj (E' ⊗ DerivedCategory.Q.obj G')) := by sorry

end AlgebraicGeometry
