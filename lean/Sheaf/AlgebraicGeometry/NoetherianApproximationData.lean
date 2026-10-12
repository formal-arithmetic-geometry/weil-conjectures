/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent
import Sheaf.AlgebraicGeometry.PerfectComplexDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Noetherian approximation of tensor data

Source: Stacks Project, Tags 01ZR, 05LY, 081G, 09RF and Cohomology Lemma 30.26.7
(blueprint: lem-pc-noetherian-approximation-data).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Noetherian approximation simultaneously for a finitely presented scheme, a bounded
flat complex with proper support, and a perfect derived object.
Source: Stacks Project, Tags 01ZR, 05LY, 081G, 09RF and Cohomology Lemma 30.26.7
(blueprint: lem-pc-noetherian-approximation-data).

Proof:
1. By `thm-pd-spreading-out` (Tag 01ZM), descend the finitely presented morphism
   to a finitely presented `Xi` over a stage, with a cartesian comparison square.
2. By `lem-pc-finite-flat-proper-support-descent` (Tags 01ZR, 05LY, 081G and
   Cohomology Lemma 30.26.7), descend the finitely many terms, differentials and
   relations of `G`, their flatness over the base, and their proper supports.
   Increasing the stage gives a bounded finitely presented base-flat complex and
   an isomorphism of complexes after tensor pullback.
3. By `lem-pc-perfect-complex-descent` (Tag 09RF), increase the stage again to
   descend `E` to a perfect object, with its derived-pullback identification.
4. Filteredness gives a common later stage. Base change preserves finite presentation,
   boundedness, base-flatness, proper support, perfectness and all three identifications.
-/
theorem noetherian_approximation_data
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c)
    (X : Scheme.{u}) (f : X ⟶ Spec c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [∀ (Z : Scheme.{u}), HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {G : CochainComplex X.Modules ℤ}
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n))
    (E : schemeDerivedCategory X) (hE : X.IsPerfect E) :
    ∃ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ Spec (R.obj i)),
      LocallyOfFinitePresentation fi ∧ QuasiCompact fi ∧ QuasiSeparated fi ∧
      ∃ (hfi : LocallyOfFiniteType fi) (g : X ⟶ Xi),
        IsPullback g f fi (Spec.map (c.ι.app i)) ∧
        ∃ (Gi : CochainComplex Xi.Modules ℤ),
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Gi.X n)) ∧
          (∀ n : ℤ, (Gi.X n).IsFinitePresentation) ∧
          (∀ n : ℤ, (Gi.X n).IsFlatOver fi) ∧
          (∀ n : ℤ, @Scheme.Modules.HasSupportProperOver _ _ fi hfi (Gi.X n)) ∧
          ∃ e : ∀ n : ℤ, Scheme.Modules.tensorPullbackObj g (Gi.X n) ≅ G.X n,
            (∀ n m : ℤ, Scheme.Modules.tensorPullbackMap g (Gi.d n m) ≫ (e m).hom =
              (e n).hom ≫ G.d n m) ∧
            ∃ (Ei : schemeDerivedCategory Xi), Xi.IsPerfect Ei ∧
              Nonempty ((derivedPullback g).obj Ei ≅ E) := by
  sorry

end AlgebraicGeometry
