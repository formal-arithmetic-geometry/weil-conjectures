import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-! # Perfect direct image with proper support

Source: literature/stacks-project/perfect.tex, Lemma 36.30.1, Tag 0A1H
(blueprint: lem-pc-proper-support-perfect-direct-image).
-/

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The direct image of a perfect complex tensored with a bounded, finitely presented,
base-flat complex with proper support is perfect and satisfies arbitrary base change.
Source: Stacks Project, Lemma 36.30.1, Tag 0A1H.

Proof: arbitrary base change is Tag 0A1D (lem-pc-rf-base-change-complex). Spread the
finite-presentation, flatness, support and perfectness data by Noetherian approximation
(thm-pd-spreading-out and lem-pc-noetherian-approximation-data). Apply the Noetherian
perfect-direct-image theorem (Tag 0DJQ), then descend perfectness and glue it Zariski-locally.
(blueprint: lem-pc-proper-support-perfect-direct-image). -/
theorem properSupport_perfect_directImage
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E)
    (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n)) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      (E ⊗ (DerivedCategory.Q.obj G))) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        Nonempty ((derivedPullback g).obj
            ((schemeDerivedDirectImage f).obj (E ⊗ (DerivedCategory.Q.obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj E ⊗
              (derivedPullback (pullback.fst f g)).obj (DerivedCategory.Q.obj G))) := by
  sorry

end AlgebraicGeometry
