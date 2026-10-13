/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.NoetherianApproximationData
import Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
/-! # Local Noetherian models for proper-support direct images

Source: Stacks Project, Tag 0A1H, lemma-base-change-tensor-perfect, approximation paragraph
(blueprint: lem-pc-proper-support-local-noetherian-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The local tensor data descend to a Noetherian base and recover the direct image.
This asserts neither perfectness nor the Noetherian direct-image theorem.
Source: Stacks Project, Tag 0A1H, lemma-base-change-tensor-perfect, approximation paragraph.
Proof: choose an affine neighbourhood U of x. Restrict X, E and G to its inverse
image. Open pullback preserves perfectness, boundedness, finite presentation,
relative flatness and proper support. Open base change identifies the restriction
of the direct image with the direct image of these restricted tensor data.
Write Gamma(U,O_U) as a filtered colimit of its finitely generated Z-subalgebras,
which are Noetherian. Apply noetherian_approximation_data, using spreading-out
(Tag 01ZM), to descend the finite-presentation morphism and the entire tensor data.
Take Si = Spec(R_i), Xi, fi, Ei and Gi from that theorem. The comparison square is
cartesian; identify it with the chosen pullback. Apply the ordinary relatively flat
base-change comparison to the descended data, and transport along the descended
complex and E identifications. Composing with the open-base-change identification
gives the displayed isomorphism. Si is Noetherian. No direct-image perfectness is
used and no arbitrary witness is chosen to define data elsewhere.
For S empty there are no x; zero E or G gives the same construction and zero image.
(blueprint: lem-pc-proper-support-local-noetherian-model). -/
theorem properSupport_local_noetherian_model
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
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n)) (x : S) :
    ∃ U : S.Opens, x ∈ U ∧
      ∃ (Xi Si : Scheme.{u}) (fi : Xi ⟶ Si),
        IsNoetherian Si ∧ LocallyOfFinitePresentation fi ∧
        QuasiCompact fi ∧ QuasiSeparated fi ∧
        ∃ (hfi : LocallyOfFiniteType fi) (Ei : schemeDerivedCategory Xi),
          Scheme.IsPerfect Xi Ei ∧
          ∃ Gi : CochainComplex Xi.Modules ℤ,
            (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Gi.X n)) ∧
            (∀ n : ℤ, (Gi.X n).IsFinitePresentation) ∧
            (∀ n : ℤ, (Gi.X n).IsFlatOver fi) ∧
            (∀ n : ℤ, @Scheme.Modules.HasSupportProperOver _ _ fi hfi (Gi.X n)) ∧
            ∃ g : U.toScheme ⟶ Si,
              Nonempty ((derivedPullback U.ι).obj
                  ((schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)) ≅
                (derivedPullback g).obj
                  ((schemeDerivedDirectImage fi).obj (Ei ⊗ DerivedCategory.Q.obj Gi))) := by sorry

end AlgebraicGeometry
