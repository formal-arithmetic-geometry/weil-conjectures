/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
/-! # Object comparison for relatively flat tensor base change

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor
(blueprint: lem-pc-relatively-flat-tensor-base-change-iso).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Object-level form of the canonical relatively flat tensor base-change comparison.
The second tensor factor on the new scheme is ordinary termwise pullback.
Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor.
Proof: choose a K-flat representative P of E. The derived monoidal construction
identifies E tensor Q(G) with Q(Tot(P tensor G)). Apply
relativelyFlat_derivedBaseChange_complex to this identification, E's quasi-coherent
cohomology, and the bounded-above, quasi-coherent, relatively flat terms of G.
Its invertible map gives an isomorphism to the direct image of ordinary pullback
of the total tensor complex. Termwise tensor-pullback compatibility identifies this
complex with Tot(g'*P tensor g'*G). Pullback of P is K-flat, so this total complex
represents Lg'*E tensor Q(g'*G). Compose the comparison with this identification
under the direct-image functor. This requires no properness or finite presentation.
Zero complexes and empty schemes are included; bounded-above G need not be K-flat
over O_X and is not replaced by its derived pullback.
(blueprint: lem-pc-relatively-flat-tensor-base-change-iso). -/
theorem relativelyFlat_tensor_baseChange_iso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ S) (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty X E) (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (G.X n))
    (hGqc : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f) :
    Nonempty ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)) ≅
      (schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj E ⊗
          DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
              (.up ℤ)).obj G))) := by sorry

end AlgebraicGeometry
