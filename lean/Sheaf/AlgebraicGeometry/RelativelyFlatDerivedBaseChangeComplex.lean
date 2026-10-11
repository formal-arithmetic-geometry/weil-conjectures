/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage

/-! # Derived base change for a bounded relatively flat complex

Source: Stacks Project, perfect.tex, Lemma 36.26.4, Tag 0A1D
(blueprint: lem-pc-rf-base-change-complex).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section

namespace AlgebraicGeometry
open MonoidalCategory

/-- The canonical base-change map for a relatively flat bounded-above complex is
invertible. `P` is a K-flat representative of `E` (`e`), so the total tensor complex
`Tot(P ⊗ G)` represents `E ⊗^L G`; `α` is any identification of the two (invertibility
does not depend on it, since it is precomposed after the derived functors). The map
displayed is `Lg^*Rf_*(E ⊗^L G) ⟶ Rf_{T,*}L(g')^*Tot(P ⊗ G) ⟶ Rf_{T,*}(g')^*Tot(P ⊗ G)`:
the recorded derived base-change map followed by the universal derived-to-ordinary
pullback counit `SingleComplexBaseChange.counit` at `Tot(P ⊗ G)`. Its target is the node's
`Rf_{T,*}(L(g')^*E ⊗^L (g')^*G)`: the termwise module pullback tensor isomorphism
(lem-weil-pbc-module-pullback-tensor) identifies `(g')^*Tot(P ⊗ G)` with
`Tot((g')^*P ⊗ (g')^*G)`, and `(g')^*P` is K-flat and represents `L(g')^*E`, so this
complex represents `L(g')^*E ⊗^L (g')^*G`. Under these identifications and the
derived pullback tensor comparison (lem-pc-derived-pullback-tensor-product, Stacks 079U)
the displayed map is the source's canonical map; postcomposing with these isomorphisms
does not change `IsIso`. No boundedness or flatness is imposed on `E`.
Source: Stacks Project, perfect.tex, Lemma 36.26.4, Tag 0A1D, lemma-base-change-tensor.
Proof (the three steps of the node):
1. Apply lem-pc-rf-base-change-single-complex-criterion (Tags 0DJ9 and 0DJA) to the
   qcqs morphism, `E` with quasi-coherent cohomology, and the bounded-above complex `G`.
2. Verify the criterion's stalk condition by
   lem-pc-derived-pullback-tor-independent-flat-complex: the stalk complex of `G` is
   bounded above and flat over the base stalk, so ordinary tensor with the new base
   computes derived tensor; the localization to the fibre-product stalk preserves it.
3. Substitute this condition into the criterion. Its canonical base-change map,
   followed by the derived-to-ordinary pullback counit, is invertible; transporting
   along `α` gives the displayed map.
(blueprint: lem-pc-rf-base-change-complex). -/
theorem relativelyFlat_derivedBaseChange_complex
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ S)
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (G.X i))
    (hqc : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (hflat : ∀ i : ℤ, Scheme.Modules.IsFlatOver (G.X i) f)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (e : DerivedCategory.Q.obj P ≅ E)
    (α : E ⊗ DerivedCategory.Q.obj G ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) :
    IsIso ((derivedPullback g).map ((schemeDerivedDirectImage f).map α.hom) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((SingleComplexBaseChange.counit (pullback.fst f g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))))) := by
  sorry

end AlgebraicGeometry
