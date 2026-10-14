/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded

/-! # Homotopy representatives of the resolved cover comparison -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The resolved cover comparison before cylinder rectification.
Source: Stacks Project, Tags 08BV, 08HZ, 08FE, 08HY and 0DJ9.
(blueprint: lem-pc-standard-single-union-homotopy-chain-data).

Proof: Put W = U union V and pull its cover back to W_A. Resolve N[0] and
its ordinary pullback by functorial injective-term K-injective complexes. The
restriction-pair and restriction-difference rows are exact: sheaf gluing gives
the kernel, and injectivity gives the surjection onto the overlap. Apply the
relative direct-image computation to these rows. Resolve the source diagram
K-flatly before applying derived pullback, keeping the restriction maps and
the homotopies of the finite diagram. The derived-to-ordinary pullback counit,
transposed under the pullback/direct-image adjunction, induces the comparison
of the two resolved diagrams. Naturality of the restriction units and the
underived open counit square supply a specified homotopy H of its first square.
The induced cone map is mapOfHomotopy H: the homotopy term must be retained,
rather than choosing an arbitrary third map between distinguished triangles.
Identify the six objects using the short exact rows, direct-image composition,
exact open restriction and the additive biproduct comparison. Expand the
single-module comparison as the base-change mate followed by the single
pullback counit. Pasting counits and the adjunction triangle identities gives
the three displayed equations, including the equation for mapOfHomotopy H.
No cylinder rectification is done here. Empty opens and zero coefficients
produce zero rows; repeated or contained opens produce split rows. These
constructions therefore require neither flatness nor quasi-coherence. -/
theorem standardSingle_union_homotopy_chain_data
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (C D C' D' : CochainComplex
        (SheafOfModules.{u} (moduleRings A.toRingedSpace)) ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ aU.left ⊞ aV.left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ aUV.left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ aU.right ⊞ aV.right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ aUV.right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom = e₂.hom ≫ biprod.map aU.hom aV.hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ aUV.hom := by sorry


end AlgebraicGeometry
