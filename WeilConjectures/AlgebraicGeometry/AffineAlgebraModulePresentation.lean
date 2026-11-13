/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleGenerators
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleKernel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Algebra-module presentations on an affine open

Source: Stacks Project, Morphisms, Lemma 0H88, proof, second paragraph;
EGA I, Proposition 9.6.1.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A module over a quasi-coherent algebra has a global algebra-module presentation on
an affine open whenever its underlying structure-sheaf module is quasi-coherent there.
The conclusion is a presentation on the slice site, rather than quasi-coherence on S.

Source: Stacks Project, Morphisms, Lemma 0H88, proof, second paragraph;
EGA I, Proposition 9.6.1. -/
theorem nonempty_algebraModule_presentation_over (S : Scheme.{u})
    (A : S.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).obj
        A.right)) (U : S.Opens) (hU : IsAffineOpen U)
    (hG : (((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
        A.hom)).obj G).over U).IsQuasicoherent) :
    Nonempty (G.over U).Presentation := by
  obtain ⟨generators⟩ :=
    nonempty_affine_algebraModule_generatingSections S A U hU (G.over U) hG
  have hK := affine_algebraModule_kernel_isQuasicoherent
    S A U (G.over U) hA hG generators.I generators.π
  obtain ⟨relations⟩ := nonempty_affine_algebraModule_generatingSections
    S A U hU (Limits.kernel generators.π) hK
  exact ⟨⟨generators, relations⟩⟩

end AlgebraicGeometry.Scheme.Modules
