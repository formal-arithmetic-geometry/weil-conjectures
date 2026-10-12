/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Extensionality on tensors of wedges of locally lifted sections

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-exterior-tensor-lift-hom-ext).
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Morphisms out of a tensor of exterior powers are determined on wedges in the first
factor and on wedges of images of sections under an epimorphism in the second factor.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph: pure wedges
and their tensors generate locally (blueprint: lem-sc-exterior-tensor-lift-hom-ext).

Proof: An epimorphism of sheaves of modules is locally surjective. Given a finite
family of sections of `C`, lift each section under `g` on a covering and take a common
refinement of the finitely many coverings. The displayed hypothesis and naturality
then imply equality on the tensor of any two pure wedges, by separatedness of `D`.
The case `s = 0` requires no lifts. Pure wedges span sectionwise exterior powers.
The sheafification maps are locally surjective, so sections of `exteriorSheaf A r`
and `exteriorSheaf C s` are locally finite linear combinations of pure wedges.
The tensor sheafification map is also locally surjective, so every section of their
tensor product is locally a finite sum of elementary tensors. Bilinearity and
linearity extend the equality to these sums, and separatedness glues it. Finally
extensionality of sheaf morphisms gives `φ = ψ`. This uses neither finite local
freeness, nor a rank relation, nor injectivity of any map. -/
theorem exteriorTensor_lift_hom_ext {X : Scheme.{v}} {A B C D : X.Modules}
    (g : B ⟶ C) [Epi g] (r s : ℕ)
    (φ ψ : exteriorSheaf A r ⊗ exteriorSheaf C s ⟶ D)
    (h : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → B.val.obj (op U)),
      φ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i)))) =
        ψ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i))))) :
    φ = ψ := by sorry

end AlgebraicGeometry.Scheme.Modules
