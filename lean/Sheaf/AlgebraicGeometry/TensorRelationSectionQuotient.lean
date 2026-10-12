/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Sections of a tensor relation cokernel

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-tensor-relation-section-quotient).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- A section cokernel of the balancing relation is the tensor product over B.
Source: Stacks Project, Schemes, Lemma 01I8 (1); Modules, Section 01CA.
(blueprint: lem-weil-pbc-tensor-relation-section-quotient).

Proof: use the bijective tensor section maps to identify S(W) with C(W) tensor_O P(W)
and the relation source with B(W) tensor_O S(W). The displayed formula identifies
range δ_W with the submodule spanned by c tensor bp minus φ(b)c tensor p: pure tensors
generate both tensor products, and δ and both section maps are additive. The quotient
by this submodule is C(W) tensor_B P(W). Indeed the balancing projection is surjective
and kills the relations, while sending (c,p) to the class of c tensor p in the quotient
is B-balanced and induces its inverse. The assumed surjectivity and kernel formula
for the cokernel projection identify its target with the same quotient. Composing
the quotient identifications gives the additive equivalence with the stated formula.
No affineness or quasi-coherence assumption is needed beyond the section formulas.
-/
theorem tensor_relation_section_quotient (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right))
    (δ : tensorObj B.toModule
      (tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P))
    (W : Y.Opens)
    (hrel : ∀ (b : B.right.obj.obj (op W)) (c : C.right.obj.obj (op W))
        (p : P.val.obj (op W)),
      δ.app W (tmulSection (M := B.toModule) b
        (tmulSection (M := C.toModule)
          (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
        tmulSection (M := C.toModule)
          (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c (b • p) -
        tmulSection (M := C.toModule)
          (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)
            (φ.right.hom.app (op W) b * c) p)
    (hS : Function.Bijective (tensorSectionsMap C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) W))
    (hF : Function.Bijective (tensorSectionsMap B.toModule
      (tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) W))
    (hq : Function.Surjective ((cokernel.π δ).app W))
    (hk : LinearMap.ker ((cokernel.π δ).val.app (op W)).hom =
      LinearMap.range (δ.val.app (op W)).hom) :
    ∃ l : (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P).obj (op W) ≃+
        Γ(cokernel δ, W),
      ∀ (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        l (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p) =
          (cokernel.π δ).app W (tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
