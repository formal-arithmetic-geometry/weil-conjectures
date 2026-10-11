/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finiteness detected by formal glueing

Source: Stacks Project, More on Algebra, Remark 05EU, case finite, with the hypotheses
of Lemma 05EK (blueprint: lem-weil-pbc-formal-glueing-finite-modules).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- A module is finite exactly when its formal glueing components are finite.
Source: Stacks Project, Remark 05EU, case finite, and Lemma 05EK
(blueprint: lem-weil-pbc-formal-glueing-finite-modules).

Proof, following the node's seven steps:
1. Images of a finite generating family generate both the scalar extension and each
localization (def-weil-finitely-generated-module, def-weil-module-base-change,
def-weil-pbc-module-localization-away).
2. Put T = S × ∏ i, R_{f i}. The diagonal map R → T is flat: S is flat by hypothesis,
localizations are flat (lem-weil-pbc-localization-flat), and finite products of flat
modules are flat (lem-weil-pbc-finite-product-flat-modules).
3. Its spectrum map is surjective. A prime not containing I lies in some D(f i)
(lem-weil-pbc-basic-subset-immersion-image). A prime containing I lifts to S by the
specified quotient isomorphism R/I → S/IS, then by inverse image along S → S/IS.
4. Flatness and surjectivity on spectra give faithful flatness
(lem-weil-pbc-flat-surjective-spectrum-faithfully-flat).
5. Tensoring M with T gives the product of the scalar extension and the localizations
(lem-weil-pbc-tensor-finite-product, lem-weil-pbc-localization-tensor). The product
comparison is T-linear, as checked on pure tensors; tensor symmetry identifies the
S-component with the node's M ⊗ S.
6. Insert a finite generating family for each component in its product coordinate.
Their union generates the product over T, hence T ⊗ M is finite over T.
7. Descend finiteness along the faithfully flat map R → T
(lem-weil-pbc-faithfully-flat-descent-finite-module). -/
theorem finite_iff_formalGlueing {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (hflat : φ.Flat)
    (hquot : let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (I.map φ) φ
          Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] :
    letI : Algebra R S := φ.toAlgebra
    Module.Finite R M ↔
        Module.Finite S (S ⊗[R] M) ∧
          ∀ i : Fin t, Module.Finite (Localization.Away (f i))
            (LocalizedModule.Away (f i) M) :=
  sorry

end Module
