/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FinitelyPresentedOverSubring

/-!
# Finite presentation of modules over finite finitely presented extensions

Source: Stacks Project, Algebra, Tag 0564, lemma-finite-finitely-presented-extension
(blueprint: lem-trf-finite-extension-module-finite-presentation).
-/

@[expose] public section

universe u v w

namespace Module

/-- For a finite, finitely presented extension of commutative rings, an `S`-module is
finitely presented over `R` exactly when it is finitely presented over `S`.
Source: Stacks Project, Algebra, Tag 0564, lemma-finite-finitely-presented-extension
(blueprint: lem-trf-finite-extension-module-finite-presentation).

Proof plan:
1. The finite-module and finite-algebra-presentation hypotheses imply that `S` is finitely
   presented as an `R`-module, by `Module.FinitePresentation.of_finite_of_finitePresentation`
   (lem-weil-pbc-finite-algebra-presentation-module-presentation). If `M` is finitely presented
   over `S`, apply `Module.FinitePresentation.trans`
   (lem-pc-module-finite-presentation-transitive) to obtain finite presentation over `R`.
2. Conversely, finite `R`-module generators of `S` also generate it as an `R`-algebra:
   every element is already an `R`-linear combination of those generators. Thus `S` is of
   finite type over `R` (def-weil-pbc-finite-type-algebra). If `M` is finitely presented over
   `R`, Tag 0561 (lem-trf-finitely-presented-over-subring) gives finite presentation over `S`.
-/
theorem finitePresentation_iff_of_finite_of_finitePresentation
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite R S] [Algebra.FinitePresentation R S] :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S M := by
  constructor
  · intro hM
    apply FinitePresentation.of_finiteType_subring (algebraMap R S)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
    have hmodule : Module.compHom M (algebraMap R S) = (inferInstance : Module R M) :=
      Module.ext' _ _ fun r m ↦ IsScalarTower.algebraMap_smul S r m
    rw [hmodule]
    exact hM
  · intro hM
    let := hM
    let := FinitePresentation.of_finite_of_finitePresentation R S
    exact FinitePresentation.trans R M S

end Module
