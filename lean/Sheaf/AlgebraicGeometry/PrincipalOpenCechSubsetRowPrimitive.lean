/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import Sheaf.AlgebraicGeometry.AlternatingCechComputes

/-! # Positive-degree exactness of a subset Čech row

Source: Stacks Project, Cohomology, Tags 01EP, 01FM and 08C1.
(blueprint: lem-sc-principal-open-cech-subset-row-primitive).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Positive-degree exactness of the subset Čech row, with integer transports.

Source: Stacks Project, Cohomology, Tags 01EP, 01FM and 08C1 (first paragraph).
(blueprint: lem-sc-principal-open-cech-subset-row-primitive).

Proof: On subsets of size k+1 identify the displayed coefficient with J^(n+1-k).
The hypothesis is exactly the alternating restriction cocycle equation on subsets
of size k+2. Use the cover D(f_i) of its union, injective module Čech acyclicity
(Tag 01EP), and the comparison to increasing tuples (Tag 01FM). The range of an
increasing tuple is a subset of the same cardinality, its intersection is the basic
open of the product, and its deletion position counts the smaller elements.
For the comparison, regard this cover as a cover of the open subscheme V and
restrict the underlying presheaf to its opens. Its full and ordered complexes
have the same sections and restriction maps as the corresponding complexes of
opens inside X. Thus full cohomology vanishing on V, already given by Tag 01EP
for the injective sheaf on X, transfers through Tag 01FM; injectivity of the
underlying abelian sheaf is neither assumed nor needed. The sign (-1)^j acting
by integer scalar multiplication is the same as (-1 : A)^j acting on sections.
Positive-degree vanishing gives a primitive on subsets of size k. Transport its
coefficients back to degree n+1-|S| and extend by zero on all other subsets.
Proof irrelevance identifies the arithmetic transports with he. When k+1>r the
row is zero; use the zero primitive. Empty and repeated opens are permitted by
Čech acyclicity. No differential of J or total complex is used in this argument. -/
theorem principalOpenCech_subset_row_primitive
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (n : ℤ) (k : ℕ), 1 ≤ k → Injective (J.X (n + 1 - (k : ℤ))) →
      ∀ c : (∀ S : {S : Finset (Fin r) // S.Nonempty},
        (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))),
      (∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = k + 2 →
        (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property (n + 1))))).hom.app
                    (op (D (S.val.erase j.val))) (c ⟨S.val.erase j.val, h⟩))
          else 0) = 0) →
      ∃ b : (∀ S : {S : Finset (Fin r) // S.Nonempty},
        (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj
          (op (D S.val))),
        (∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card ≠ k → b S = 0) ∧
        (∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = k + 1 →
          (∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) (b ⟨S.val.erase j.val, h⟩))
          else 0) = c S) := by sorry

end AlgebraicGeometry
