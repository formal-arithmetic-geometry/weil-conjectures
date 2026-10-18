/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Sheaf.AlgebraicGeometry.FieldExtensionFpqcCover
import Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.AlgebraicGeometry.UnramifiedOrdinaryFibreCriterion

/-!
# Unramifiedness tested on geometric fibres

Source: Stacks Project, Morphisms, Tags 02G7 and 02G8; Descent, Tag 02VM
(blueprint: lem-trf-geometric-fibre-unramified-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finite type morphism is unramified if and only if its geometric fibres are
unramified. The algebraic closure chosen at each point is Mathlib's `AlgebraicClosure`.
Empty geometric fibres are permitted, and the base scheme is arbitrary.
Source: Stacks Project, Morphisms, Tags 02G7 and 02G8; Descent, Tag 02VM
(blueprint: lem-trf-geometric-fibre-unramified-criterion).

Proof:
1. Apply `lem-weil-pbc-unramified-base-change-open` to the canonical geometric point
   defining each geometric fibre (`def-weil-geometric-fibre`).
2. Conversely, form the ordinary fibre (`def-pc-scheme-fibre`). Its base change along
   the algebraic-closure extension is the given geometric fibre. This extension is an
   fpqc singleton cover by `lem-pc-field-extension-fpqc-cover`. Descend unramifiedness
   using `lem-galois-fpqc-descend-unramified`.
3. By `lem-trf-unramified-field-fibre-decomposition` (Tag 02G7), every ordinary fibre is
   a disjoint union of spectra of finite separable extensions of the residue field.
4. Apply `lem-trf-unramified-ordinary-fibre-criterion` (Tag 02G8(2)), using the given
   local finite type hypothesis (`def-weil-finite-type-morphism`). -/
theorem unramified_iff_unramified_geometric_fibres
    {Z B : Scheme.{u}} (h : Z ⟶ B) [LocallyOfFiniteType h] :
    (LocallyOfFiniteType h ∧ IsOpenImmersion (pullback.diagonal h)) ↔
      ∀ s : B,
        LocallyOfFiniteType
          (pullback.snd h
            (Spec.map (CommRingCat.ofHom
              (algebraMap (B.residueField s) (AlgebraicClosure (B.residueField s)))) ≫
                B.fromSpecResidueField s)) ∧
          IsOpenImmersion
            (pullback.diagonal
              (pullback.snd h
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (B.residueField s) (AlgebraicClosure (B.residueField s)))) ≫
                    B.fromSpecResidueField s))) := by
  sorry

end AlgebraicGeometry
