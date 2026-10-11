/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Proper flat morphisms with fibrewise constant functions

Source: Stacks Project, Tag 0E62, Lemma 36.32.5 (a), `perfect-lemma-proper-flat-h0`
(blueprint: lem-sc-proper-flat-global-sections-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map `O_S → f_* O_X` is an isomorphism, universally, if its proper flat
finitely presented morphism has only residue-field functions on every fibre.
Source: Stacks Project, Tag 0E62, Lemma 36.32.5 (a)
(blueprint: lem-sc-proper-flat-global-sections-criterion).

Proof: Step 1 applies `lem-pc-rf-perfect-base-change` to the structure sheaf. It is finitely
presented and flat over the base, so `K = Rf_* O_X` is perfect and commutes with every base
change. The adjunction unit `O_S → K` pulls back to the corresponding unit on each base
change. On a residue-field fibre the resulting complex is `RΓ(X_s, O_{X_s})`; its negative
cohomology vanishes and its degree-zero unit is the canonical map in the hypothesis.
Step 2 applies `lem-sc-perfect-degree-zero-fibre-criterion` to this perfect complex and unit
and obtains `O_S ≅ H⁰(K) = f_* O_X`. For any `T → S`, apply the same criterion to the derived
pullback of `K` and its unit. At a point of `T` over `s`, transitivity identifies the fibre
complex with the fibre at `s` tensored with the new residue field. Field extension is exact,
so negative cohomology still vanishes and the degree-zero unit remains an isomorphism.
Derived base change then identifies the conclusion with `O_T ≅ f_{T,*} O_{X_T}`.

The canonical map `O_S → f_* O_X` of `O_S`-modules is the unit at `O_S` of the module
adjunction `tensorPullback f ⊣ pushforward f` (`f^* O_S = O_X`), as in the hypothesis `hO`
of `lem-sc-picard-diagonal-locally-closed`; after base change along `g : T ⟶ S` it is the
unit for `p = pullback.snd f g : X_T ⟶ T`.
The fibre hypothesis uses `Γ(Spec κ(s), O) ≅ κ(s)` through `Scheme.ΓSpecIso` implicitly:
thus the map `(f.fiberToSpecResidueField s).appTop` is an isomorphism exactly when the
canonical residue-field map is. Properness supplies quasi-compactness and
quasi-separatedness, so locally finite presentation here is finite presentation. -/
theorem isIso_structureSheafMap_of_proper_flat_fiberwise
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f]
    (hfiber : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    IsIso ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app
        (SheafOfModules.unit S.ringCatSheaf)) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        IsIso ((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
            (SheafOfModules.unit T.ringCatSheaf)) := by
  sorry

end AlgebraicGeometry
