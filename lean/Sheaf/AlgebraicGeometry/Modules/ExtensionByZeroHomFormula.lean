/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # A component of extension by zero for modules
Source: Stacks Project, Sheaves, Lemma 00A7. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical adjunction has the stated formula on each direct-sum injection.
Source: Stacks Project, Sheaves, Definition 00A4 and Lemma 00A7 (2).
(blueprint: lem-weil-pbc-module-extension-by-zero-hom-formula).

Proof: A map from the extension presheaf to a global module sends each summand
indexed by V → U through a module morphism on U. Conversely such a morphism defines
a map on each summand; the direct-sum universal property gives its components.
Naturality follows on summands from naturality on U. The constructions are inverse
on each injection and natural in both modules. Compose this Hom equivalence with
the sheafification Hom equivalence. Its formula is the evaluation of the composite
on each injection, which is precisely the asserted equation. -/
theorem module_extensionByZero_hom_formula (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∃ adj : L ⊣ SheafOfModules.overFunctor R U,
        (∀ (F : SheafOfModules.{u} (R.over U)) (G : X.Modules)
          (ψ : L.obj F ⟶ G) (V : X.Opens) (h : V ⟶ U)
          (s : F.val.obj (op (Over.mk h))),
          ((adj.homEquiv F G ψ).val.app (op (Over.mk h))) s =
            (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) ψ).app (op V)
              (DirectSum.of (fun φ : V ⟶ U => F.val.obj (op (Over.mk φ))) h s)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
