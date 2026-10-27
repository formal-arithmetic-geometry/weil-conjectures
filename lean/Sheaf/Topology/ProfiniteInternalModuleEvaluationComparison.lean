/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C7
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison

/-! # Evaluation of arbitrary internal module resolutions

Source: Stacks Project, Tags 00YV and 03FD.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace Profinite

/-- Evaluating any injective internal module resolution computes abelian derived
sections of its underlying sheaf. No injectivity after forgetting is required.
Source: Stacks Project, Tags 00YV and 03FD; step 3 of
lem-sfb-finite-normed-scalar-section-acyclicity.
(blueprint: lem-sfb-profinite-internal-module-evaluation-comparison).

Proof: Reconstruct the section ring and use sectionModuleEquivalence to transport
the resolution to sectionwise module sheaves. This equivalence is exact and preserves
injectives, and its underlying abelian sections and maps agree with the original
ones. The ringed-site module/abelian comparison (03FD) identifies the cohomology of
this arbitrary resolution on V with abelian right derived evaluation of M.X.
It applies in the common coefficient universe u+1; equivalently lift the site's hom
sets to that universe before applying the small-site formulation and transport back
along the resulting site equivalence. Injective module sheaves are acyclic for
abelian evaluation, which suffices even though their underlying abelian sheaves need
not be injective. Compose the comparison with the transported resolution isomorphism
and the identity of its section complex. This works in every positive degree
and on the empty object, for every module M and every chosen injective resolution. -/
theorem nonempty_internalModule_eval_homology_iso
    (R : CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}))
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) R.X)
    (I : InjectiveResolution M) (V : Profinite.{u}) (q : ℕ) (hq : 0 < q) :
    Nonempty
      (((((Mod.forget R.X ⋙
        sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} ⋙
          (evaluation Profinite.{u}ᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
            (.up ℕ)).obj I.cocomplex).homology q) ≅
        (((sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} ⋙
          (evaluation Profinite.{u}ᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).rightDerived q).obj
            M.X)) := by
  sorry

end Profinite
