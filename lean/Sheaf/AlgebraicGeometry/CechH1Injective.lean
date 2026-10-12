/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CechH1MapNatural
import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Injectivity of the first Čech cohomology map

Source: Stacks Project, Cohomology, Lemma 0B8R (blueprint: lem-sc-cech-h1-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical map from first Čech cohomology of an open cover to first module
cohomology is injective. Source: Stacks Project, Cohomology, Lemma 0B8R
(blueprint: lem-sc-cech-h1-injective).

Proof: identify module cohomology with cohomology of the underlying abelian sheaf on the
Zariski site using lem-sc-zariski-module-abelian-cohomology-agree. Apply the convergent
first-quadrant Čech-to-cohomology spectral sequence of lem-sc-cech-spectral: the
`(1,0)` term has no incoming or outgoing higher differentials, hence equals the first
filtration piece of total degree one. The edge map is therefore injective, and composing
with the comparison isomorphism preserves injectivity. -/
theorem cechH1_injective (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) :
    ∃ c : ∀ F : X.Modules,
        ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology 1 ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace 1).obj F,
      (∀ F : X.Modules, IsModuleCechComparison U F 1 (c F)) ∧
      (∀ F : X.Modules, Function.Injective (c F).hom) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
