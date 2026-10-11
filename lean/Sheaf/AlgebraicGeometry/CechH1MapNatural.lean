/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison

/-! # Naturality of the first Čech-to-cohomology comparison

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EQ
(blueprint: lem-sc-cech-h1-map-natural).

The canonical comparison is characterized by the existing `IsModuleCechComparison`
predicate, so its existence cannot be witnessed by an arbitrary natural homomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- For every open cover of a scheme, the canonical comparison from first Čech cohomology
of an `O_X`-module to its first module cohomology exists and is natural in the module.
Source: Stacks Project, Cohomology of Sheaves, Lemma 01EQ
(blueprint: lem-sc-cech-h1-map-natural).

Proof:
1. By lem-weil-pbc-scheme-modules-enough-injectives and def-sp-injective-resolutions,
choose an injective resolution. Form its Čech double complex (def-weil-pbc-site-cech-complex)
and total complex (def-sp-double-complex-total). Restrictions of global sections give alpha;
the resolution augmentation gives beta. Both commute with the differentials.
2. By lem-weil-pbc-module-injective-open-cover-cech-acyclic the horizontal rows have zero
positive cohomology, and the sheaf axiom identifies their degree-zero cohomology with global
sections. The row-first spectral sequence (thm-sp-double-complex-spectral-sequences) implies
that alpha induces an isomorphism on total cohomology.
3. Compose H(beta) with the inverse of H(alpha) and the resolution identification for
pqf-def-cohomology. Comparison maps (lem-weil-pbc-injective-resolution-lift-exists) and
lem-weil-pbc-derived-functor-map-via-lift show that the resulting map satisfies
IsModuleCechComparison for every resolution, independently of the chosen resolution.
4. Lift a module morphism to the two resolutions. Termwise Čech functoriality gives a map
of total complexes. Its squares with alpha commute by naturality of restriction and those
with beta commute by the lifting equation. Taking first cohomology and using the lifted
formula for the right derived map gives the displayed equality. -/
theorem cechH1Map_natural (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) :
    ∃ c : ∀ F : X.Modules,
        ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology 1 ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace 1).obj F,
      (∀ F : X.Modules, IsModuleCechComparison U F 1 (c F)) ∧
      ∀ (F F' : X.Modules) (φ : F ⟶ F'),
        HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map
            ((PresheafOfModules.forgetToPresheafModuleCat
              (op ⊤) isTerminalTop.op).map φ.val)) 1 ≫ c F' =
          c F ≫ (RingedSpace.moduleCohomology X.toRingedSpace 1).map φ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
