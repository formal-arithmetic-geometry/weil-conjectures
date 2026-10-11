/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.Coherent

/-! # Extension of a quasi-coherent module across a quasi-compact open

Source: Stacks Project, Properties, Lemma 01PE (lemma-extend-trivial), part (3)
and its proof (properties.tex, lines 2787--2843).
(blueprint: lem-weil-pbc-quasi-coherent-extension-qc-open)

Restriction to an open is expressed on the localized site with `SheafOfModules.over`,
on the `moduleRings` carrier, as in the sibling extension lemmas.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module and a map on a quasi-compact open extend across the open.
Source: Stacks Project, Properties, Lemma 01PE (lemma-extend-trivial), part (3)
and its proof (properties.tex, lines 2787--2843).
(blueprint: lem-weil-pbc-quasi-coherent-extension-qc-open)

Proof:
1. The open immersion is quasi-compact by hypothesis and quasi-separated because it is
   an open immersion (hence a monomorphism and separated), using
   lem-weil-pbc-open-immersion-monomorphism and def-weil-quasi-separated-morphism.
2. Restriction preserves quasi-coherence
   (lem-weil-pbc-module-restriction-open-immersion-colimits). Push forward the given
   module and the restriction of `F`; these are quasi-coherent by pqf-lem-pushforward-qcoh.
   Their direct sum is quasi-coherent (lem-weil-pbc-quasi-coherent-module-direct-sum).
   Form the map `d : F ⊞ j_*G ⟶ j_*(F|_U)` given sectionwise by restriction minus
   the pushed-forward map.
3. Let `H = Ker d` and let `ψ` be the first projection. Quasi-coherence of kernels
   gives quasi-coherence of `H` (lem-weil-pbc-quasi-coherent-module-kernel).
4. Over `U`, projection to the second component gives an isomorphism
   `α : H|_U ≅ G`, with inverse `g ↦ (φ(g), g)`, and the defining equation gives
   `ψ|_U = α.hom ≫ φ`; restriction is as in
   lem-weil-pbc-module-restriction-open-immersion-colimits.
-/
theorem exists_quasiCoherent_extension_of_quasiCompact_open
    (X : Scheme.{u}) (U : X.Opens) (hU : QuasiCompact U.ι)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) [G.IsQuasicoherent]
    (φ : G ⟶ F.over U) :
    ∃ (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)), H.IsQuasicoherent ∧
      ∃ (ψ : H ⟶ F) (α : H.over U ≅ G),
        (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map ψ = α.hom ≫ φ :=
  sorry

end AlgebraicGeometry.Scheme.Modules
