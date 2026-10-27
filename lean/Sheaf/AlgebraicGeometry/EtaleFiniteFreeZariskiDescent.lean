/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction

/-!
# Descent of étale finite local freeness to the Zariski topology

Source: Stacks Project, Descent, Tags 05VG, 05B2 and 03DX (2)
(blueprint: lem-sfb-etale-finite-free-zariski-descent).

The finite-local-freeness predicate on either site is the existing
`SheafOfModules.IsFiniteLocallyFree`, whose finite ranks may vary over the covering.
The existential witnesses contain only continuity and right-adjoint-existence proofs;
the restriction, extension and pullbacks are the recorded canonical constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite local freeness after a jointly surjective étale family descends to Zariski
finite local freeness under the quasi-coherent equivalence. Conversely, extension of
a Zariski finite locally free module is finite locally free on the small étale site.
The witnesses `c` and `hp` provide only proofs required by the canonical functor API;
no additional hypothesis is imposed on the scheme, modules, ranks or covering family.

Source: Stacks Project, Descent, Tags 05VG, 05B2 and 03DX (2)
(blueprint: lem-sfb-etale-finite-free-zariski-descent).

Proof, following the five DAG steps:
1. Restrict F to Zariski opens to obtain G. The quasi-coherent equivalence
   (lem-trf-scheme-zariski-etale-quasi-coherent-equivalence) says G is quasi-coherent,
   its extension is F, and extension commutes with tensor pullback. Pullback preserves
   quasi-coherence by lem-weil-pbc-module-pullback-quasi-coherent.
2. On each member of the given family choose an étale covering with finite free
   frames. By lem-trf-etale-extension-free-presentations-hom, restriction of the
   extension of the ordinary pulled-back G recovers that module. Restrict the frames
   to Zariski opens. Finite sums of structure modules restrict to the corresponding
   finite sums, sectionwise as tuples of functions. Tensor-pullback composition
   (def-pc-module-pullback) gives finite free frames for pullbacks along the composite
   covering maps.
3. These composites are étale by lem-weil-pbc-etale-composition-cancellation and
   jointly surjective by lifting a point twice. They are a small étale covering
   (def-weil-pbc-etale-site), hence an fpqc covering by
   lem-weil-pbc-fpqc-finer-than-etale.
4. Apply finite-local-freeness reflection in lem-pc-fpqc-descent to G and this
   covering. This gives finite local freeness itself, with no common rank imposed.
5. Conversely, choose Zariski finite free frames of H. Such H is quasi-coherent
   (pqf-def-coherent). The open immersions form an étale covering. By
   lem-weil-pbc-open-immersion-module-pullback-restriction and
   lem-trf-etale-extension-free-presentations-hom, extension restricts on that
   covering to the extension of each frame, which is a finite sum of the étale
   structure module. These are the required étale frames. On the empty scheme the
   local assertions are vacuous; zero-rank frames use the empty finite sum.
-/
theorem etale_finite_free_zariski_descent (T : Scheme.{u}) :
    ∃ (c : ZariskiEtaleModuleContext T)
      (hp : ∀ (U : Scheme.{u}) (e : U ⟶ T),
        (smallEtaleModulePushforward e).IsRightAdjoint),
      (∀ (F : SmallEtaleModules T) [F.IsQuasicoherent]
          (ι : Type v) (U : ι → Scheme.{u}) (e : ∀ a, U a ⟶ T)
          [∀ a, Etale (e a)],
        (∀ x : T, ∃ (a : ι) (y : U a), e a y = x) →
        (∀ a, SheafOfModules.IsFiniteLocallyFree
          ((smallEtaleModulePullback (e a) (hp (U a) (e a))).obj F)) →
        (c.restriction.obj F).IsFiniteLocallyFree) ∧
      (∀ (H : T.Modules), H.IsFiniteLocallyFree →
        (c.extension.obj H).IsFiniteLocallyFree) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
