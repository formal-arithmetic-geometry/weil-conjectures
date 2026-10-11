/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.Coherent
import Mathlib.Topology.Sets.Closeds

/-! # Coherent pushforward from an open with closed ambient support

Source: Stacks Project, Cohomology of Schemes, Lemma 30.9.11 (Tag 0CYJ)
(blueprint: lem-weil-pbc-pushforward-coherent-on-open).
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- If a coherent module on an open subscheme has support contained in a closed subset
of the ambient scheme lying inside that open, its direct image is coherent. Its restriction
back to the open is isomorphic to the original module, and its restriction to the complement
of the closed subset is zero. Support is the nonzero-stalk locus, as in
`def-weil-pbc-closed-subset-proper-over-base`; no properness assumption is needed here.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.9.11 (Tag 0CYJ)
(blueprint: lem-weil-pbc-pushforward-coherent-on-open).

Proof:
1. On an open of `U`, the pushforward has exactly the sections and restriction maps of `F`,
   with the same structure-sheaf action. Thus its restriction to `U` is `F`
   (def-pc-module-pullback; lem-weil-pbc-module-restriction-open-immersion-colimits;
   Mathlib's `restrictFunctorAdjCounitIso`).
2. Every stalk of `F` outside `T` is zero (def-weil-pbc-module-stalk and the support definition).
   A section there has zero germ at every point, hence is zero by the sheaf property
   (lem-weil-pbc-sheaf-sections-determined-by-germs). Thus `F` vanishes on `U` minus `T`.
3. For an open `V` in `X` minus `T`, the sections of the pushforward are the sections of `F`
   on `V` intersect `U`, which vanish by step 2. Its restriction to `T.compl` is therefore zero
   (def-pc-module-pullback; lem-weil-pbc-module-restriction-open-immersion-colimits).
4. The opens `U` and `T.compl` cover `X`. The restrictions are coherent: the first by the
   hypothesis, the second because the zero module is coherent (pqf-def-coherent).
   Coherence is local on an open cover (lem-weil-pbc-coherent-module-local-on-open-cover),
   so the pushforward is coherent. -/
theorem pushforward_coherent_on_open (X : Scheme.{u}) (U : X.Opens) (T : Closeds X)
    (hT : (T : Set X) ⊆ (U : Set X)) (F : U.toScheme.Modules)
    (hF : RingedSpace.IsCoherent U.toScheme.toRingedSpace F)
    (hSupp : {x : U.toScheme | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      U.ι.base ⁻¹' (T : Set X)) :
    RingedSpace.IsCoherent X.toRingedSpace ((pushforward U.ι).obj F) ∧
      Nonempty ((restrictFunctor U.ι).obj ((pushforward U.ι).obj F) ≅ F) ∧
      IsZero ((restrictFunctor (Scheme.Opens.ι T.compl)).obj ((pushforward U.ι).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
