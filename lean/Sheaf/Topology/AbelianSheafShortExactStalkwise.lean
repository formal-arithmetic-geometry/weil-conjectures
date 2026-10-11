/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Short exactness of abelian sheaves is detected on stalks

Source: literature/stacks-project/modules.tex, Modules, Lemma 01AG (lemma-abelian),
specialized to the constant sheaf of integers; Sheaves, Section 007S
(section-exactness-points) (blueprint: lem-sc-abelian-sheaf-short-exact-stalkwise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace TopCat

/--
Source: literature/stacks-project/modules.tex, Modules, Lemma 01AG (lemma-abelian),
specialized to the constant sheaf of integers; Sheaves, Section 007S
(section-exactness-points).

For a short complex of abelian sheaves, short exactness is equivalent to short
exactness of its stalk complex at every point. The forward implication maps the
short exact complex along each stalk functor. Conversely, exactness in the
middle
is detected by `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`, while the
monomorphism and epimorphism conditions are detected by the stalk criteria;
these three conditions are recombined using the definition of `ShortExact`.
(blueprint: lem-sc-abelian-sheaf-short-exact-stalkwise)
-/
theorem shortExact_iff_stalkFunctor_map_shortExact
    {X : TopCat.{u}}
    (S : ShortComplex (Sheaf AddCommGrpCat X)) :
    S.ShortExact ↔
      ∀ (x : X), (S.map (Sheaf.forget AddCommGrpCat X ⋙ Presheaf.stalkFunctor (X := X)
        AddCommGrpCat x)).ShortExact := by
  sorry

end TopCat
