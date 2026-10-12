/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Algebra.Homology.TruncationTelescope

/-!
# K-flat resolutions on a ringed site

Source: Stacks Project, Cohomology on Sites, Lemma 06YS
(`sites-cohomology-lemma-K-flat-resolution`) (blueprint: lem-pc-kflat-resolution).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

/-- Every complex of modules over a sheaf of commutative rings on a site admits a K-flat
resolution with flat terms and a degreewise surjective augmentation. Surjectivity is in the
category of sheaves of modules, i.e. an epimorphism, rather than surjectivity on all sections.
Source: Stacks Project, Lemma 06YS (blueprint: lem-pc-kflat-resolution).

Proof outline recorded in the DAG:
1. Replace each good truncation of `G` by a bounded-above flat complex with a termwise
   surjective quasi-isomorphism, compatibly with the transition maps
   (`lem-pc-kflat-bounded-flat-replacement`).
2. Form the telescope, the cone of one minus the shift on the countable direct sum of these
   replacements. Bounded-above flat complexes, their sums and their cones are K-flat;
   their terms are flat (`lem-pc-kflat-closure`). The induced map to the telescope of the
   truncations is degreewise surjective. Its composite with the augmentation to `G` is
   degreewise surjective, since the truncations agree with `G` in each fixed degree eventually.
3. Direct sums of the replacement quasi-isomorphisms are quasi-isomorphisms, by exactness of
   filtered colimits of finite sums (`lem-pc-kflat-hocolim-truncations`). The long exact
   cohomology sequences of the cones and the five lemma give a quasi-isomorphism on
   telescopes. The telescope of truncations maps quasi-isomorphically to `G` by the same node.
4. The composite is the desired degreewise surjective quasi-isomorphism from a K-flat
   complex with flat terms. -/
theorem exists_isKFlatResolution
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    ∃ (K : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (f : K ⟶ G), K.IsKFlat ∧ (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  sorry

end CochainComplex
