/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Hom from a complex concentrated in one degree

Source: Stacks Project, Tag 0A8X, Hom complexes; Tag 08DM, bounded Hom calculation;
Tag 010N, exact functors. The argument isolates step 1 of the bounded exact-term proof.
(blueprint: lem-pc-single-degree-exact-term-hom-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Internal Hom from a complex concentrated in one degree preserves quasi-isomorphisms
if internal Hom from its sole possibly nonzero term preserves short exact sequences.

Source: Stacks Project, Tag 0A8X, Hom complexes; Tag 08DM, bounded Hom calculation;
Tag 010N, exact functors.
(blueprint: lem-pc-single-degree-exact-term-hom-quasi-iso).

Proof: all factors of the degree-n Hom product other than the factor at k are zero:
internal Hom from a zero object is zero. The product universal property identifies
that degree with internal Hom from P.X k to M.X (k+n). The source differential is zero,
so the Hom differential is just postcomposition with the target differential. These
identifications commute with postcomposition by f. Internal Hom from P.X k is additive,
as follows sectionwise from addition of localized linear maps. Its short-exact-sequence
preservation implies finite-limit and finite-colimit preservation by the exact-functor
criterion (Tag 010N). The natural homology comparison for an exact functor identifies
homology of its degreewise image with its image of homology. Thus the map at every
homology degree is an isomorphism since f is a quasi-isomorphism. Translating the
integer grading by k preserves this assertion; no bound on M or N is needed.
The argument includes the case P.X k is zero and then all Hom terms are zero. -/
theorem quasiIso_homComplex_map_of_single_degree_exact_term
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k : ℤ) (hsingle : ∀ n : ℤ, n ≠ k → IsZero (P.X n))
    (hexact : ∀ (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X k)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X k)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X k)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X k)) S.g) hz).ShortExact)
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map f) := by sorry

end CategoryTheory
