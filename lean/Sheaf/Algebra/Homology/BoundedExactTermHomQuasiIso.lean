/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Bounded Hom complexes with exact internal Hom in each source degree

Source: Stacks Project, Cohomology of Sheaves, Tag 08DM, bounded Hom calculation,
and Homology, Tag 0117, long exact cohomology sequence.
(blueprint: lem-pc-bounded-exact-term-hom-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A bounded source complex whose termwise internal Hom preserves short exact sequences
sends every quasi-isomorphism in the second variable to a quasi-isomorphism. The second
variable is arbitrary, and no K-injective resolution or derived category occurs here.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DM, bounded Hom calculation;
Homology, Tag 0117, long exact cohomology sequence.
(blueprint: lem-pc-bounded-exact-term-hom-quasi-iso).

Proof:
1. Choose bounds a and b for P. For a complex concentrated in a single degree k,
   the Hom complex is the shifted complex obtained by applying Hom(P^k,-) degreewise.
   This functor is additive (postcomposition is additive on localized linear maps).
   Preservation of short exact sequences in an abelian category implies exactness,
   so it commutes with cohomology and sends quasi-isomorphisms to quasi-isomorphisms.
2. Filter P by its stupid tails in degrees at least k. The quotient of consecutive
   tails is P^k placed in degree k. Applying Hom(-,M) to the degreewise split sequence
   gives a degreewise split short exact sequence with terms Hom(P^k[-k],M),
   Hom(tail k,M), Hom(tail (k+1),M); likewise for N. Restriction of product factors
   gives the chain maps, with the Hom differential specifying their compatibility.
3. The maps induced by f form a morphism of these short exact sequences. The long
   exact cohomology sequences and the five lemma show that the middle map is a
   quasi-isomorphism whenever the outer maps are. Start with the zero tail above b
   and induct down to a, using step 1 for each graded piece. Below a the omitted
   terms are zero, so this is the Hom complex of P itself. There are only finitely
   many source degrees, even if M and N are unbounded; thus no exactness of infinite
   products is required. If b < a, every source term is zero and the assertion is
   the quasi-isomorphism between zero complexes. -/
theorem quasiIso_homComplex_map_of_bounded_exact_terms
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hexact : ∀ (n : ℤ) (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.g) hz).ShortExact)
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map f) := by sorry

end CategoryTheory
