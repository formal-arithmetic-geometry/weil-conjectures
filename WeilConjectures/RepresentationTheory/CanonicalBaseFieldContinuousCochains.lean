/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.BaseFieldContinuousCochains
public import WeilConjectures.RepresentationTheory.DiscreteModule.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal

/-!
# Canonical cochain delta-functor and normalized derived comparison

Source: latest blueprint `sec-six-functors-basics/sk-lem-base-field-cd`,
`det-base-field-cd-cochains`, clause (1) and proof steps (1)--(4); Stacks Project,
Tags 010T, 015B and 05TE. (blueprint: det-base-field-cd-cochains)

The existing module supplies the coordinate predicate and the proved directed-union
and finite-quotient clauses. This statement additionally specifies the cochain and
right-derived connecting morphisms and the normalization in degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DiscreteModule

/-- Continuous cochain cohomology, with its actual homology connecting maps, is the
universal delta-functor of invariants. Its comparison with right derived invariants is
normalized by evaluation on zero-cycles and the canonical degree-zero derived comparison.
The right derived connecting maps are specified on every compatible injective horseshoe.

The degree-zero equation evaluates the class of a cycle at the unique empty tuple. It
therefore fixes the isomorphism with `M^G`, rather than just asserting some isomorphism.
The last equation fixes the degree-zero comparison by `rightDerivedZeroIsoSelf.inv`,
whose underlying map is `toRightDerivedZero`. All `eqToHom` terms merely identify the
objects along the displayed equalities of degree functors.

Proof, following the six steps of the node:
1. Compactness gives finite image for every continuous cochain and factorization through
an open normal finite quotient. Locally constant functions are precisely continuous
functions into the discrete coefficient group. The existing coordinate predicate fixes
coefficient maps and the full inhomogeneous differential.
2. For a short exact sequence, a cochain in the quotient lifts by choosing preimages of
its finitely many values on its clopen fibres. Thus its cochain sequence is degreewise
short exact. Use its homology boundary for `T.delta`; the long exact sequence and its
naturality give the delta-functor axioms with the displayed boundary formula. In degree
zero there are no incoming boundaries. Evaluation of a zero-cycle on the empty tuple
identifies it with an element of `M` killed by `g m - m` for every `g`. This gives the
natural isomorphism `z` and exactly the displayed zero-cycle normalization.
3. Embed `M` into `Map_cont(G,M)` by its orbit maps, with right translation action.
Evaluation at 1 proves injectivity, and finite clopen partitions give open stabilizers.
Homogeneous cochains identify with all continuous functions on `G^(r+1)` by evaluation
at 1, with inverse `F(g₀,...,gᵣ)(t)=f(tg₀,...,tgᵣ)`. Insertion of 1 satisfies
`dh+hd=id` in positive degrees. Hence this cochain delta-functor is effaceable.
4. Tag 010T makes `T` universal. The discrete module category has enough injectives,
and invariants is left exact and additive. The right derived delta-functor uses the
snake boundary on a compatible injective horseshoe, transported by `isoRightDerivedObj`.
Naturality for a ladder and the identity ladder show independence of the horseshoe,
giving exactly the displayed characterization of `R.delta`. These right derived
functors are universal too. Extend `z.hom` followed by the inverse of the canonical
`rightDerivedZeroIsoSelf` to a morphism of delta-functors. Extend its inverse in the
other direction. Uniqueness makes both composites identities and fixes `alpha` in degree
zero as stated. The upstream Ext comparison identifies these values with `H(G,M,n)`.
5. The retained theorem `Rep.baseFieldContinuousCochains_directedUnion` proves clause (2):
each finite cochain image lies in one stage, and exactness of filtered colimits commutes
with homology. Use the normalized comparison of step 4 to obtain the formula for `H`.
6. The retained theorem `Rep.baseFieldContinuousCochains_finiteQuotients` proves clause
(3): the inverse-limit hypothesis makes the trivial-action open normals cofinal by
compactness and intersection. Each cochain factors through one quotient. Pullback gives
the specified inflation maps and the complex colimit; filtered-colimit exactness gives
the homology colimit. Step 4 for each finite quotient identifies its terms with `H`.

Source: blueprint `det-base-field-cd-cochains`, proof (1)--(3); Stacks Project,
Homology, Tag 010T, and Derived Categories, Tags 015B/05TE.
(blueprint: det-base-field-cd-cochains) -/
theorem exists_canonicalBaseFieldContinuousCochains
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ∃ (C : DiscreteModule.{w} G ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ)
      (e : ∀ (M : DiscreteModule.{w} G) (n : ℕ),
        (C.obj M).X n ≃+ LocallyConstant (Fin n → G) M.obj.V),
      Rep.HasBaseFieldCochainCoordinates G (DiscreteModule.{w} G)
        (discreteContinuousRepEquivalence G) C e ∧
      ∃ (_hC : C.Additive),
      ∃ (hs : ∀ (S : ShortComplex (DiscreteModule.{w} G)), S.ShortExact →
          (S.map C).ShortExact)
        (T R : CohomologicalDeltaFunctor (DiscreteModule.{w} G) AddCommGrpCat.{max u w})
        (hT : T.F = (fun n ↦ C ⋙ HomologicalComplex.homologyFunctor
          AddCommGrpCat.{max u w} (ComplexShape.up ℕ) n))
        (hR : R.F = (fun n ↦ (invariants G).rightDerived n))
        (z : T.F 0 ≅ invariants G),
        T.IsUniversal ∧ R.IsUniversal ∧
        (∀ (S : ShortComplex (DiscreteModule.{w} G)) (hS : S.ShortExact) (n : ℕ),
          T.delta S hS n ≫ eqToHom (congrArg (fun F ↦ (F (n + 1)).obj S.X₁) hT) =
            eqToHom (congrArg (fun F ↦ (F n).obj S.X₃) hT) ≫
              (hs S hS).δ n (n + 1) rfl) ∧
        (∀ (M : DiscreteModule.{w} G) (x : (C.obj M).cycles 0),
          ((z.hom.app M).hom
            ((eqToHom (congrArg (fun F ↦ (F 0).obj M) hT.symm) :
              (C.obj M).homology 0 ⟶ (T.F 0).obj M).hom
              ((C.obj M).homologyπ 0 x))).1 =
            e M 0 ((C.obj M).iCycles 0 x) (fun i ↦ Fin.elim0 i)) ∧
        (∀ (S : ShortComplex (DiscreteModule.{w} G)) (hS : S.ShortExact)
          (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
          (IC : InjectiveResolution S.X₃)
          (a : IA.cocomplex ⟶ IB.cocomplex) (b : IB.cocomplex ⟶ IC.cocomplex)
          (hab : a ≫ b = 0)
          (_hA : IA.ι ≫ a = (CochainComplex.single₀ (DiscreteModule.{w} G)).map S.f ≫ IB.ι)
          (_hB : IB.ι ≫ b = (CochainComplex.single₀ (DiscreteModule.{w} G)).map S.g ≫ IC.ι)
          (_hH : ∀ k : ℕ, ((ShortComplex.mk a b hab).map
            (HomologicalComplex.eval (DiscreteModule.{w} G) (ComplexShape.up ℕ) k)).ShortExact),
          ∃ hvH : ((ShortComplex.mk a b hab).map
            ((invariants G).mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact,
            ∀ n : ℕ,
              R.delta S hS n ≫ eqToHom (congrArg (fun F ↦ (F (n + 1)).obj S.X₁) hR) =
                eqToHom (congrArg (fun F ↦ (F n).obj S.X₃) hR) ≫
                  (IC.isoRightDerivedObj (invariants G) n).hom ≫ hvH.δ n (n + 1) rfl ≫
                    (IA.isoRightDerivedObj (invariants G) (n + 1)).inv) ∧
        ∃ (alpha : CohomologicalDeltaFunctor.Hom T R)
          (beta : CohomologicalDeltaFunctor.Hom R T),
          (∀ n : ℕ, alpha.app n ≫ beta.app n = 𝟙 (T.F n)) ∧
          (∀ n : ℕ, beta.app n ≫ alpha.app n = 𝟙 (R.F n)) ∧
          alpha.app 0 ≫ eqToHom (congrArg (fun F ↦ F 0) hR) =
            z.hom ≫ (invariants G).toRightDerivedZero := by
  sorry

end DiscreteModule
