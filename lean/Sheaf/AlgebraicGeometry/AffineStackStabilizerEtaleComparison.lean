/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed

/-! # Étale comparison over an affine-covered stack

Source: Stacks Project, `stacks-more-morphisms.tex`, Tags 0DUS and 0DUR
(blueprint: lem-sfb-affine-stack-stabilizer-etale-comparison).

All chart tests use the recorded total-category and algebraic-space interfaces.
The conditions defining a finite flat affine cover and a uniform categorical map
are expanded in the statement, as in the DAG node. The comma comparison retains
both projections and the natural isomorphism making the square commute.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A representable separated étale stabilizer-preserving map descends to a separated
étale scheme map over an affine uniform categorical quotient.
Source: Stacks Project, `stacks-more-morphisms.tex`, Tag 0DUS,
`lemma-etale-separated-over-well-nigh-affine`, with Tag 0DUR
(blueprint: lem-sfb-affine-stack-stabilizer-etale-comparison).

Proof:
1. Apply `lem-sfb-finite-flat-affine-stack-invariant-quotient` to the affine cover.
   Categorical uniqueness identifies its invariant quotient with the given `M`.
   The quotient is a universal homeomorphism; use
   `lem-sfb-stack-topology-open-substacks` for the correspondence of opens.
2. Pull the cover back to `B`. The result `V` is an algebraic space separated
   étale over the affine cover. Use `lem-sfb-space-separated-diagonal-closed`
   and `lem-a1-separated-etale-space-scheme` to obtain a scheme. By
   `lem-a1-etale-space-locally-quasi-finite` and
   `lem-sfb-separated-lqf-affine-finite-set`, every finite subset has an affine
   neighbourhood. The relation is finite locally free by
   `def-pc-finite-locally-free`. Use `lem-sfb-fppf-groupoid-stack-presentations`,
   `lem-sfb-locally-free-groupoid-invariant-affine` and
   `lem-sfb-finite-flat-groupoid-quotient-open-geometry` to cover `B` by invariant
   affine-covered open stacks. Base-change properties use
   `lem-sfb-stack-chartwise-smooth-etale-calculus`.
3. The induced groupoid maps have cartesian source and target squares by the
   explicit triples defining the two-fibre product. The stabilizer square is
   cartesian by the automorphism hypothesis. Apply
   `lem-sfb-affine-groupoid-etale-invariant-comparison` and
   `lem-sfb-quotient-stack-invariant-base-change` to obtain the local cartesian
   squares with affine schemes `Nᵢ` étale over `M`.
4. Open overlaps correspond under the universal homeomorphisms. The uniform
   categorical properties give unique overlap isomorphisms; uniqueness on triple
   intersections proves the cocycle condition. Apply `lem-weil-pbc-glue-schemes`
   to glue the `Nᵢ` and their maps to `M`.
5. Glue the maps from the open stacks to obtain `qB`. Stack descent checks the
   comparison equivalence on the open cover, and étaleness is local there, by
   `def-sfb-stable-pointed-moduli-groupoids`, `def-pc-scheme` and
   `lem-sfb-stack-chartwise-smooth-etale-calculus`.
6. The map `V → N` is surjective and universally closed: locally its affines are
   integral over their invariant rings by `lem-a1-affine-groupoid-integral-invariants`
   and `pqf-lem-integral-univclosed`. The composite `V → M` is separated by
   `lem-weil-pbc-affine-source-morphism-separated` and
   `lem-sfb-space-separated-fp-composition`. Apply
   `lem-weil-pbc-surjective-universally-closed-separated` to deduce separatedness
   of `N → M`. All constructions and compatibilities are over `S`.

The cover tests give scheme representatives, with their actual projections.
Flatness of an algebraic space over `M` is tested on every étale scheme chart.
Separatedness of `h` is properness of the diagonal of each space base change.
Bijectivity on fibre isomorphisms is the isomorphism on automorphism sheaves:
quantification over all test schemes also tests every restriction of every object.
The final equivalence has first projection `qB` and second projection exactly `h`;
its comma isomorphisms are the specified commutative square. -/
theorem exists_affineStack_stabilizer_etale_comparison
    {S : Scheme.{u}}
    (A : BasedCategory.{v₁, w₁} (Over S))
    (B : BasedCategory.{v₂, w₂} (Over S))
    (hA : IsDeligneMumfordModuliStack A) (hB : IsDeligneMumfordModuliStack B)
    (U : Over S) (hU : IsAffine U.left)
    (p : BasedFunctor (discreteModuli (yoneda.obj U)) A)
    (hp : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) A),
      ∃ (V : Over S) (f : V ⟶ T)
        (e : BasedFunctor (discreteModuli (yoneda.obj V)) (moduliTwoFiberProduct t p)),
        e.toFunctor.IsEquivalence ∧
        Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst t p))
          (discreteModuliMap (yoneda.map f))) ∧
        IsFinite f.left ∧ Flat f.left ∧ LocallyOfFinitePresentation f.left ∧ Surjective f.left)
    (M : Over S) (hM : IsAffine M.left)
    (q : BasedFunctor A (discreteModuli (yoneda.obj M)))
    (hq : ∀ (M₁ : AlgebraicSpace S) (a : M₁.obj.obj ⟶ yoneda.obj M),
      (∀ (T : Over S) (b : yoneda.obj T ⟶ M₁.obj.obj),
        AlgebraicSpace.IsEtale b → Flat (yoneda.preimage (b ≫ a)).left) →
      ∀ Z : AlgebraicSpace S,
        Function.Bijective (fun f : M₁.obj.obj ⟶ Z.obj.obj ↦
          (moduliTwoFiberFst (discreteModuliMap a) q).comp (discreteModuliMap f)))
    (h : BasedFunctor B A) (hrep : IsRepresentableByAlgebraicSpaces h)
    (het : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) A)
      (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange h T t Z a → SpaceMapIsEtale Z T a)
    (hsep : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) A)
      (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange h T t Z a →
        AlgebraicSpace.IsRepresentableWith (fun _ _ f ↦ IsProper f.left)
          (pullback.diagonal a))
    (haut : ∀ (T : Over S) (b : Functor.Fiber B.p T),
      Function.Bijective (fun α : b ≅ b ↦ (moduliFiberMap h T).mapIso α)) :
    ∃ (N : Over S) (f : N ⟶ M), IsSeparated f.left ∧ Etale f.left ∧
      ∃ (qB : BasedFunctor B (discreteModuli (yoneda.obj N)))
        (e : BasedFunctor B (moduliTwoFiberProduct (discreteModuliMap (yoneda.map f)) q)),
        e.toFunctor.IsEquivalence ∧
        e.comp (moduliTwoFiberFst (discreteModuliMap (yoneda.map f)) q) = qB ∧
        e.toFunctor ⋙ ObjectProperty.ι _ ⋙
          Comma.snd (discreteModuliMap (yoneda.map f)).toFunctor q.toFunctor = h.toFunctor := by
  sorry

end AlgebraicGeometry
