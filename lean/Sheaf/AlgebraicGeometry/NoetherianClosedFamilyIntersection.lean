module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange

/-! # Finite universal intersections of closed subschemes in a Noetherian open

Source: Bourbaki Expose 221, proof of Lemma 3.4 after Lemma 3.6, printed p.264;
Stacks Project, Tags 01HP, 0C4H, 01QQ, 01IN and 01Y8. The ideal-sum and finite-chart
expansion is the agent-written proof recorded in the DAG
(blueprint: lem-sfb-noetherian-closed-family-intersection).

The sum is Mathlib's supremum of `Scheme.IdealSheafData`; its closed subscheme and
quotient charts are Mathlib's `subscheme`, `subschemeι` and `subschemeCover`.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A set-indexed family of quasi-coherent ideals on an open of a Noetherian scheme
has a finite subsum, and its sum cuts out the universal intersection, including on
arbitrary nonreduced test schemes. The affine chart square uses the actual quotient
map `glueDataObjι`. The last clause gives finite principal charts over each affine
open of the ambient scheme, including their localization algebras and quotient cover.

Source: Bourbaki Expose 221, proof of Lemma 3.4, printed p.264; Stacks Project,
Tags 01HP, 0C4H, 01QQ, 01IN, 01Y8 and 01T2
(blueprint: lem-sfb-noetherian-closed-family-intersection).

Proof:
1. On every affine open of S, the coordinate ring is Noetherian
   (pqf-lem-affine-open-locnoeth). Generate the ideal of the complement of V by
   finitely many elements (def-weil-pbc-noetherian-ring); their principal opens
   cover V there. A finite affine cover of S therefore gives a finite affine
   cover of V, with Noetherian coordinate rings. Empty covers are permitted.
2. Sum the given ideals on affine opens. Affine section base change
   (lem-weil-pbc-quasi-coherent-affine-section-base-change) shows compatibility
   with principal localization. Construct the closed subscheme with these ideals
   using lem-weil-pbc-affine-ideals-closed-subscheme; its kernel ideal is the sum
   on every affine open (def-sbc-closed-immersion-ideal-sheaf).
3. This ideal sheaf is the sheaf sum: it contains every summand, and each of its
   sections on an affine open is a finite sum of sections of the summands.
   Both inclusions can be checked on the affine basis. This proves quasi-coherence
   and the affine formula, also for empty families.
4. On the finite affine cover of V, choose finitely many generators of each sum
   ideal. Each generator uses finitely many family indices. Their finite union
   gives the required finite subsum globally, by equality on the affine cover.
5. For a family indexed by d >= m, take the maximum of m and the finite set of
   indices. The interval sum lies between the finite subsum and the full sum.
   If the full sum is zero, every summand is zero and N = m works; this is stated
   separately in `noetherian_closed_family_tail`.
6. A map factors through the closed subscheme precisely when it kills its ideals
   (lem-weil-pbc-closed-immersion-lift-ideal-kills-sections). Killing their sum is
   equivalent to killing each summand. Factorizations are unique because closed
   immersions are monomorphisms
   (lem-sfb-noetherian-open-closed-finite-presentation). Vanishing of sections is
   checked on affine charts of the test scheme by the sheaf axiom, without any
   Noetherian or reducedness hypothesis on that scheme.
7. The closed immersion followed by the open immersion is an immersion. The
   principal charts from step 1 pull back to the quotient affine charts from
   step 2. Each quotient of R_f is generated over R by the image of 1/f, so the
   finite chart cover proves finite type (def-weil-finite-type-morphism).
-/
theorem noetherian_closed_family_intersection
    {S V : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (v : V ⟶ S) [IsOpenImmersion v] {L : Type w} (I : L → V.IdealSheafData) :
    ∃ J : V.IdealSheafData,
      J = (⨆ l, I l) ∧
      J.toModules.IsQuasicoherent ∧
      (∀ A : V.affineOpens,
        J.ideal A = ⨆ l, (I l).ideal A) ∧
      (∀ A : V.affineOpens,
        Nonempty (J.toModules.restrict A.2.fromSpec ≅
          tilde (ModuleCat.of Γ(V, A) ↥(⨆ l, (I l).ideal A)))) ∧
      (∃ L₀ : Finset L, J = (⨆ l ∈ L₀, I l)) ∧
      IsClosedImmersion J.subschemeι ∧
      J.subschemeι.ker = J ∧
      (∀ A : V.affineOpens,
        IsPullback (J.subschemeCover.f A) (J.glueDataObjι A) J.subschemeι A.1.ι) ∧
      (∀ (T : Scheme.{u}) (t : T ⟶ V),
        ((∃! a : T ⟶ J.subscheme, a ≫ J.subschemeι = t) ↔
          ∀ l, ∃ a : T ⟶ (I l).subscheme, a ≫ (I l).subschemeι = t) ∧
        ((∃! a : T ⟶ J.subscheme, a ≫ J.subschemeι = t) ↔
          ∀ (l : L) (A : V.affineOpens) (W : T.affineOpens)
            (h : W.1 ≤ t ⁻¹ᵁ A.1),
            (I l).ideal A ≤ RingHom.ker (t.appLE A.1 W.1 h).hom)) ∧
      IsImmersion (J.subschemeι ≫ v) ∧
      LocallyOfFiniteType (J.subschemeι ≫ v) ∧
      QuasiCompact (J.subschemeι ≫ v) ∧
      (∀ B : S.affineOpens,
        ∃ (n : ℕ) (f : Fin n → Γ(S, B)) (A : Fin n → V.affineOpens)
          (hAB : ∀ j, (A j).1 ≤ v ⁻¹ᵁ B.1),
          (∀ j, (A j).1 = v ⁻¹ᵁ S.basicOpen (f j)) ∧
          (∀ j, S.basicOpen (f j) ≤ v.opensRange) ∧
          (⨆ j, S.basicOpen (f j)) = v.opensRange ⊓ B.1 ∧
          (∀ j, @IsLocalization.Away Γ(S, B) _ (f j) Γ(V, A j) _
            (v.appLE B.1 (A j).1 (hAB j)).hom.toAlgebra) ∧
          (⨆ j, (J.subschemeCover.f (A j)).opensRange) =
            (J.subschemeι ≫ v) ⁻¹ᵁ B.1 ∧
          (∀ j, IsPullback (J.subschemeCover.f (A j)) (J.glueDataObjι (A j))
            J.subschemeι (A j).1.ι)) := by
  sorry

/-- For a tail-indexed family the finite subsum can be an initial interval of the
same tail; when the full sum is zero, the bound can be m itself.

Source: the finite-maximum consequence of the finite-generator argument in Stacks
Project, Tag 01Y8, as expanded in step 5 of the DAG proof
(blueprint: lem-sfb-noetherian-closed-family-intersection).

Proof: apply the finite-subsum clause of `noetherian_closed_family_intersection`.
Take N to be the maximum of m and the finitely many selected indices. The interval
sum contains this finite subsum and is contained in the full sum, hence is equal
to it. If the full sum is zero, each ideal in the family is zero, and choose N = m.
-/
theorem noetherian_closed_family_tail
    {S V : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (v : V ⟶ S) [IsOpenImmersion v] (m : ℕ)
    (I : {d : ℕ // m ≤ d} → V.IdealSheafData) :
    ∃ N : ℕ, m ≤ N ∧
      (⨆ d, I d) = (⨆ d : {d : ℕ // m ≤ d ∧ d ≤ N}, I ⟨d.1, d.2.1⟩) ∧
      ((⨆ d, I d) = ⊥ → N = m) := by
  sorry

end AlgebraicGeometry
