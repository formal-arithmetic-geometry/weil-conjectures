module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # Flatness at a stage of a directed colimit

Source: literature/stacks-project/algebra.tex; literature/stacks-project/limits.tex,
Lemma Tags 02JO and 04AI (blueprint: lem-weil-pbc-colimit-flat-ring-map).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w x

namespace RingHom

/-- Flatness of a finitely presented algebra map descends to a stage of a directed
colimit of base rings (Stacks, Tags 02JO and 04AI).
(blueprint: lem-weil-pbc-colimit-flat-ring-map)

Proof (the nine steps of the node, following 02JO (1), (3), with M = S):
1. Restrict to stages above the initial stage. The elementwise base-change
   colimit lemma (`lem-weil-pbc-directed-colimit-base-change-elementwise`) and
   the module colimit criterion (`lem-weil-pbc-filtered-colimit-modules-criterion`)
   identify the colimits of the tensor products with B and C. Tensor associativity
   and `lem-weil-pbc-finite-presentation-base-change-composition` give finite
   presentation at every stage and the base-change isomorphisms between stages.
2. Apply `lem-weil-pbc-limit-finite-presentation` to B → C. Its finite type
   integer-algebra models P → Q are Noetherian and finitely presented by
   `lem-weil-pbc-finite-type-algebra-noetherian` and
   `lem-weil-pbc-finite-type-noetherian-finite-presentation`.
3. The flat loci in Spec Q are open by `lem-weil-pbc-openness-of-flatness`.
   They persist under transition maps: localize the base-change tensor product
   (`lem-weil-pbc-localization-tensor-over-base`), use flat module base change,
   then localization flatness and composition of flat ring maps.
4. At every prime of C, localize the models using
   `lem-weil-pbc-filtered-colimit-localization-at-prime`. The local Noetherian
   system satisfies `lem-weil-pbc-colimit-eventually-flat`; its colimit is flat
   by `lem-weil-pbc-flat-local-ring-maps`. Flatness over the localized base is
   flatness over the base by `lem-weil-pbc-flat-over-localization`, giving a
   stage's flat locus containing this prime, and all later stages by step 3.
5. Pull these flat loci back to Spec C. They form an increasing open cover.
   Quasi-compactness (`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`)
   gives one stage whose flat locus pulls back to all of Spec C.
6. The ideal defining its complement generates the unit ideal in C. Lift
   finitely many coefficients using `lem-weil-pbc-filtered-colimit-algebras-elementwise`
   and the resulting unit relation using `lem-weil-pbc-filtered-colimit-rings-zero`.
   At a later stage the complement is empty, by persistence from step 3.
7. The resulting Noetherian model P' → Q' is flat by
   `lem-weil-pbc-flat-map-local-criterion` and flatness over localization.
   Its base change to B is C by `lem-weil-pbc-limit-finite-presentation`.
8. Factor P' → B and Q' → C through stages using
   `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`.
   The comparison Q' ⊗ B_i → C_i becomes an isomorphism in the colimit.
   Descend its inverse and the two inverse identities using clauses (2), (3)
   of `lem-weil-pbc-colimit-category-fp-algebras`, obtaining a stage where
   C_i is the base change of Q' over P'.
9. Flatness of this stage, and all later stages, follows from
   `lem-weil-pbc-flat-module-base-change` and the isomorphisms of steps 1, 8.
-/
theorem exists_eventually_flat_of_colimit_flat
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I)
    (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (hfp : φ₀.toRingHom.FinitePresentation)
    (hflat :
      letI := (colimit.ι F i₀).hom.toAlgebra
      (Algebra.TensorProduct.map
        (R := ((F.obj i₀ : CommRingCat) : Type v))
        (S := ((colimit F : CommRingCat) : Type v))
        (A := ((colimit F : CommRingCat) : Type v)) (B := B₀)
        (C := ((colimit F : CommRingCat) : Type v)) (D := C₀)
        (Algebra.ofId ((colimit F : CommRingCat) : Type v)
          ((colimit F : CommRingCat) : Type v)) φ₀).toRingHom.Flat) :
    ∃ i₁ : I, ∃ h₀ : i₀ ≤ i₁, ∀ i : I, ∀ hi : i₁ ≤ i,
      letI := (F.map (homOfLE (h₀.trans hi))).hom.toAlgebra
      (Algebra.TensorProduct.map
        (R := ((F.obj i₀ : CommRingCat) : Type v)) (S := ((F.obj i : CommRingCat) : Type v))
        (A := ((F.obj i : CommRingCat) : Type v)) (B := B₀)
        (C := ((F.obj i : CommRingCat) : Type v)) (D := C₀)
        (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom.Flat := by
  sorry

end RingHom
