/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Separation.Profinite
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Relative profinite test schemes

Source: RefactorInstruction, Section 4, equations finite-XI and XS, Lemma lem:XS;
ModuleObject/Basic.lean, module docstring, lines 38–52; Stacks Project, Tag 097D
(blueprint: lem-weil-pbc-profinite-test-object-functor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The relative profinite test functor is independent of finite-quotient presentation,
preserves finite limits and finite disjoint unions, and takes finite jointly surjective
families to fpqc coverings. Its restriction to finite sets is naturally the coproduct of
copies of `X` over `X`; for every cofiltered finite-quotient presentation, the image cone
is limiting over `X`. These two clauses identify its value with the required relative
inverse limit, with canonical comparison isomorphisms respecting all projections.
The functor already supplies weakly etale structure maps, identity and composition laws.
Over `Spec ℤ` the last natural isomorphism identifies it with `Spec LC(-, ℤ)`;
`profiniteToScheme` sends a continuous map to the spectrum of precomposition.

Source: RefactorInstruction, Section 4, equations finite-XI and XS, Lemma lem:XS;
ModuleObject/Basic.lean, lines 38–52; Stacks Project, Tag 097D
(blueprint: lem-weil-pbc-profinite-test-object-functor).

Proof plan (the ten steps of the node):
1. Use `lem-weil-pbc-profinite-limit-function-factorization` and
   `lem-weil-pbc-profinite-clopen-basis` to express locally constant functions as the
   filtered colimit over finite quotients, also over all finite clopen partitions.
2. Form finite coproducts over the partitions, adjoining `X` as a least stage.
   `lem-weil-pbc-finite-affine-coproduct-spectrum`,
   `lem-weil-pbc-morphism-affine-schemes-affine`, and `pqf-lem-affine-local-target`
   make the transitions affine. `lem-weil-pbc-limit-affine-transition-core` gives the limit.
3. Use `lem-weil-pbc-limit-cone-affine-projections-opens` and
   `lem-weil-pbc-spec-small-colimit-limit` to compute its restriction to `Spec R` as
   `Spec LC(S,R)`. `lem-weil-pbc-scheme-morphism-gluing` proves the limit property for
   every finite-quotient presentation, without any compactness assumption on `X`.
4. Precomposition and `def-weil-affine-spectrum` give the local maps; glue them by
   `lem-weil-pbc-scheme-morphism-gluing`. The ring-map identities give functoriality
   and the functorial identification over `Spec ℤ`.
5. Compute the tensor product formulas using finite clopen partitions, compactness
   (`lem-weil-pbc-tychonoff-product-quasi-compact`) and the clopen basis. Apply
   `lem-weil-pbc-spec-small-colimit-limit` and glue to obtain products over `X`.
6. Extend locally constant functions from a closed subspace using the clopen basis.
   For an equalizer, characteristic functions generate the kernel of restriction.
   The spectrum theorem and gluing give equalizers; these and products give finite limits.
7. `lem-weil-pbc-locally-constant-prime-spectrum` identifies points as `(s,p)`.
   `lem-weil-pbc-affine-open-stalk-localization` identifies stalks with `R_p` by
   evaluation, with inverse given by constants. Hence the induced stalk maps are flat
   (`def-weil-flat-morphism`).
8. Apply the finite-limit formula to the diagonal. Step 7 makes it flat, so the
   maps are weakly etale (`def-weil-weakly-etale-morphism`) and lie in the recorded
   small pro-etale site (`def-weil-pbc-proetale-site`).
9. Finite jointly surjective families remain jointly surjective on the points `(s,p)`.
   Their arrows are affine (`pqf-def-affine-morphism`, `pqf-lem-affine-local-target`,
   and `lem-weil-pbc-morphism-affine-schemes-affine`) and flat, so their affine
   preimages verify `def-weil-pbc-fpqc-covering`, including the empty family.
10. Restriction gives `LC(S ⊔ T,R) = LC(S,R) × LC(T,R)`.
    Use `lem-weil-pbc-finite-affine-coproduct-spectrum` and gluing for disjoint unions.
    The empty space gives the zero ring and the empty scheme. -/
theorem profinite_test_object_functor (X : Scheme.{u}) :
    PreservesFiniteLimits (profiniteToProEtOf X) ∧
    (∀ (A : Type u) [Finite A],
      PreservesColimitsOfShape (Discrete A) (profiniteToProEtOf X)) ∧
    Nonempty
      (FintypeCat.toProfinite ⋙ profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ≅
        forget FintypeCat.{u} ⋙ sigmaConst.obj (Over.mk (𝟙 X))) ∧
    (∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
      (D : I ⥤ FintypeCat.{u}) (c : Cone (D ⋙ FintypeCat.toProfinite)),
      IsLimit c → (∀ i : I, Function.Surjective (c.π.app i)) →
      Nonempty (IsLimit
        ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X).mapCone c))) ∧
    (∀ (A : Type u) [Finite A] (S : A → Profinite.{u}) (T : Profinite.{u})
      (f : ∀ a : A, S a ⟶ T),
      (∀ t : T, ∃ (a : A) (s : S a), f a s = t) →
      Presieve.ofArrows
        (fun a ↦ (profiniteToProEtOf X |>.obj (S a)).left)
        (fun a ↦ (profiniteToProEtOf X |>.map (f a)).left) ∈
        Scheme.fpqcPrecoverage ((profiniteToProEtOf X).obj T).left) ∧
    Nonempty
      (profiniteToProEtOf specZ.{u} ⋙ Scheme.ProEt.forget specZ ⋙ Over.forget specZ ≅
        profiniteToScheme.{u}) := by
  sorry

end AlgebraicGeometry.ProEtale
