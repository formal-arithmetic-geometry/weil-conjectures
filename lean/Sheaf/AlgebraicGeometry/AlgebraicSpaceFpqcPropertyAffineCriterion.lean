/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Affine-test criterion for fpqc locality of algebraic-space morphism properties

Source: Stacks Project, Spaces Descent, Tag 041J; Topologies on Algebraic Spaces,
Tag 03MQ (blueprint: lem-sfb-space-fpqc-property-affine-criterion).

Finite coproduct closure includes the empty cofan. The fpqc covering condition is
expanded as flatness and finite affine refinements, without a nonempty-index assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An isomorphism-invariant property closed under finite sheaf coproducts, detected
by affine scheme tests, and descending along flat surjections of affine schemes is
local on the target for every fpqc family.
Source: Stacks, Spaces Descent, Tag 041J; covering definition: Tag 03MQ
(blueprint: lem-sfb-space-fpqc-property-affine-criterion).

Proof:
1. Hypothesis (2) implies arbitrary base-change stability: for each affine T → W → Y,
   the iterated sheaf pullback (X ×_Y W) ×_W T is X ×_Y T. On sections, forget the
   redundant W-coordinate; the inverse inserts the image of the T-coordinate.
   These inverse maps commute with projection. Apply (2) and isomorphism invariance.
   Algebraicity of the pullbacks is lem-trf-space-fibre-products-etale-covers.
2. For the converse fix an affine Z → Y. The fpqc refinement gives finitely many
   affine Z_j → Z, flat and jointly surjective, factoring through Y_i(j).
   Step 1 applied to the local hypotheses gives P(X ×_Y Z_j → Z_j).
3. Form Z' = ∐ Z_j using lem-weil-pbc-scheme-coproduct-family. By
   lem-weil-pbc-finite-affine-coproduct-spectrum it is Spec(∏ Γ(Z_j)), hence affine.
   Its map to Z is flat since on each open summand its local maps are the flat
   maps for Z_j → Z (def-weil-open-immersion and def-weil-flat-morphism).
   It is surjective by joint surjectivity. For no summands, Z is empty as well.
4. By lem-trf-fppf-sheaf-coproduct-partition the scheme coproduct also represents
   the sheaf coproduct: sections are clopen partitions and maps on each part.
   By lem-trf-set-sheaf-finite-extensivity, X ×_Y Z' → Z' is the coproduct of
   X ×_Y Z_j → Z_j. The isomorphism commutes with the projections, summandwise.
5. Apply (1), including the empty cofan, to obtain P over Z'. Apply (3) to the
   flat surjective affine map Z' → Z, using pullback associativity as in step 1.
   This gives P over every affine Z → Y, and (2) gives P(f). The forward
   implication follows from step 1. The argument also covers an empty family. -/
theorem fpqc_property_affine_criterion {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) [P.RespectsIso]
    (hcoprod : ∀ (J : Type u) [Finite J] (Xj Yj : J → AlgebraicSpace S)
      (fj : ∀ j : J, Xj j ⟶ Yj j) (X Y : AlgebraicSpace S)
      (a : ∀ j : J, Xj j ⟶ X) (b : ∀ j : J, Yj j ⟶ Y) (q : X ⟶ Y),
      IsColimit (Cofan.mk X.obj (fun j : J ↦ (a j).hom)) →
      IsColimit (Cofan.mk Y.obj (fun j : J ↦ (b j).hom)) →
      (∀ j : J, a j ≫ q = fj j ≫ b j) → (∀ j : J, P (fj j)) → P q)
    (haffine : ∀ (X Y : AlgebraicSpace S) (f : X ⟶ Y),
      P f ↔ ∀ (Z : Over S) [IsAffine Z.left] (g : schemeSpace Z ⟶ Y),
        P (enlargedFibreProductFst g f))
    (hdesc : ∀ (Z Z' : Over S) [IsAffine Z.left] [IsAffine Z'.left]
      (g : Z' ⟶ Z), Flat g.left → Surjective g.left →
      ∀ (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Z),
        P (enlargedFibreProductFst
          (ObjectProperty.homMk ⟨yoneda.map g⟩ : schemeSpace Z' ⟶ schemeSpace Z) f) →
        P f)
    {I : Type w} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (Yi : I → AlgebraicSpace S) (g : ∀ i : I, Yi i ⟶ Y)
    (hflat : ∀ i : I, MapIsFlat (g i))
    (hrefine : ∀ (T : Over S) [IsAffine T.left] (a : schemeSpace T ⟶ Y),
      ∃ (n : ℕ) (Tj : Fin n → Over S) (q : ∀ j : Fin n, Tj j ⟶ T)
        (k : Fin n → I) (b : ∀ j : Fin n, schemeSpace (Tj j) ⟶ Yi (k j)),
        (∀ j : Fin n, IsAffine (Tj j).left) ∧
        (∀ j : Fin n, Flat (q j).left) ∧
        (∀ t : T.left, ∃ (j : Fin n) (s : (Tj j).left), (q j).left s = t) ∧
        (∀ j : Fin n, b j ≫ g (k j) =
          (ObjectProperty.homMk ⟨yoneda.map (q j)⟩ :
            schemeSpace (Tj j) ⟶ schemeSpace T) ≫ a)) :
    P f ↔ ∀ i : I, P (enlargedFibreProductFst (g i) f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
