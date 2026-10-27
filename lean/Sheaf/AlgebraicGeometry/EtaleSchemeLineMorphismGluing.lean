/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Precoverage
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionAssociativity
import WeilConjectures.AlgebraicGeometry.Descent

/-! # Étale gluing of morphisms of schemes with line modules

Source: Stacks Project, Descent, Tags 023Q and 023T; Spaces Descent, Tag 04W8
(blueprint: lem-trf-etale-scheme-line-morphism-gluing).

The overlap condition is evaluated on all schemes mapping to both charts over `X`.
Taking the scheme `X_i ×_X X_j` recovers the usual overlap equation; pulling that
one equation back gives every test equation. All comparisons are the recorded
canonical tensor-pullback composition comparisons.

## Main declarations

* `lineHomPullToTest`: pull a module map back, normalizing both composite maps.
* `IsLineHomBaseChange`: the equations saying that a local pair is a base change.
* `existsUnique_etaleSchemeLineMorphism`: glue the pair, including its isomorphism clause.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Pull a map between two pulled-back modules to a test scheme, using the canonical
composition comparisons at both ends.
Source: Stacks Project, Sheaves, Tags 0095 and 0096; Descent, Tag 023T
(blueprint: lem-trf-etale-scheme-line-morphism-gluing). -/
noncomputable def lineHomPullToTest {T R X Y : Scheme.{u}}
    (r : T ⟶ R) (f : R ⟶ Y) (p : R ⟶ X) (M : Y.Modules) (L : X.Modules)
    (μ : (tensorPullback f).obj M ⟶ (tensorPullback p).obj L) :
    (tensorPullback (r ≫ f)).obj M ⟶ (tensorPullback (r ≫ p)).obj L :=
  (tensorPullbackCompositionIso r f (r ≫ f) rfl).hom.app M ≫
    (tensorPullback r).map μ ≫
    (tensorPullbackCompositionIso r p (r ≫ p) rfl).inv.app L

/-- The local scheme map has the prescribed `Y` component, and its module map equals
the pullback of the global map under the canonical composition identifications.
When both scheme maps are over the same base and the local map is over its cover chart,
its other fibre-product component is already fixed, so these are exactly base-change
agreement of the pair. Equality transport carries no choice of comparison.
Source: Stacks Project, Descent, Tags 023Q and 023T
(blueprint: lem-trf-etale-scheme-line-morphism-gluing). -/
def IsLineHomBaseChange {X Y X' Y' : Scheme.{u}}
    (p : X' ⟶ X) (q : Y' ⟶ Y) (b : X ⟶ Y) (b' : X' ⟶ Y')
    (M : Y.Modules) (L : X.Modules) (μ : (tensorPullback b).obj M ⟶ L)
    (μ' : (tensorPullback b').obj ((tensorPullback q).obj M) ⟶
      (tensorPullback p).obj L) : Prop :=
  ∃ hb : p ≫ b = b' ≫ q,
    (tensorPullbackCompositionIso p b (p ≫ b) rfl).hom.app M ≫
        (tensorPullback p).map μ =
      eqToHom (congrArg (fun f ↦ (tensorPullback f).obj M) hb) ≫
        (tensorPullbackCompositionIso b' q (b' ≫ q) rfl).hom.app M ≫ μ'

/-- Compatible morphisms of schemes with invertible modules glue uniquely over an
arbitrary jointly surjective étale family. Local isomorphisms give a global isomorphism
of both the scheme and the module. The sigma type records the pair, with the equation
that the scheme map is over `S`; its equality expresses uniqueness of the entire pair.

Source: Stacks Project, Descent, Tag 023Q, `lemma-fpqc-universal-effective-epimorphisms`,
and Tag 023T, `proposition-fpqc-descent-quasi-coherent`; Spaces Descent, Tag 04W8
(blueprint: lem-trf-etale-scheme-line-morphism-gluing).

Proof:
1. The étale cover is fpqc by `lem-weil-pbc-fpqc-finer-than-etale`. Its base changes
   to X and Y are fpqc by `lem-galois-fpqc-covering-base-change`. The fibre-product
   universal property identifies their overlaps with the overlaps over the base cover.
2. Glue `b_i` followed by the projection to Y by
   `lem-weil-pbc-fpqc-representable-descent`. Its uniqueness shows that the resulting b
   is over S. The fibre-product universal property recovers every prescribed b_i;
   the same descent uniqueness proves uniqueness of b.
3. The module b*M is invertible by `lem-weil-pbc-invertible-pullback-invertible`,
   hence quasi-coherent, as is L. Transport each mu_i by the canonical composition
   comparison to a map p_i*(b*M) to p_i*L. Associativity of the comparisons, namely
   `lem-pc-tensor-pullback-composition-associativity`, and their naturality identify
   the overlap equations below with the canonical module descent equations.
   Fullness in `lem-pc-fpqc-descent` supplies mu; faithfulness makes it unique.
4. If the b_i are isomorphisms, their inverses agree on overlaps. Apply the same
   representable descent with X and Y exchanged to glue an inverse c. Uniqueness
   proves both inverse equations, so b is an isomorphism.
5. If the mu_i are also isomorphisms, invert the compatible local module maps in
   step 3. Fullness in `lem-pc-fpqc-descent` glues their inverses, and faithfulness
   proves both inverse equations for mu. No local map is assumed invertible in
   steps 1--3. Empty covers, the empty scheme and zero module maps are included. -/
theorem existsUnique_etaleSchemeLineMorphism
    {S X Y : Scheme.{u}} (a : X ⟶ S) (d : Y ⟶ S)
    (L : X.Modules) (M : Y.Modules) [IsInvertible L] [IsInvertible M]
    {I : Type v} (U : I → S.Etale)
    (hcover : ∀ x : S, ∃ (i : I) (z : (U i).left), (U i).hom z = x)
    (b : ∀ i : I, Limits.pullback a (U i).hom ⟶ Limits.pullback d (U i).hom)
    (hover : ∀ i : I, b i ≫ pullback.snd d (U i).hom = pullback.snd a (U i).hom)
    (μ : ∀ i : I, (tensorPullback (b i)).obj
      ((tensorPullback (pullback.fst d (U i).hom)).obj M) ⟶
        (tensorPullback (pullback.fst a (U i).hom)).obj L)
    (hcompat : ∀ (i j : I) (T : Scheme.{u})
      (r : T ⟶ Limits.pullback a (U i).hom) (s : T ⟶ Limits.pullback a (U j).hom)
      (hp : r ≫ pullback.fst a (U i).hom = s ≫ pullback.fst a (U j).hom),
      ∃ hb : r ≫ (b i ≫ pullback.fst d (U i).hom) =
          s ≫ (b j ≫ pullback.fst d (U j).hom),
        lineHomPullToTest r (b i ≫ pullback.fst d (U i).hom)
            (pullback.fst a (U i).hom) M L
            ((tensorPullbackCompositionIso (b i) (pullback.fst d (U i).hom)
              (b i ≫ pullback.fst d (U i).hom) rfl).hom.app M ≫ μ i) ≫
            eqToHom (congrArg (fun f ↦ (tensorPullback f).obj L) hp) =
          eqToHom (congrArg (fun f ↦ (tensorPullback f).obj M) hb) ≫
            lineHomPullToTest s (b j ≫ pullback.fst d (U j).hom)
              (pullback.fst a (U j).hom) M L
              ((tensorPullbackCompositionIso (b j) (pullback.fst d (U j).hom)
                (b j ≫ pullback.fst d (U j).hom) rfl).hom.app M ≫ μ j)) :
    ∃ B : (Σ f : {f : X ⟶ Y // f ≫ d = a}, (tensorPullback f.val).obj M ⟶ L),
      (∀ i : I, IsLineHomBaseChange
        (pullback.fst a (U i).hom) (pullback.fst d (U i).hom)
        B.1.val (b i) M L B.2 (μ i)) ∧
      (∀ B' : (Σ f : {f : X ⟶ Y // f ≫ d = a}, (tensorPullback f.val).obj M ⟶ L),
        (∀ i : I, IsLineHomBaseChange
          (pullback.fst a (U i).hom) (pullback.fst d (U i).hom)
          B'.1.val (b i) M L B'.2 (μ i)) → B' = B) ∧
      ((∀ i : I, IsIso (b i) ∧ IsIso (μ i)) → IsIso B.1.val ∧ IsIso B.2) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
