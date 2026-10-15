/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Sites.Subcanonical
import Sheaf.AlgebraicGeometry.FiniteCoproductLfpQcqs

/-!
# Finite disjoint unions in the pro-etale site

Source: Stacks Project, Tags 0F4P and 0DB1
(blueprint: lem-weil-pbc-proetale-finite-coproduct-evaluation).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Finite qcqs families admit a qcqs disjoint union in the pro-etale site, affine if
all summands are affine. Its representable sheaf is the coproduct of the representable
summands, and restriction gives a bijection on sections natural in the sheaf.
Here `uliftYoneda` places representables in the same universe as the sheaves of sets.
The colimit witness asserts existence in sheaves; `hc.desc` is the canonical comparison
from any chosen coproduct. Empty families give the empty scheme and singleton sections.

Source: Stacks Project, Tag 0F4P, proof of `lemma-weakly-contractible-cover`, and
Tag 0DB1, `remark-take-unions-hypercovering-X`, hypotheses (a)-(c)
(blueprint: lem-weil-pbc-proetale-finite-coproduct-evaluation).

Proof:
1. Construct the scheme coproduct and its clopen coprojections using
   lem-weil-pbc-scheme-coproduct-family. Apply lem-weil-pbc-finite-coproduct-lfp-qcqs
   for qcqs and lem-weil-pbc-finite-affine-coproduct-spectrum for affineness.
   The empty coproduct is the spectrum of the zero ring, hence empty.
2. The structural morphism is weakly etale: flatness and flatness of its diagonal
   are checked on each open summand using def-weil-weakly-etale-morphism and
   def-weil-flat-morphism. Finite unions respect def-weil-size-convention.
3. The summand inclusions cover in def-weil-pbc-proetale-site. For an affine open
   of the union, its intersections with summands are clopen and quasi-compact;
   finite affine covers of these intersections verify the covering criterion.
   The empty family covers the empty scheme, so its sections form a singleton.
   Apply the sheaf equalizer axiom of def-weil-pbc-sites-and-cohomology: distinct
   summands have empty overlaps, and self-overlaps give identity restrictions.
   Every tuple therefore glues uniquely. Naturality of a sheaf morphism on each
   coprojection proves naturality of this bijection.
4. By lem-weil-pbc-proetale-subcanonical the representables are sheaves.
   Use lem-galois-yoneda-hom-bijection to identify maps out of each representable
   with sections. Step 3 gives exactly the coproduct universal property of
   def-weil-pbc-category-colimit. The universal maps in both directions between
   two such coproducts are inverse since they agree on all coprojections. -/
theorem finite_coproduct_evaluation (X : Scheme.{u}) (I : Type v) [Finite I]
    (V : I → X.ProEt) (hqc : ∀ i, CompactSpace (V i).left)
    (hqs : ∀ i, QuasiSeparatedSpace (V i).left) :
    ∃ (W : X.ProEt) (ι : ∀ i, V i ⟶ W)
      (e : (∐ fun i ↦ (V i).left) ≅ W.left),
      (∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.hom = (ι i).left) ∧
      CompactSpace W.left ∧ QuasiSeparatedSpace W.left ∧
      ((∀ i, IsAffine (V i).left) → IsAffine W.left) ∧
      Nonempty (IsColimit (Cofan.mk ((topology X).uliftYoneda.{max (u + 1) w}.obj W)
        (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.map (ι i)))) ∧
      (∀ (c : Cofan (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.obj (V i)))
        (hc : IsColimit c),
        IsIso (hc.desc (Cofan.mk ((topology X).uliftYoneda.{max (u + 1) w}.obj W)
          (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.map (ι i))))) ∧
      (∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
        Function.Bijective (fun s : F.obj.obj (op W) ↦
          fun i ↦ F.obj.map (ι i).op s)) ∧
      (∀ (F G : Sheaf (topology X) (Type (max (u + 1) w))) (η : F ⟶ G)
        (s : F.obj.obj (op W)) (i : I),
        G.obj.map (ι i).op (η.hom.app (op W) s) =
          η.hom.app (op (V i)) (F.obj.map (ι i).op s)) ∧
      (IsEmpty I → IsEmpty W.left ∧
        ∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
          Nonempty (Unique (F.obj.obj (op W)))) := sorry

end AlgebraicGeometry.Scheme.ProEt
