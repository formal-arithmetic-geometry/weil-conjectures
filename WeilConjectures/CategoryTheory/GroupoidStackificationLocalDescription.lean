/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Groupoid

/-! # Stackification of fibred groupoids

Source: Stacks Project, stacks.tex, Tags 02ZP and 0436
(blueprint: lem-sfb-groupoid-stackification-local-description).

A fibred groupoid with coherent choices of pullback is represented by a pseudofunctor
on the locally discrete opposite base category. Its fibres are groupoids, without
passing to isomorphism classes. `StrongTrans` expresses a pullback-compatible functor;
isomorphisms between strong transformations are invertible modifications.
The same statement includes strict presheaves of groupoids, whose associated fibred
category is the CoGrothendieck construction. All sizes lie in the chosen larger universe.
-/

@[expose] public section

set_option autoImplicit false

universe w

open CategoryTheory Opposite
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor

set_option backward.isDefEq.respectTransparency false in
/-- A fibred groupoid admits a stackification with sheafified isomorphisms, local
representatives, and extension of functors into stacks.

Source: Stacks Project, stacks.tex, Tag 02ZP, clauses (1) and (2), and Tag 0436
(blueprint: lem-sfb-groupoid-stackification-local-description).

The groupoid hypothesis makes `presheafHom` the presheaf of isomorphisms. The
comparison with its sheafification is natural on the whole slice and takes the
sheafification unit to the map induced by `i`, conjugated by its pullback comparisons.
The stack axioms are Mathlib's `IsStack`: morphism sheaves and effective object descent
for all covering sieves, including empty covering sieves.

Proof: first sheafify the morphism presheaves, retaining all fibre objects, as in
`lem-sfb-groupoid-morphism-sheafification`. Composition, identities, inverses and
pullback extend by sheafification, producing a prestack Q and an objectwise identity
functor q. Apply `lem-sfb-prestack-sieve-descent-completion` to Q. Its objects are
cartesian sections on covering sieves; arrows are compatible local arrows modulo
covering refinement. The resulting completion A is a stack and its embedding e is
fibrewise fully faithful. Put i = e q. Full faithfulness of e identifies A's morphism
sheaves between images with Q's sheafified morphisms, compatibly with the unit.
Every completion object restricts along its defining covering sieve to e of one of
its section objects, hence to i of an original object because q fixes objects.
For F into a stack Y, extend first across q to G on Q. For each completion object,
glue G of its cartesian section in Y, choosing a realization with its descent
identifications. A completion arrow gives compatible local arrows between these
realizations; the morphism sheaf axiom glues them uniquely. Independence of refinement,
identities and composition follow after restriction to a common covering sieve.
Pulling back a realization and realizing the pulled-back section give uniquely
isomorphic realizations of the same descent datum. These comparisons satisfy the
identity and composition coherences by the same local uniqueness, and define a
strong transformation H. On maximal-sieve sections the chosen realization is
naturally isomorphic to G of the original object, giving H i isomorphic to F.
For a presheaf of groupoids, the associated total category has objects (T,u) and
arrows over h given by v -> P(h)(u); identity fibre arrows provide cartesian lifts,
so exactly the same construction applies. -/
theorem exists_groupoid_stackification_local_description
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    (hP : ∀ T : C, IsGroupoid (P.obj (.mk (op T)))) :
    ∃ A : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w},
      (∀ T : C, IsGroupoid (A.obj (.mk (op T)))) ∧ A.IsStack J ∧
      ∃ i : StrongTrans P A,
        (∀ (T : C) (u v : P.obj (.mk (op T))),
          ∃ e : sheafify (J.over T) (P.presheafHom u v) ≅
              A.presheafHom ((i.app (.mk (op T))).toFunctor.obj u)
                ((i.app (.mk (op T))).toFunctor.obj v),
            ∀ (V : Over T) (φ : (P.presheafHom u v).obj (op V)),
              e.hom.app (op V) ((toSheafify (J.over T) (P.presheafHom u v)).app (op V) φ) =
                (i.naturality V.hom.op.toLoc).inv.toNatTrans.app u ≫
                  (i.app (.mk (op V.left))).toFunctor.map φ ≫
                    (i.naturality V.hom.op.toLoc).hom.toNatTrans.app v) ∧
        (∀ (T : C) (a : A.obj (.mk (op T))),
          ∃ R : Sieve T, R ∈ J T ∧
            ∀ (V : C) (f : V ⟶ T), R f →
              ∃ u : P.obj (.mk (op V)),
                Nonempty ((i.app (.mk (op V))).toFunctor.obj u ≅
                  (A.map f.op.toLoc).toFunctor.obj a)) ∧
        (∀ (Y : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}),
          (∀ T : C, IsGroupoid (Y.obj (.mk (op T)))) → Y.IsStack J →
          ∀ F : StrongTrans P Y, ∃ H : StrongTrans A Y,
            Nonempty (@CategoryTheory.Iso (StrongTrans P Y)
              (StrongTrans.homCategory (F := P) (G := Y)) (StrongTrans.vcomp i H) F)) := by
  sorry

end CategoryTheory.Pseudofunctor
