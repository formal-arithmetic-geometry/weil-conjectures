/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSchemeActionTorsorGroupoid
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription

/-! # Recognizing a stack from a finite action-groupoid cover

Source: Stacks Project, algebraic.tex, Tags 04T4 and 04T5;
examples-stacks.tex, Tag 04WM, with the relation and étale local lifting
hypotheses explicit (blueprint: lem-sfb-action-groupoid-quotient-criterion).

`G`, its coprojections, and their coproduct universal property present the constant
scheme `H_S`. The multiplication equations specify its constant group structure.
The based functor `A` bundles the atlas map and the coherent action isomorphisms,
including their pullback compatibility. Fibrewise full faithfulness is the given
identification of the relation with the action groupoid, without taking isomorphism
classes. The conclusion includes the extension, its inverse over the base, and the
unique 2-isomorphism compatible with its specified atlas-and-arrows comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SchemeAction

/-- A locally surjective atlas whose entire relation is the finite action groupoid
identifies the stack with the groupoid of étale locally trivial scheme torsors and
equivariant maps. `incl` is a coproduct cocone of copies of the terminal `S`-scheme;
its unit and multiplication equations say that `G` is precisely `H_S`.

Source: Stacks Project, Tags 04T4, 04T5 (presentation), 04WM (torsor comparison),
02ZP, 0436 (stackification), and 046N (local essential surjectivity)
(blueprint: lem-sfb-action-groupoid-quotient-criterion).

Proof:
1. The based functor A gives the atlas map and the arrows alpha. Its functor laws
are alpha(1)=1 and alpha(g,h u) alpha(h,u)=alpha(gh,u). Nonconstant sections of
H_S are treated on their clopen constant components and glued using the target's
isomorphism sheaves. Fibrewise full faithfulness identifies the whole arrow
presheaf with the target isomorphism sheaf.
2. Apply lem-sfb-groupoid-stackification-local-description to the action groupoid.
Extend A to F on its étale stackification Q. The arrow-sheafification description
and step 1 identify isomorphisms between atlas objects.
3. Locally represent two arbitrary objects of Q by atlas objects, using the same
local-description lemma. Lift arrows locally, compare them on overlaps by local
injectivity, and glue by the isomorphism-sheaf axiom. Thus F is fully faithful.
The lifting hypothesis gives local essential surjectivity, so
lem-sfb-stack-fully-faithful-local-equivalence makes F an equivalence.
4. By lem-sfb-finite-constant-torsor-map-etale-stack the scheme-torsor category is
an étale stack over this arbitrary S. Extend the specified trivial-torsor functor
to E on Q by the local-description lemma. Its arrow h is R(h inverse).
5. An equivariant isomorphism of trivial torsors is right translation by its
value at 1; preserving their orbit maps forces that value to be h inverse for
exactly an action-groupoid arrow h. Thus E is fully faithful on atlas objects,
and step 3's gluing argument makes it fully faithful everywhere. A local
trivialization of any torsor identifies its equivariant map with the orbit map
of its value at 1. The local-equivalence criterion makes E an equivalence.
6. Compose an inverse of E with F. The two extension comparisons give epsilon
on the entire action groupoid, so they specify both a and alpha. For any other
extension, trivialize each torsor étale locally and use the comparisons to define
the compatible isomorphism there. Changes of trivialization are R(h inverse),
so compatibility on arrows makes these maps agree on overlaps. The target's
isomorphism sheaf glues them uniquely. Trivializing both ends of an arbitrary
arrow proves naturality. This proves the unique compatible 2-isomorphism. -/
theorem actionGroupoid_quotient_criterion
    {S : Scheme.{u}} (H : Type u) [Group H] [Finite H]
    (G U : Over S) [GrpObj G] [ModObj G U]
    (incl : H → (Over.mk (𝟙 S) ⟶ G))
    (hincl : IsColimit (Cofan.mk G incl))
    (hincl_one : incl 1 = 1) (hincl_mul : ∀ g h : H, incl (g * h) = incl g * incl h)
    (Z : BasedCategory.{v, w} (Over S)) (hZ : IsModuliStack Z)
    (A : BasedFunctor (actionGroupoid G U) Z)
    (hrel : ∀ T : Over S,
      (moduliFiberMap A T).Full ∧ (moduliFiberMap A T).Faithful)
    (hlift : ∀ z : Z.obj,
      ∃ R : Sieve (Z.p.obj z), R ∈ (Scheme.etaleTopology.over S) (Z.p.obj z) ∧
        ∀ (W : Over S) (b : W ⟶ Z.p.obj z), R b →
          ∃ (x : (actionGroupoid G U).obj) (r : A.obj x ⟶ z), Z.p.IsHomLift b r) :
    ∃ C : BasedFunctor (etaleTorsorGroupoid G U) Z,
      (∃ D : BasedFunctor Z (etaleTorsorGroupoid G U),
        Nonempty (C.comp D ≅ BasedFunctor.id (etaleTorsorGroupoid G U)) ∧
        Nonempty (D.comp C ≅ BasedFunctor.id Z)) ∧
      ∃ ε : (etaleTrivialTorsorFunctor G U).comp C ≅ A,
        ∀ (C' : BasedFunctor (etaleTorsorGroupoid G U) Z)
          (ε' : (etaleTrivialTorsorFunctor G U).comp C' ≅ A),
          ∃! eComp : C ≅ C',
            BasedCategory.whiskerLeft (etaleTrivialTorsorFunctor G U) eComp.hom ≫ ε'.hom =
              ε.hom := by
  sorry

end AlgebraicGeometry.SchemeAction
