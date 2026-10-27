/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.SmoothAtlasModuleDatum
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Quasi-coherent module descent along an arbitrary smooth scheme atlas

Source: Stacks Project, stacks-sheaves.tex, Tag 06WT (proposition-quasi-coherent),
Tag 06WK; algebraic.tex, Tag 04T5 (lemma-stack-presentation)
(blueprint: lem-sfb-smooth-atlas-module-descent).

The relation and triple relation are expressed on their scheme tests. This retains
algebraic-space relations without requiring scheme representatives. Section coordinates
fix both the functor and the orientation delta = inverse(c2) c1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- The actual scalar identification over a scheme test of the atlas.
Source: Stacks 06WT, 06WK (blueprint: lem-sfb-smooth-atlas-module-descent). -/
def smoothAtlasTestScalar {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    (hC : IsFibredInGroupoids X) {U : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) X) {T : Over S} (f : T ⟶ U) :
    (atlasFppfRings.{u, max v w} U.left).obj.obj (op (Over.mk f.left)) →+*
      (moduliModuleRings X hC).obj.obj (op (atlasTestObject a f)) :=
  (Scheme.Γ.map (atlasTestBaseIso a f).hom.op).hom.ulift

/-- Restriction along any specified smooth surjective scheme atlas is an equivalence
onto quasi-coherent modules with their normalized relation isomorphism and cocycle.
Essential surjectivity supplies every prescribed pair with its compatible isomorphism;
full faithfulness says all compatible module maps descend uniquely.

Source: Stacks Project, stacks-sheaves.tex, Tag 06WT (proposition-quasi-coherent),
Tag 06WK; algebraic.tex, Tags 04T5 and 04WY
(blueprint: lem-sfb-smooth-atlas-module-descent).

Proof:
1. By lem-sfb-stack-chartwise-smooth-etale-calculus the atlas is flat and locally
finitely presented. Clause (2) of lem-sfb-fppf-groupoid-stack-presentations gives its
self-relation groupoid and the canonical equivalence [U/R] to X commuting with the atlas.
The relation is an algebraic space, and is not replaced by a scheme.
2. Invert the groupoid-module datum of lem-sfb-space-groupoid-module-descent. Its
alpha goes from target pullback to source pullback; delta goes the other way.
Taking inverses translates alpha's composition law into delta23 delta12 = delta13.
It translates the morphism rule too, and inversion again is the inverse functor.
3. Precompose modules with the equivalence [U/R] to X and its inverse. Underlying
scheme objects, fppf covers and regular-function rings agree. Thus these operations
preserve sheaves and their local free presentations, and unit and counit give the
inverse equivalences on the full quasi-coherent subcategories and every module map.
4. Apply lem-sfb-space-groupoid-module-descent and compose the preceding equivalences.
The canonical two-arrow gives alpha = inverse(c1) c2; inversion gives the required
delta = inverse(c2) c1. By lem-sfb-stack-quasi-coherent-scheme-restriction the tensor
comparisons are natural in F and coherent with composition. On scheme tests of R
and R2 these are precisely sections_delta, naturality, identity and cocycle above.
The associated-module adjunction unit identifies restriction on the small etale site;
the canonical regular-function transport gives sections_smul. Every module map is
restricted to U, giving sections_map.
5. Essential surjectivity gives a descended F and an isomorphism to each datum.
Full faithfulness gives existence and uniqueness for every compatible module map.
No quasi-compactness, quasi-separatedness, Noetherian, finiteness or DM assumption
has entered. Scheme tests include the empty scheme and repeated relation points. -/
theorem smooth_atlas_module_descent {S : Scheme.{u}}
    (X : BasedCategory.{v, w} (Over S)) (hX : IsAlgebraicModuliStack X)
    (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) X)
    (ha : IsSmoothModuliAtlas X U a) :
    ∃ e : ModuliQCoh X hX.1.1 ≌ SmoothAtlasModuleDatum a,
    ∃ sections : ∀ (F : ModuliQCoh X hX.1.1) (T : Over S) (f : T ⟶ U),
      ((atlasAssociated.{u, max v w} U.left).obj
        (e.functor.obj F).module.obj).val.obj (op (Over.mk f.left)) ≃+
          F.obj.val.obj (op (atlasTestObject a f)),
    (∀ F : ModuliQCoh X hX.1.1,
      IsIso ((atlasAssociatedAdjunction.{u, max v w} U.left).unit.app
        (e.functor.obj F).module.obj)) ∧
    (∀ (F : ModuliQCoh X hX.1.1) (T : Over S) (f : T ⟶ U)
      (r : (atlasFppfRings.{u, max v w} U.left).obj.obj (op (Over.mk f.left)))
      (s : ((atlasAssociated.{u, max v w} U.left).obj
        (e.functor.obj F).module.obj).val.obj (op (Over.mk f.left))),
      sections F T f (r • s) = smoothAtlasTestScalar hX.1.1 a f r • sections F T f s) ∧
    (∀ (F : ModuliQCoh X hX.1.1) (T' T : Over S) (h : T' ⟶ T) (f : T ⟶ U)
      (s : ((atlasAssociated.{u, max v w} U.left).obj
        (e.functor.obj F).module.obj).val.obj (op (Over.mk f.left))),
      sections F T' (h ≫ f)
        (((atlasAssociated.{u, max v w} U.left).obj (e.functor.obj F).module.obj).val.map
          (atlasSchemeTestArrow h f).op s) =
        F.obj.val.map (atlasTestArrow a h f).op (sections F T f s)) ∧
    (∀ (F G : ModuliQCoh X hX.1.1) (b : F ⟶ G) (T : Over S) (f : T ⟶ U)
      (s : ((atlasAssociated.{u, max v w} U.left).obj
        (e.functor.obj F).module.obj).val.obj (op (Over.mk f.left))),
      sections G T f
        (((atlasAssociated.{u, max v w} U.left).map (e.functor.map b).val).val.app
          (op (Over.mk f.left)) s) =
        b.hom.val.app (op (atlasTestObject a f)) (sections F T f s)) ∧
    (∀ (F : ModuliQCoh X hX.1.1) (T : Over S) (f g : T ⟶ U)
      (q : AtlasRelation a f g)
      (s : ((atlasAssociated.{u, max v w} U.left).obj
        (e.functor.obj F).module.obj).val.obj (op (Over.mk f.left))),
      sections F T g ((e.functor.obj F).delta f g q s) =
        F.obj.val.map q.val.hom.op (sections F T f s)) := by
  sorry

end CategoryTheory
