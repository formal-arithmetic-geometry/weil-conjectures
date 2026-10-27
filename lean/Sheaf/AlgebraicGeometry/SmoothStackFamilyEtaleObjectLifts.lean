/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.SmoothModuliMap
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Étale-local object lifts through a smooth stack covering family

Source: Stacks, stacks-cohomology.tex, Tags 075Y (proof, first paragraph) and 0764
(proof (3)); stacks-sheaves.tex, Tag 06XH(2); spaces-topologies.tex, Tag 0CFV
(blueprint: lem-sfb-smooth-stack-family-etale-object-lifts).

The smoothness hypothesis uses the landed `CategoryTheory.IsSmoothModuliMap` definition
owned by def-sfb-smooth-moduli-map; this module introduces no smoothness predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Every scheme-valued object lifts étale locally through a jointly surjective smooth
family of algebraic stacks, including nonrepresentable family maps.
Source: Stacks 075Y, proof first paragraph; 0764, proof (3); 06XH(2); 0CFV
(blueprint: lem-sfb-smooth-stack-family-etale-object-lifts).

Proof plan:
1. Choose smooth surjective scheme atlases `W_j → X_j` and `V → X`, using
   def-sfb-algebraic-moduli-stack. Maps from schemes to `X` are representable by
   lem-sfb-stack-diagonal-space-source-representability; form `Z_j = W_j ×_X V`.
2. Apply lem-sfb-fibred-groupoid-representable-smooth-calculus to the projections.
   Conditions (A) and (B) of lem-sfb-stack-smooth-presentation-criterion show that
   each composite `q_j : W_j → X` is representable smooth, without representability
   of `p_j`.
3. Form the disjoint union `W` by lem-weil-pbc-scheme-coproduct-family and glue the
   atlas objects by def-sfb-stable-pointed-moduli-groupoids. The resulting `q : W → X`
   is smooth by lem-sfb-stack-chartwise-smooth-etale-calculus and representable by the
   diagonal lemma. Joint surjectivity follows by lifting a field object first through
   some `p_j` and then through its atlas, composing the two field extensions.
4. For `x : h_U → X`, the space `P = W ×_X U` is smooth surjective over `U` by
   lem-sfb-fibred-groupoid-representable-smooth-calculus. Apply
   lem-sfb-smooth-space-cover-etale-sections to obtain an étale covering `A_k → U`
   with maps to `P`, hence maps `A_k → W` and isomorphisms with the restriction of `x`.
5. Refine by `A_k ×_W W_j`. These are open subschemes by
   lem-weil-pbc-open-immersion-base-change, cover by the coproduct lemma, and remain
   étale over `U` by lem-weil-pbc-etale-composition-cancellation. Their atlas objects
   and restricted isomorphisms supply the desired lifts. Choose all data in the fixed
   site universe (def-weil-size-convention). For empty `U`, take the empty cover;
   if `J` is empty, joint surjectivity rules out any object over nonempty `U` by
   restriction to a residue field.
-/
theorem exists_etale_object_lifts_of_smooth_stack_family
    {S : Scheme.{u}} (X : BasedCategory.{v₁, w₁} (Over S))
    (J : Type u) (Y : J → BasedCategory.{v₂, w₂} (Over S))
    (p : ∀ j : J, BasedFunctor (Y j) X)
    (hX : IsAlgebraicModuliStack X) (hY : ∀ j : J, IsAlgebraicModuliStack (Y j))
    (hp : ∀ j : J, IsSmoothModuliMap (p j))
    (hsurj : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S)
      (z : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) X),
      ∃ (L : Type u) (_ : Field L) (i : K →+* L) (j : J)
        (y : BasedFunctor
          (discreteModuli (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom i) ≫ b))))
          (Y j)),
        Nonempty (ModuliTwoIso (y.comp (p j))
          ((discreteModuliMap (yoneda.map
            (Over.homMk (Spec.map (CommRingCat.ofHom i))))).comp z)))
    (U : Over S) (x : BasedFunctor (discreteModuli (yoneda.obj U)) X) :
    ∃ (I : Type u) (V : I → Over S) (e : ∀ i : I, V i ⟶ U) (j : I → J)
      (y : ∀ i : I, BasedFunctor (discreteModuli (yoneda.obj (V i))) (Y (j i))),
      (∀ i : I, Etale (e i).left) ∧
      (∀ z : U.left, ∃ (i : I) (t : (V i).left), (e i).left t = z) ∧
      ∀ i : I, Nonempty (ModuliTwoIso ((y i).comp (p (j i)))
        ((discreteModuliMap (yoneda.map (e i))).comp x)) := by
  sorry

end CategoryTheory
