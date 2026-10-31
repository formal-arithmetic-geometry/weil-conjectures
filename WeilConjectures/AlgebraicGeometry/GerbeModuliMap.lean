/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

/-! # Gerbes over algebraic spaces

Source: Stacks Project, stacks-morphisms.tex, definition-gerbe, and stacks.tex,
lemma-when-gerbe (blueprint: def-sfb-gerbe-moduli-map).

The two local conditions use covering sieves of the existing big fppf topology.
Restrictions are the actual compositions with maps of represented discrete groupoids.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Local nonemptiness and local connectedness of the lift groupoids over a space.
Since the target has discrete fibres, an isomorphism of two lifts is automatically
compatible with their maps to the specified target object.
Source: Stacks Project, stacks-morphisms.tex, definition-gerbe; stacks.tex,
lemma-when-gerbe, conditions (2)(a) and (2)(b)
(blueprint: def-sfb-gerbe-moduli-map). -/
def IsGerbeModuliMap {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    {Q : AlgebraicSpace S} (p : BasedFunctor F (discreteModuli Q.obj.obj)) : Prop :=
  (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T))
      (discreteModuli Q.obj.obj)),
    ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
      ∀ (U : Over S) (a : U ⟶ T), R a →
        ∃ x : BasedFunctor (discreteModuli (yoneda.obj U)) F,
          Nonempty (ModuliTwoIso (x.comp p)
            ((discreteModuliMap (yoneda.map a)).comp t))) ∧
  (∀ (T : Over S) (x y : BasedFunctor (discreteModuli (yoneda.obj T)) F),
    Nonempty (ModuliTwoIso (x.comp p) (y.comp p)) →
      ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
        ∀ (U : Over S) (a : U ⟶ T), R a →
          Nonempty (ModuliTwoIso
            ((discreteModuliMap (yoneda.map a)).comp x)
            ((discreteModuliMap (yoneda.map a)).comp y)))

end CategoryTheory
