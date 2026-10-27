/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.AlgebraicClassifyingStackFlatness

/-! # Sections of neutral algebraic gerbes are fppf presentations

Source: Stacks Project, stacks-morphisms.tex, Tag 06QG, lemma-gerbe-with-section,
assertion (3) (blueprint: lem-sfb-neutral-gerbe-section-fppf).

The two gerbe hypotheses express local existence and local isomorphism over the
big fppf site. The conclusion specifies the actual algebraic-space projection of
every scheme 2-base change, with flatness and finite presentation on étale charts.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A section of an algebraic gerbe over a scheme is representable by algebraic
spaces, surjective, flat and locally of finite presentation, as expressed by all
of its scheme 2-base changes.

Source: Stacks Project, stacks-morphisms.tex, Tag 06QG, lemma-gerbe-with-section,
assertion (3) (blueprint: lem-sfb-neutral-gerbe-section-fppf).

`hobjects` gives fppf local lifts of every map to V. `hisomorphisms` gives fppf
local isomorphisms between any two objects with the same image in V. Because V
is a discrete fibred groupoid, such an isomorphism automatically respects that
image; no compatibility condition on a chosen isomorphism has been omitted.

Proof:
1. By lem-sfb-etale-smooth-atlas-fppf-descent, F is an fppf stack. Apply
   lem-sfb-self-relation-quotient-embedding to x. Its self-relation R is an
   algebraic space and the quotient maps fully faithfully to F. Applying a to
   an arrow x(v) -> x(w), and using hsection, gives v = w in the discrete V.
   Thus the two projections R -> V coincide, and R is the automorphism group G
   of x with its identity, composition and inverse: the action on V is trivial.
2. By lem-sfb-groupoid-stackification-local-description, [V/G] is an fppf stack.
   For y over T put v = a(y). The gerbe local-isomorphism hypothesis identifies
   y locally with x(v). Hence [V/G] -> F is locally essentially surjective.
   By lem-sfb-stack-fully-faithful-local-equivalence it is an equivalence. A
   quasi-inverse carries the smooth atlas and algebraic-space diagonal of F to
   [V/G], making [V/G] algebraic with the same scheme-test properties.
3. Apply lem-sfb-algebraic-classifying-stack-flatness: G -> V is flat and
   locally of finite presentation. Both endpoints of the trivial-action
   groupoid are this map; no smoothness of G is required.
4. By lem-sfb-flat-groupoid-algebraic-quotient, V -> [V/G] is representable,
   surjective, flat and locally of finite presentation. The quotient equivalence
   and its identification of the object map with x identify its base changes
   with those of x over every T and y. Transport their algebraic-space
   representatives and projections along this identification. Their
   surjectivity and their flat, locally finitely presented étale chart maps
   give the stated conclusion. -/
theorem neutral_gerbe_section_fppf
    {S : Scheme.{u}} (V : Over S) (F : BasedCategory.{v, w} (Over S))
    (a : BasedFunctor F (discreteModuli (yoneda.obj V)))
    (hF : IsAlgebraicModuliStack F)
    (hobjects : ∀ (T : Over S) (t : T ⟶ V),
      ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
        ∀ (U : Over S) (f : U ⟶ T), R f →
          ∃ z : BasedFunctor (discreteModuli (yoneda.obj U)) F,
            Nonempty (ModuliTwoIso (z.comp a) (discreteModuliMap (yoneda.map (f ≫ t)))))
    (hisomorphisms : ∀ (T : Over S)
      (y z : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      Nonempty (ModuliTwoIso (y.comp a) (z.comp a)) →
        ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
          ∀ (U : Over S) (f : U ⟶ T), R f →
            Nonempty (ModuliTwoIso ((discreteModuliMap (yoneda.map f)).comp y)
              ((discreteModuliMap (yoneda.map f)).comp z)))
    (x : BasedFunctor (discreteModuli (yoneda.obj V)) F)
    (hsection : ModuliTwoIso (x.comp a) (BasedFunctor.id (discreteModuli (yoneda.obj V)))) :
    ∀ (T : Over S) (y : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange x T y Z p ∧ SpaceMapIsSurjective Z T p ∧
          ∀ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
            Flat ((yoneda.preimage (b ≫ p)).left) ∧
              LocallyOfFinitePresentation ((yoneda.preimage (b ≫ p)).left) := by
  sorry

end CategoryTheory
