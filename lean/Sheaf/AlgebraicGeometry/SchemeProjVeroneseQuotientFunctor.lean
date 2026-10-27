/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.SchemeVeroneseQuotientData
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The Veronese quotient functor represented by scheme relative Proj

Source: Stacks Project, Constructions, Tags 01NW, 01NY and 01NZ, including equation-proj
and the twisting-sheaf normalization in the second proof of 01NZ
(blueprint: lem-sfb-scheme-proj-veronese-quotient-functor).

The quasi-coherent algebra is in the existing `GradedAlgebraData` affine-basis presentation.
`Representation` includes the equivalence relation, the prescribed pullback on classes,
the compatible-family extension to arbitrary tests, the actual contravariant functor,
the representing natural bijection, the structural-map equation and the normalization
against the existing twisting sheaves. The final equation fixes graded-isomorphism naturality.
The `ULift` in the Yoneda functor only puts the morphism set in the quotient set's universe.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.VeroneseQuotient

/-- Relative Proj represents positive-Veronese invertible quotients, with the prescribed
canonical normalization and contravariant graded-isomorphism action.

Source: Stacks, 01NW, equation-proj, 01NY and 01NZ
(blueprint: lem-sfb-scheme-proj-veronese-quotient-functor).

Proof:
1. Use `lem-sfb-relative-proj-twists-degree-opens` to obtain the relative twists `E_j`,
   canonical homogeneous map and the opens `Y_d`. On `Y_d` the degree-d twist is a line,
   the degree-d map is surjective, and multiplication identifies its powers with `E_dn`.
   The opens cover Proj and increase when d is replaced by a positive multiple.
2. Over each affine base open, tensor-pullback adjunction and the affine tilde--sections
   adjunction turn a datum into a graded map to the line's section ring. Its degree-one
   sections generate the line. Apply `lem-sfb-proj-fixed-degree-line-quotient`. Unitality
   identifies the map to the base with f. Affine refinements of intersections and
   uniqueness glue the local maps and their normalized line isomorphisms. This gives
   fixed-degree classification for arbitrary tests, with the actual twisting sections.
3. Raising a datum to a positive tensor power preserves degree-one surjectivity: locally
   lift a free generator and raise that lift to its power. Such powers leave its Proj
   map unchanged. At a common degree two equivalent data therefore give the same map.
   Conversely, at the least common multiple their powered lines both identify with the
   pullback of `E_m`, respecting every homogeneous component, including degree zero.
   Thus `Equivalent` is an equivalence relation and exactly identifies equal Proj maps.
4. On a quasi-compact test a finite subcover by inverse images of degree opens has a
   positive common degree m; its map therefore comes from degree-m data. For an empty
   test take m=1. The remembered map is the composite with the structural morphism.
5. For arbitrary tests classify each quasi-compact open. Their intersections are covered
   by affine opens, so compatibility makes the maps agree there without assuming
   quasi-separatedness. Scheme-morphism gluing gives the inverse-limit bijection.
   On a quasi-compact test evaluation at the top open is a bijection.
6. For a test morphism and a quasi-compact source open, its quasi-compact image lies in
   a finite union of affine target opens. Pull back that target component. Tensor
   pullback preserves a surjection onto a line since it is locally split. Pulling back
   the common-power isomorphism preserves equivalence, so the class is independent of
   the representative and of the chosen target open. Fixed-degree classification
   identifies it with composition of scheme maps. Identity, composition and naturality
   follow, giving the specified functor and its representing natural isomorphism.
7. For a graded algebra isomorphism e, the ordinary Proj isomorphism has comorphism
   b/a^k ↦ e(b)/e(a)^k on standard charts. The normalized fixed-degree classification
   therefore sends its composite with g to the quotient ψ after precomposition by e
   in every degree. Glue on base overlaps and extend componentwise to arbitrary tests.
   This gives `IsoActs` in exactly the asserted contravariant direction.
-/
theorem scheme_proj_veronese_quotient_functor {S : Scheme.{u}} (Z : Over S) :
    ∃ R : ∀ A : Z.left.GradedAlgebraData, Representation Z A,
      ∀ (A B : Z.left.GradedAlgebraData) (e : A ≅ B) (T : Over S)
        (g : T ⟶ projTest Z B) (V : CompactOpens T),
        IsoActs e
          (((R B).sections T ((R B).represent.hom.app (op T) ⟨g⟩)).val V)
          (((R A).sections T
            ((R A).represent.hom.app (op T) ⟨g ≫ projIsoHom e⟩)).val V) := by
  sorry

end AlgebraicGeometry.Scheme.VeroneseQuotient
