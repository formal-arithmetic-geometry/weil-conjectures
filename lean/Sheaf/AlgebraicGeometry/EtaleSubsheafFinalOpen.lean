/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Subsheaves of the final étale sheaf are open subfunctors

Source: Stacks Project, Étale Cohomology, Tag 04HV, used in Tag 09XM
(blueprint: lem-weil-pbc-etale-subsheaf-final-open).
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A subsheaf of the final small étale sheaf is represented by a unique open subscheme.
`H` is a subsheaf of the final sheaf `⊤_ _`: the unique morphism `terminal.from H` is a
monomorphism. `Nonempty (Unique A)` means that the set `A` is a singleton.
Source: Stacks Project, Étale Cohomology, Tag 04HV, statement and proof
(blueprint: lem-weil-pbc-etale-subsheaf-final-open).

Proof:
1. Each section set is empty or a singleton. Take the union of the images of all étale
   objects admitting a section. Étale morphisms are open, so this gives an open `W`
   (lem-weil-pbc-etale-morphism-open-map).
2. A section over `U` implies its image is contained in `W`. Conversely, when `U` factors
   through `W`, pull back the étale objects used in the union to cover `U`. Their sections
   restrict to sections on this cover. They agree on overlaps by subsingletonness, and
   glue uniquely by the sheaf condition (def-weil-pbc-etale-sheaf-of-sets). Thus the section
   set is a singleton precisely for morphisms factoring through `W`, and empty otherwise.
3. Testing the factorization property on the open immersions of two candidate opens gives
   both inclusions, proving uniqueness. A geometric stalk is nonempty precisely when some
   pointed étale neighbourhood has a section (def-weil-pbc-geometric-stalks). This is
   equivalent to the image point lying in `W`; in that case `W` itself is a pointed
   neighbourhood with a section. The filtered colimit of the subsingleton section sets is
   a subsingleton, so a nonempty stalk is a singleton (def-weil-geometric-point). -/
theorem existsUnique_open_of_etale_subsheaf_final (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v)))
    [Mono (terminal.from H)] :
    ∃! W : S.Opens,
      (∀ U : S.Etale,
        (Nonempty (Unique (H.obj.obj (op U))) ↔
          ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom) ∧
        ((¬ ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom) →
          IsEmpty (H.obj.obj (op U)))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
        (x default ∈ W ↔ Nonempty ((pointSmallEtale x).sheafFiber.obj H)) ∧
        (Nonempty ((pointSmallEtale x).sheafFiber.obj H) ↔
          Nonempty (Unique ((pointSmallEtale x).sheafFiber.obj H)))) := by
  sorry

end AlgebraicGeometry.Scheme
