/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Construction of the open support of a subterminal étale sheaf -/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Section factorization property for an open. -/
def etaleSubsheafFactorization (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v))) (W : S.Opens) : Prop :=
  ∀ U : S.Etale,
    (Nonempty (Unique (H.obj.obj (op U))) ↔
      ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom) ∧
    ((¬ ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom) →
      IsEmpty (H.obj.obj (op U)))

/-- A subterminal étale sheaf has an open support with the section factorization property.
Source: Stacks Project, Étale Cohomology, Tag 04HV, lemma-support-subsheaf-final.
(blueprint: lem-weil-pbc-etale-subsheaf-final-open-parts-factorization)

Proof: Monicity into the terminal sheaf makes each section set a subsingleton. Take the
union of the images of all étale objects with a section. Étale maps are open, so the union
is open. A section implies factorization through this union. Conversely, for an object
factoring through it, the pullbacks of the objects used in the union form a jointly
surjective étale covering. Pull back their sections. They agree on every overlap by
subsingletonness; sheaf gluing gives a section on the object, unique by subsingletonness.
If factorization fails, any section would imply factorization, so the section set is empty.
This also handles empty objects: the empty covering supplies their unique section. -/
theorem exists_open_etale_subsheaf_final_factorization (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v)))
    [Mono (terminal.from H)] :
    ∃ W : S.Opens, etaleSubsheafFactorization S H W := by sorry

end AlgebraicGeometry.Scheme
