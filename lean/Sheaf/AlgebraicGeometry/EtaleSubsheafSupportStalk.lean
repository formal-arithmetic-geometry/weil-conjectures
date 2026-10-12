/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSubsheafSupportOpen
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Geometric stalks of the open support of a subterminal étale sheaf -/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The open support of a subterminal étale sheaf is detected by geometric stalks.
Source: Stacks Project, Étale Cohomology, Tag 04HV, lemma-support-subsheaf-final.
(blueprint: lem-weil-pbc-etale-subsheaf-final-open-parts-stalk)

Proof: An element of the stalk is represented by a section on a pointed étale neighbourhood.
The factorization property puts the image point in W. Conversely, if the point belongs to
W, the geometric morphism lifts through the open immersion W → S. This makes W a pointed
étale neighbourhood. The identity factorization of W gives its unique section, whose image
in the stalk proves nonemptiness. Monicity into the terminal sheaf makes all section sets
subsingletons. Their filtered colimit is a subsingleton: two representatives agree after a
common pointed refinement. Therefore a nonempty stalk is a singleton; the converse follows
from its distinguished element. -/
theorem etale_subsheaf_final_stalk_criterion (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v)))
    [Mono (terminal.from H)] (W : S.Opens)
    (hW : etaleSubsheafFactorization S H W) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
      (x default ∈ W ↔ Nonempty ((pointSmallEtale x).sheafFiber.obj H)) ∧
      (Nonempty ((pointSmallEtale x).sheafFiber.obj H) ↔
        Nonempty (Unique ((pointSmallEtale x).sheafFiber.obj H))) := by sorry

end AlgebraicGeometry.Scheme
