/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ChowLemma

/-! # Chow modification data with projective immersion

Source: Stacks Project, Theorem 088E, Chow modification paragraph.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A Chow modification with its immersion into a finite projective space over the base
and a nonempty open of the target over which it is an isomorphism.

Source: Stacks Project, Theorem 088E, Chow modification paragraph, using Chow's lemma
0200 and the reduced complement construction.
(blueprint: new-chow-modification-data).

Proof: Apply ChowModification.nonempty_data to f over the Noetherian scheme Spec A.
Extract its source Y, proper surjective map q, finite coordinate type N, immersion
into ProjectiveSpace N (Spec A), equation over Spec A, and dense open U on which the
restriction of q is an isomorphism. Since Z is nonempty and q is surjective, Y is
nonempty. Projective space with an empty coordinate type is empty, so N is nonempty.
Choose a finite enumeration N ≃ ULift (Fin (n + 1)), with n one less than its positive
cardinality. Renaming homogeneous variables induces an isomorphism of projective spaces
over Spec A. Compose the extracted immersion with this isomorphism to obtain e;
composition preserves immersion and the equation over Spec A.
Take L to be the vanishing ideal of the reduced closed complement of U. The reduced
complement theorem identifies its support with that complement, hence L.support.compl
with U. Density of U and nonemptiness of Z imply U is nonempty. Finally the canonical
isomorphism from the pullback along U.ι to the restricted source identifies pullback.snd
with q restricted to U. Transport the restriction isomorphism along this identification
and the equality U = L.support.compl. These constructions supply all asserted data. -/
theorem exists_chow_modification_data
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {Z : Scheme.{u}} [IsNoetherian Z] (f : Z ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hZ : Nonempty Z) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Z) (_ : IsProper q) (L : Z.IdealSheafData)
      (n : ℕ)
      (e : Y ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A))),
      IsImmersion e ∧
      e ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
        q ≫ f ∧
      (L.support.compl : Set Z).Nonempty ∧
      IsIso (pullback.snd q (Scheme.Opens.ι L.support.compl)) := by sorry

end AlgebraicGeometry
