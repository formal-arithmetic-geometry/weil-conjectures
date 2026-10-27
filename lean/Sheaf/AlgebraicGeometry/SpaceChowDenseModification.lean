/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup
import Sheaf.AlgebraicGeometry.SpaceFiniteTypeComposition
import WeilConjectures.Compactification.ProjectiveSpace
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Dense-open Chow modification of an algebraic space

Source: Stacks Project, spaces-more-morphisms.tex, Tag 088U,
lemma-chow-noetherian-separated, specialized to an affine Noetherian target;
Tag 08BE, theorem-grothendieck-existence, third paragraph of the proof
(blueprint: lem-sfb-space-chow-dense-modification).

The source and target retain their given maps to S. The open is the existing
representable open subfunctor, and its inverse image uses the actual presheaf pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type algebraic space over an affine Noetherian base admits a
representable proper surjection from a Noetherian scheme, unchanged over a dense open,
and an immersion of that scheme into finite-dimensional projective space over the base.
The immersion is explicitly an open immersion followed by a closed immersion.

Source: Stacks Project, Tag 088U, lemma-chow-noetherian-separated, and its application
in Tag 08BE, theorem-grothendieck-existence
(blueprint: lem-sfb-space-chow-dense-modification).

Proof:
1. Spec A is Noetherian by pqf-def-locnoeth and lem-weil-pbc-affine-scheme-qcqs.
   Apply lem-sfb-space-dense-affine-immersion to obtain a dense quasi-compact open U
   with an immersion into affine space over Spec A. Compose with the standard open
   chart of projective space from lemma-nagata-relative-affine-space-open-immersion.
2. Apply lem-sfb-space-blowup-embedding-extension. This gives a closed subscheme Z
   of projective space, a finite-type quasi-coherent ideal J of Z, its ordinary scheme
   blowup Z', and a scheme V open in Z'. It supplies a representable proper map
   q : V → X whose entire inverse image of U maps isomorphically onto U.
3. The map Z → Spec A is H-projective. By lem-sfb-projective-affine-base-blowup,
   the blowup Z' is H-projective over Spec A. Choose its closed immersion i into
   some P^r_A. Composing with the open immersion j : V → Z' gives e = j ≫ i.
4. Properness makes the point image of q closed by def-sfb-space-morphism-properties.
   It contains the dense open U because q is an isomorphism above U, so it is all
   of X. Thus q is surjective, also after scheme base change, as q is representable.
5. Proper q is finite type. Compose with f using lem-sfb-space-finite-type-composition.
   Apply lem-weil-pbc-finite-type-over-noetherian to see that V is quasi-compact and
   locally Noetherian. By lem-weil-pbc-locally-noetherian-quasi-separated it is also
   quasi-separated, as required. The construction imposes no reducedness,
   irreducibility or flatness hypothesis, and permits the empty scheme. -/
theorem exists_chow_dense_modification {S : Scheme.{u}}
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (a : Spec (.of A) ⟶ S) (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace (Over.mk a))
    (hsep : MapIsSeparated f) (hft : MapIsFiniteType f) :
    ∃ (V : Over S) (b : V ⟶ Over.mk a) (q : schemeSpace V ⟶ X)
      (U : OpenSubspace X) (r : ℕ)
      (e : V.left ⟶ ProjectiveSpace (ULift.{u} (Fin (r + 1))) (Spec (.of A)))
      (W : Scheme.{u}) (j : V.left ⟶ W)
      (i : W ⟶ ProjectiveSpace (ULift.{u} (Fin (r + 1))) (Spec (.of A))),
      IsNoetherian V.left ∧
      IsRepresentable q.hom.hom ∧ MapIsProper q ∧ IsSurjective q.hom.hom ∧
      (q ≫ f).hom.hom = yoneda.map b ∧
      Dense (pointImage U.val.ι) ∧
      IsIso (pullback.snd q.hom.hom U.val.ι) ∧
      IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = e ∧
      e ≫ (ProjectiveSpace (ULift.{u} (Fin (r + 1))) (Spec (.of A)) ↘ Spec (.of A)) =
        b.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
