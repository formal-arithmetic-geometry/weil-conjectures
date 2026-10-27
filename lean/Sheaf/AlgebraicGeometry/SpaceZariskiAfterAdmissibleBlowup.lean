/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties

import Sheaf.AlgebraicGeometry.AlgebraicSpaceQcOpenBoundaryIdeal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceStrictTransformAsBlowup
import Sheaf.AlgebraicGeometry.SpaceFlatteningByAdmissibleBlowup
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCompositionCentresTransforms

/-! # Zariski main theorem after an admissible blowup of an algebraic space

Source: Stacks Project, More on Morphisms of Spaces, Tag 087F, with the separatedness
hypothesis of More on Flatness, Tag 081S; Divisors on Spaces, Tag 0864(1)
(blueprint: lem-sfb-space-zariski-after-admissible-blowup).

Blowups use the existing affine-etale-chart presentations. The extended centre is
specified by its epi-mono image factorization. The final two cartesian squares and
triangle specify the canonical restrictions over the given open, including the
identity under the identification of its inverse image with that open.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type morphism to a qcqs algebraic space, isomorphic over a
quasi-compact open, becomes an open immersion on the intrinsic blowups after an
admissible finite-type quasi-coherent blowup of the base. The map is over the base
and restricts to the identity using the given isomorphism over the open.
Source: Stacks Project, More on Morphisms of Spaces, Tag 087F; More on Flatness,
Tag 081S (separatedness); Divisors on Spaces, Tag 0864(1)
(blueprint: lem-sfb-space-zariski-after-admissible-blowup).

Proof:
1. By lem-sfb-space-qc-open-boundary-ideal choose a finite-type ideal I0 with zero
   locus exactly T minus U and unit restriction to U. Blow up I0. By
   lem-sfb-space-blowup-chart-properties its exceptional ideal is Cartier and the
   inverse image of U is schematically dense. Replace X by its strict transform,
   using lem-sfb-space-strict-transform-as-blowup. The new base is qcqs, the new
   map is separated and finite type, hence quasi-separated, and is still an
   isomorphism over U.
2. An isomorphism is flat and locally finitely presented, as is seen on common
   etale scheme charts. Apply lem-sfb-space-flattening-by-admissible-blowup to
   this map and the inverse image of U. The second centre is finite type and
   unit over U; the second strict transform is flat and finitely presented.
   The strict-transform comparison preserves separatedness.
3. Apply lem-sfb-space-composition-centres-and-transforms to the two blowups.
   Its support formula gives a single finite-type centre I whose zero locus
   is exactly T minus U, so I restricts to the unit ideal on U. Its compatible
   comparisons identify the iterated strict transform with the strict transform
   for this one blowup, hence with the blowup in the image of f^* I to O_X by
   lem-sfb-space-strict-transform-as-blowup.
4. The inverse image of U in this final base blowup is schematically dense by
   lem-sfb-space-blowup-chart-properties. Its inclusion is quasi-compact: on
   affine etale charts a finite affine cover trivializes the exceptional Cartier
   ideal, and on each member its complement is a principal affine open.
   The transformed map is separated, flat and locally finite type, and remains
   an isomorphism over that open. Apply lem-sfb-space-flat-isomorphism-dense-open
   to obtain the open immersion v.
5. Transport v by the projection-preserving comparisons in step 3. These give
   v followed by the base blowup map equal to f following the source blowup map.
   Both blowups are isomorphisms over U. Their canonical inverse sections give
   lT and lX in the two cartesian squares below. The off-centre identification
   of the strict transform gives lX followed by v equal to fU followed by lT;
   after identifying XU with U by fU this is precisely the identity. -/
theorem exists_openImmersion_blowups_of_isIso_over_open
    {S : Scheme.{u}} (X T U XU : AlgebraicSpace S) (f : X ⟶ T) (j : U ⟶ T)
    (hfsep : MapIsSeparated f) (hfft : MapIsFiniteType f)
    (hTqc : ∃ (V : Over S) (a : yoneda.obj V ⟶ T.obj.obj),
      CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a)
    (hTqs : IsAbsolutelyQuasiSeparated T)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (hUqc : ∃ (V : Over S) (a : yoneda.obj V ⟶ U.obj.obj),
      CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a)
    (q : XU ⟶ X) (fU : XU ⟶ U) (hU : IsPullback q fU f j) (hfU : IsIso fU) :
    ∃ I : QuasiCoherentIdeal T,
      (I.val : T.Modules).IsFiniteType ∧ IsIso (idealTensorMap j I) ∧
      ∃ J : QuasiCoherentIdeal X,
        (∃ e : (moduleTensorPullback f).obj (I.val : T.Modules) ⟶ (J.val : X.Modules),
          Epi e ∧ e ≫ J.val.arrow = idealTensorMap f I) ∧
        ∃ (B : BlowupPresentation I) (C : BlowupPresentation J) (v : C.space ⟶ B.space),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) v.hom.hom ∧
          v ≫ B.projection = C.projection ≫ f ∧
          ∃ (lT : U ⟶ B.space) (lX : XU ⟶ C.space),
            IsPullback lT (𝟙 U) B.projection j ∧
            IsPullback lX (𝟙 XU) C.projection q ∧
            lX ≫ v = fU ≫ lT := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
