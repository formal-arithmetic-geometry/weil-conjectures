/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.IntrinsicLabeledResolution

/-!
# Extracting an ordinary tower from an embedded resolution

Source: ILO VIII 2.1.3(ii), 2.1.4, 2.3.1, pp.87,91.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The strict-transform diagram of a single embedded tower is an ordinary resolution
of the input, with its actual intrinsic ideals and its original labels.

Source: ILO VIII 2.1.3(ii), 2.1.4, 2.3.1, pp.87,91; the construction in Step 1 of
lem-trf-embedded-to-intrinsic-smooth-resolution
(blueprint: lem-trf-embedded-resolution-ordinary-tower).

Proof: Enumerate the finite set of active labels increasingly. Use the intrinsic
scheme at the cut just before each label as the corresponding ordinary level, and
use the top cut as the last level. The constant-stage isomorphisms identify any
other cut with the level indexed by the number of labels it contains. Take diagram
transition maps for the ordinary transitions; functoriality gives their laws.
At an active label the ambient center factors as a closed subscheme of the strict
transform. Its intrinsic kernel ideal therefore extends the ambient center ideal.
The strict-transform/blowup identification of ILO 2.1.3(ii), or Stacks 080E, identifies
the next level with the blowup of this kernel ideal, over the preceding level.
The supplied nonempty, nowhere dense, regular and coherent center conditions give
IsRegularResolution; finite type of the center ideals follows from coherence. The
last scheme is regular by finalRegular. Transport the initial identification along
the given embedding isomorphism. At absent labels both ideals are unit ideals.
The increasing enumeration proves index_labels, index_before and the endpoint
identities; an empty label set gives a length-zero tower. regularInput and emptyInput
give the two required length-zero implications. The cut diagram remains the original
intrinsic diagram, so its identity isomorphism gives the required identification,
including its labels and every center ideal. -/
theorem exists_ordinary_tower_of_embedded
    {L : Type w} [LinearOrder L] (S : RationalResolutionInput.{u})
    (p : RationalResolutionEmbedding S) (T : LabeledEmbeddedResolutionTower L p.pair) :
    ∃ A : IntrinsicLabeledOrdinaryTower L S.scheme,
      Nonempty (IntrinsicEmbeddedResolutionIdentification A p T) := by sorry

end AlgebraicGeometry
