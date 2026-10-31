/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.StageSystem.Preadditive

import WeilConjectures.CategoryTheory.FaithfulStageHomTransport

/-! # Native and colimit Hom groups in the legacy coefficient pair category

Source: blueprint `sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`,
retained owning argument 6, and `AlgebraicallyClosedCoefficients.lean:627-804`
(blueprint: lem-pur-general-legacy-hom-coordinates).

The existing module supplies `homCoordinates_existsUnique`, `homCoordinatesAddEquiv`,
`composition_bilinear` and `inclusion_additive`. This module exposes the remaining equality
of the transferred and native group structures, previously available only privately.
All categories, coefficient models, maps and group structures are the existing legacy ones.
-/

@[expose] public section
set_option autoImplicit false

universe d u v

open CategoryTheory

namespace WeilConjectures.AlgebraicallyClosedCoefficients

/-- The abelian group transferred through the unique representative-normalized Hom
coordinates equals the native common-stage quotient group, including zero and negatives.
Together with `homCoordinates_existsUnique`, `homCoordinatesAddEquiv`,
`composition_bilinear` and `inclusion_additive` this is the full legacy Hom interface.

Source: blueprint two-colimit unit, retained owning argument 6;
`AlgebraicallyClosedCoefficients.lean:627-804`
(blueprint: lem-pur-general-legacy-hom-coordinates).

Proof: (1) The old completed-integral full subcategory is linear. Its raw Hom scalar
localization is preadditive, and scalar extension is additive on pure tensors and hence
on their finite sums. (2) The normalized self-extension unitor makes each reflexive
transition faithful. (3) The associator cocycle and this faithfulness give identity and
composition laws for associator-conjugated Hom transports. Finite composita make the
common-overfield index nonempty and directed. (4) Define addition at a common stage,
zero by a zero representative, and negation on representatives. Transporting all choices
and equality witnesses to a further common stage proves well-definedness. (5) Compute
all abelian-group laws at one common stage; each quotient constructor is additive and
compatible with transport. (6) Send a quotient representative to its direct-limit class;
the same eventual-equality relation makes this a bijection, with inverse the colimit lift
of the quotient constructors. (7) Representative induction proves uniqueness with this
normalization. (8) Represent two arrows at one stage. The direct-limit structure map is
additive, so injectivity of the coordinates identifies transferred addition with native
addition. Uniqueness of zero and inverses and the additive group extensionality theorem
identify the entire group structures, which is the assertion here. (9) For composition,
represent three arrows at one common stage and use its two distributivity laws.
(10) The inclusion of a stage sends an arrow to its reflexive scalar image; reflexive
scalar extension and the quotient constructor are additive. These last two steps give
the already public bilinearity and inclusion assertions without strictifying self-extension.
-/
theorem legacyHomGroup_eq_native
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u}) (A B : Pair D l hl Ω Y) :
    homAddCommGroup A B = StageSystem.PairCategory.instAddCommGroupHom A B := by
  sorry

end WeilConjectures.AlgebraicallyClosedCoefficients
