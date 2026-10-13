/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # The underlying-set Kan comparison for an abelian inverse image

Source: Stacks Project, Tags 00YV, 09XN, and 00WK.
(blueprint: new-r2-etale-abelian-kan-comparison-locally-surjective). -/

@[expose] public section

universe u
open CategoryTheory Opposite AlgebraicGeometry

/-- Underlying sections, lifted to the universe of the small etale category. -/
abbrev etaleAbelianLargeSections {X : Scheme.{u + 1}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  F.obj ⋙ forget AddCommGrpCat.{u + 1} ⋙ uliftFunctor.{u + 2, u + 1}

/-- The pointwise set-valued Kan extension before sheafification. -/
noncomputable abbrev etaleAbelianSetKan {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  p.Etale.op.leftKanExtension (etaleAbelianLargeSections F)

/-- The comparison induced by the supplied adjunction unit, by the Kan universal property. -/
noncomputable def etaleAbelianKanComparison
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    etaleAbelianSetKan p F ⟶ etaleAbelianLargeSections (H.obj F) :=
  Functor.descOfIsLeftKanExtension _
    (p.Etale.op.leftKanExtensionUnit (etaleAbelianLargeSections F)) _
    (Functor.whiskerRight (Functor.whiskerRight (hH.unit.app F).hom
      (forget AddCommGrpCat.{u + 1})) uliftFunctor.{u + 2, u + 1})

/-- The underlying-set Kan comparison is locally surjective.
Source: Stacks Project, Tags 09XN and 00YV, inverse image and algebraic structures.
(blueprint: new-r2-etale-abelian-kan-comparison-locally-surjective).

Proof: Sheafify the set-valued pointwise Kan extension along opposite base change.
The sheafification unit is locally surjective. Finite-limit preservation by base
change makes the indexing categories filtered. Filtered colimits of abelian groups
are computed on underlying sets; the lifted set-valued construction therefore
carries the addition and zero induced from F. Sheafification preserves these
operations and their identities. The set adjunction restricts to homomorphisms:
the adjunct of a map preserving addition, zero and inverse preserves each operation,
by naturality of the unit and counit and preservation of finite products. Thus this
constructs the abelian inverse-image adjunction, with the set adjunction unit.
Compare this abelian left adjoint with H via
uniqueness of left adjoints to the specified pushforward. The comparison respects
units, so its underlying map after the sheafification unit is precisely the map
defined here, by the Kan universal property. It is locally surjective since the
sheafification unit is, and the comparison is an isomorphism. To compare coefficient
universes restrict to a small basis of affine etale maps of finite presentation
into affine opens of T and X. Every etale object is covered by such maps; their
fibre products have covers in the same basis. On this basis the set-valued Kan
and plus constructions use diagrams and covering families in the coefficient
universe. On a small skeleton of this basis, matching families are indexed by sets in
Type (u+1), so their products, equalizers and the quotients in the plus construction
stay in Type (u+1). Lifting sets commutes with these limits and small filtered
colimits. Values on an arbitrary etale object are reconstructed from matching
families on a small affine covering, with overlaps checked on affine covers; this
also stays in Type (u+1). These constructions give a left adjoint to the actual
small-coefficient pushforward, and their lifted values identify with the large
set construction by the same matching-family description. Extend the comparison
from the basis by the sheaf condition. The resulting comparison
with the larger-universe set inverse image is an isomorphism locally on every
etale object, hence globally by the sheaf condition. This statement concerns only
the comparison map; extraction
of Kan representatives and a cover indexed by points is done in the importing
module. Empty objects are covered by the empty sieve. -/
theorem etaleAbelianKanComparison_locally_surjective
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallySurjective T.smallEtaleTopology
      (etaleAbelianKanComparison p H hH F) := by sorry
