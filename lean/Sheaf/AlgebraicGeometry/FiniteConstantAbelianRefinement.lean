/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves

/-!
# Refining a finite set trivialization to an abelian trivialization

Source: Stacks Project, Tag 03RU, and the finite-operation argument in
`lem-weil-pbc-finite-local-abelian-forget`, step 2.
(blueprint: lem-weil-pbc-finite-constant-abelian-refinement).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- An abelian sheaf whose underlying restriction has a specified finite constant value
admits abelian constant trivializations after an etale refinement of that member.
Source: Stacks Project, Tag 03RU; the finite-operation refinement in step 2 of
`lem-weil-pbc-finite-local-abelian-forget`.
(blueprint: lem-weil-pbc-finite-constant-abelian-refinement)

Proof: identify the localized site at `U` with the small etale site of `U.left`.
The given isomorphism supplies one global section for each element of `S`.
For each geometric point of `U.left`, the germ isomorphism for a constant sheaf
identifies `S` with the underlying abelian stalk. Transport its abelian operations to `S`.
For each of the finitely many pairs in `S × S`, the sum of the corresponding sections
has the same germ as the section labeled by the transported sum. Similarly the zero
section and each of the finitely many negatives have the corresponding germs.
Equality of two germs holds on an etale neighborhood. Intersect these finitely many
neighborhoods to make all these equalities hold at once. On that neighborhood, the set
isomorphism preserves zero, addition and negation, since these equalities hold for every
constant input, and all sections of a constant sheaf are locally constant inputs.
It therefore lifts to an isomorphism with the constant abelian sheaf of the transported
finite group. The group laws hold in the chosen stalk. The neighborhoods, one at every
geometric point, jointly cover `U.left`; choose one above each underlying point to keep
its indexing type in universe `u`. Translate their trivializations back to restrictions
of `G` along the composite maps to `Y`. If `U.left` is empty, take the empty cover.
If `S` is empty on a nonempty member, the assumed isomorphism cannot exist because an
abelian stalk contains zero; thus this case introduces no extra hypothesis. -/
theorem finite_constant_abelian_refinement {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S) :
    ∃ 𝒱 : Cover.{u} etalePrecoverage U.left, ∀ j : 𝒱.I₀,
      (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj
        (𝒱.etalePrecoverageToEtale j))).IsConstant
          (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj
            (𝒱.etalePrecoverageToEtale j))) := by sorry

end AlgebraicGeometry.Scheme
