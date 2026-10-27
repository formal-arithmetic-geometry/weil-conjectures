/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.ClosedRestrictionSignedData
public import Sheaf.AlgebraicGeometry.FiniteClosedCoverResolution

/-!
# Ordered refinement maps between specified signed closed rows

Source: the agent's signed-refinement calculation from Stacks Tags 09AH and 01FG.
(blueprint: lem-sfb-signed-closed-row-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- The row-level refinement data for an already specified collection of signed rows.
This contains no total maps and constructs no rows.
Source: the signed-refinement deduction from Stacks Tags 09AH and 01FG.
(blueprint: lem-sfb-signed-closed-row-maps). -/
structure SignedClosedRowMaps {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (row : ∀ F : SignedClosedFamily i, SignedClosedRow i F A) where
  mixed : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (_hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (s : Finset (Fin F.length)) (t : Finset (Fin G.length)),
    finiteClosedRestriction (finiteClosedIntersection F.members s).hom A ⟶
      finiteClosedRestriction (finiteClosedIntersection G.members t).hom A
  mixed_unit : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (s : Finset (Fin F.length)) (t : Finset (Fin G.length)), s ⊆ t.image f →
    finiteClosedUnit (finiteClosedIntersection F.members s).hom A ≫ mixed F G f hf s t =
      finiteClosedUnit (finiteClosedIntersection G.members t).hom A
  refine : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (_hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b))), (row F).rows ⟶ (row G).rows
  refine_components : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (M : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) (p : ℕ),
    ((row F).terms p).inv.app M ≫ ((refine F G f hf).app M).f (p : ℤ) ≫
      ((row G).terms p).hom.app M =
        (finiteClosedRefinementMap F.members G.members A f (mixed F G f hf) p).app M
  refine_augment : ∀ (F G : SignedClosedFamily i) (f : Fin G.length → Fin F.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b))),
    (row F).alpha ≫ refine F G f hf = (row G).alpha
  refine_id : ∀ (F : SignedClosedFamily i)
    (hf : ∀ b, Nonempty (F.members b ⟶ F.members (id b))),
    refine F F id hf = 𝟙 (row F).rows
  refine_comp : ∀ (F G H : SignedClosedFamily i)
    (f : Fin G.length → Fin F.length) (g : Fin H.length → Fin G.length)
    (hf : ∀ b, Nonempty (G.members b ⟶ F.members (f b)))
    (hg : ∀ c, Nonempty (H.members c ⟶ G.members (g c)))
    (hfg : ∀ c, Nonempty (H.members c ⟶ F.members ((f ∘ g) c))),
    refine F G f hf ≫ refine G H g hg = refine F H (f ∘ g) hfg

/-- Signed refinement maps exist between any specified unit-normalized signed rows.
In particular, the choice of the rows need not anticipate a choice of refinements.

Source: Stacks Project, cohomology.tex, Tag 01FG, deleted-position sign calculation;
proetale.tex, Tag 09AH, actual closed units; steps 2, 4--7 of
lem-sfb-closed-restriction-signed-refinements.
(blueprint: lem-sfb-signed-closed-row-maps).

Proof: factorizations of family members induce maps between the corresponding finite
intersections by their product projections. For s ⊆ f(t), push the actual unit along
the resulting closed map and identify composite inverse images; put zero for other
pairs. The composition-unit equation proves mixed_unit and compatibility with every
successive restriction. Transport finiteClosedRefinementMap through the given terms
isomorphisms. On an injective image tuple the deleted-face permutation identity
Fin.signed_face_permutation identifies each summand of the two chain equations after
reindexing the deletion positions by their sorted ranks. On a noninjective tuple all
faces are noninjective, unless there is exactly one repeated pair. Only the two
faces deleting that pair then survive: their restrictions coincide by the unit
composition equation and their signed coefficients are negatives. Thus they cancel
in every characteristic. Outside the row support all objects are zero, giving a chain
map in every integer degree. Naturality of the matrices makes this a natural
transformation of row functors. For the singleton components the sign is one and the
unit equation identifies the augmentations; in other degrees the source single
complex is zero. Identity tuples have identity permutation and identity restrictions,
so the identity matrix is obtained. For composition, repeated images give zero on
both sides. Otherwise the two sorting permutation signs multiply to the composite
sorting sign and the restrictions compose. These component identities imply strict
identity and composition by the terms isomorphisms, product projections, and vanishing
outside the support. Unit normalization makes these arguments valid for the supplied
rows: precomposing a comparison with the epimorphic closed unit identifies it with
the actual restriction, so the row restrictions and augmentations coincide with the
ones used in the calculation. -/
theorem signedClosedRow_maps {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (row : ∀ F : SignedClosedFamily i, SignedClosedRow i F A) :
    Nonempty (SignedClosedRowMaps i A row) := by sorry

end AlgebraicGeometry
