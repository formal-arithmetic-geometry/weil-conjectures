/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal

import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Sheaf.CategoryTheory.SetSheafCoverDescent
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.RingTheory.IndEtaleUniverseTransport

/-! # Affine comparison for torsors under classical group sheaves

Source: current blueprint, sec-proetale-coefficients/sk-lem-pe-torsor-comparison,
`sk-lem-pe-torsor-comparison-affine.md`; Stacks Project, Tag 099X
(blueprint: det-pe-torsor-comparison-affine).

Group sheaves are Mathlib internal group objects in sheaves of sets. Actions and their
laws are stated as sheaf morphisms, and the torsor condition uses the displayed
isomorphism and epimorphism of the source. No commutativity is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison inverse image on the original small sites, as publicly
retained by the recorded comparison module. Its data is left Kan extension followed by
sheafification, not an arbitrary left adjoint.
Source: Stacks Tags 099R and 099X (blueprint: det-pe-torsor-comparison-affine). -/
abbrev torsorComparisonPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical product-preserving structure, used to pull back group multiplication,
unit, inverse and actions. Its multiplication comparison is the inverse of the canonical
product comparison.
Source: Stacks Tags 099R and 099X (blueprint: det-pe-torsor-comparison-affine). -/
instance torsorComparisonPullback_monoidal (X : Scheme.{u}) :
    (torsorComparisonPullback X).Monoidal :=
  haveI := Scheme.preservesFiniteLimits_proEtaleSiteComparison X
  Functor.Monoidal.ofChosenFiniteProducts (torsorComparisonPullback X)

/-- Every torsor under a pulled-back group sheaf on an affine scheme descends to an
etale torsor with a section on one affine etale surjection; the given torsor is classical
and has a section on the same etale covering. The action isomorphism identifies these
sections with trivializations by left translation.
Source: blueprint `sk-lem-pe-torsor-comparison-affine.md`; Stacks Tag 099X
(blueprint: det-pe-torsor-comparison-affine).

Proof:
1. Local surjectivity of the epic map T to the terminal sheaf gives local sections.
   The fpqc finite affine refinement in sk-def-pe-site and the finite affine coproduct
   spectrum lemma give one affine weakly etale surjection carrying a section.
2. Apply sk-thm-pe-indetale-refinement and ind-etale stability to refine this to one
   affine ind-etale surjection U. Present U as a cofiltered limit of affine etale U_i.
   Each U_i is surjective since U factors through it.
3. Simple transitivity gives the unique transition g with s_1 = g s_2. Uniqueness on
   the triple product gives g_13 = g_12 g_23, without a commutativity assumption.
4. Finite affine etale products present the double and triple products of U. Apply
   lem-weil-pbc-comparison-sections to identify their group sections with filtered
   colimits, compatibly with restrictions and group operations.
5. The elementwise filtered-colimit lemma descends g and its cocycle identity to
   one stage V = U_i. Diagonal restriction and cancellation give normalization and
   the inverse identity, including repeated indices.
6. Apply lem-pe-set-sheaf-cover-descent to right multiplication h maps to h c_12.
   Left multiplication commutes with these transitions, so it glues to an action
   on T_0. The local unit gives s_0 in T_0(V); local inverse maps
   (a,b) maps to (a b inverse,b) glue, giving the torsor isomorphism. The section
   on the covering makes T_0 to the terminal sheaf epic.
7. Pull back s_0 using the comparison unit. On the affine ind-etale basis, the
   comparison-sections formula identifies the pulled-back local trivialization
   with the group by h maps to h s'. This proves the local comparison with T.
8. Its two overlap restrictions agree since s_1 = g s_2 and s'_1 = g s'_2.
   Descent glues the maps and their inverses, giving the equivariant global iso e.
9. det-pe-classical-sheaves-image makes T classical. The image of the pulled-back
   s_0 supplies a section of T(V), hence its asserted etale trivialization.
-/
theorem torsor_comparison_affine (X : Scheme.{u}) [IsAffine X]
    (G₀ : Grp (Sheaf X.smallEtaleTopology (Type (u + 1))))
    (T : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (a : (torsorComparisonPullback X).obj G₀.X ⊗ T ⟶ T)
    (h_one : (MonObj.one (X := (torsorComparisonPullback X).obj G₀.X) ▷ T) ≫ a =
      (λ_ T).hom)
    (h_mul : (MonObj.mul (X := (torsorComparisonPullback X).obj G₀.X) ▷ T) ≫ a =
      (α_ _ _ T).hom ≫ ((torsorComparisonPullback X).obj G₀.X ◁ a) ≫ a)
    (h_iso : IsIso (lift a (snd ((torsorComparisonPullback X).obj G₀.X) T)))
    (h_epi : Epi (toUnit T)) :
    ∃ (V : X.Etale), IsAffine V.left ∧ Surjective V.hom ∧
      ∃ (T₀ : Sheaf X.smallEtaleTopology (Type (u + 1))) (a₀ : G₀.X ⊗ T₀ ⟶ T₀),
        (MonObj.one (X := G₀.X) ▷ T₀) ≫ a₀ = (λ_ T₀).hom ∧
        (MonObj.mul (X := G₀.X) ▷ T₀) ≫ a₀ =
          (α_ G₀.X G₀.X T₀).hom ≫ (G₀.X ◁ a₀) ≫ a₀ ∧
        IsIso (lift a₀ (snd G₀.X T₀)) ∧ Epi (toUnit T₀) ∧
        Nonempty (T₀.obj.obj (op V)) ∧
        ∃ e : (torsorComparisonPullback X).obj T₀ ≅ T,
          Functor.LaxMonoidal.μ (torsorComparisonPullback X) G₀.X T₀ ≫
            (torsorComparisonPullback X).map a₀ ≫ e.hom =
              ((torsorComparisonPullback X).obj G₀.X ◁ e.hom) ≫ a ∧
          IsClassical T ∧ Nonempty (T.obj.obj (op ((Scheme.toProEt X).obj V))) := by
  sorry

end AlgebraicGeometry.ProEtale
