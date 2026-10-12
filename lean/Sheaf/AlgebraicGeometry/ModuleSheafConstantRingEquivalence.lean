/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.Paper.SiteSheafificationSectionsLocal

/-! # Comparing the two encodings of constant-coefficient module sheaves

Source: Stacks Project, Modules on Sites, Section 18.42 (Tag 093I), opening
paragraph, and Cohomology on Sites, Lemma 21.12.4 (Tag 03FD). The construction
below is the encoding argument needed to apply that lemma.
-/


@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale


/-- Module-valued étale sheaves are modules over the constant ring sheaf.

Source: Stacks Project, Tag 093I, opening paragraph (constant algebraic structures),
and Tag 03FD (underlying abelian sheaves). The encoding argument is written here.
(blueprint: lem-weil-pbc-module-sheaf-constant-ring-equivalence)

Proof: let R be the sheafification of the constant ring presheaf with value Λ.
For a ModuleCat Λ-valued sheaf F, a section of R is locally represented by elements
of Λ. Multiply such representatives by restrictions of a section of F, then glue.
Local equality of representatives makes this independent of all choices. The
module identities hold locally for Λ and hence globally by separatedness. The
restrictions commute with this action, giving a sheaf of R-modules. A morphism
of Λ-module sheaves respects these local actions and their gluings.
Conversely restrict the R-action along the constant-presheaf sheafification unit
Λ → R(U), for each object U. The module identities and restriction compatibility
give a ModuleCat Λ-valued sheaf, since the additive sheaf is unchanged. R-linear
maps give Λ-linear natural transformations. Restricting the glued action recovers
the original Λ-action. Extending the restricted action recovers the R-action:
locally every scalar comes from Λ, so equality follows by separatedness. These
identities give the unit and counit and their triangle identities. Both functors
retain the same additive sheaf and additive maps; their identity components give
the displayed natural isomorphism of underlying-abelian functors.
All ring and module carriers lie in Type (u+1), while X lies in Scheme.{u}; no
universe lift of X, torsion assumption, or injectivity assumption is required.
For the empty scheme the unique sheaves correspond, and for the zero ring all
module sheaves are zero. The same construction applies to ULift coefficients.
-/
theorem moduleSheaf_constantRing_equivalence
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    : let R : Sheaf X.smallEtaleTopology RingCat.{u + 1} := (sheafCompose X.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ))
    ∃ (e : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌
      SheafOfModules.{u + 1} R),
      Nonempty (e.functor ⋙ SheafOfModules.toSheaf R ≅
        sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  sorry

end AlgebraicGeometry
