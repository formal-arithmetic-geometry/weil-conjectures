/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Lifted étale cohomology computed by a finite affine section complex

Source: Stacks Project, Tag 03P2, separated-case proof, and Tag 03DW (2).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The lifted associated étale sheaf is computed by the lifted module section
Čech complex of any finite affine open cover of a separated scheme, in positive degree.
Source: Stacks Project, Tag 03P2, separated-case proof, and Tag 03DW (2).
(blueprint: lem-sc-etale-qcoherent-ulift-finite-cech-comparison)

Proof: Every nonempty finite intersection of the affine opens is affine, by
separatedness. Tensor pullback preserves quasi-coherence. The open-immersion
pullback/restriction identification identifies sections of the associated étale
sheaf on each intersection with the sections of F there, compatibly with all
restriction maps. Apply ULift to these sectionwise identifications. Lifted affine
quasi-coherent acyclicity gives zero positive cohomology on every intersection.
Apply the Čech-to-derived spectral sequence to this covering with large
coefficients. Its positive rows vanish, so its edge isomorphism identifies H^(n+1) at
the terminal object with degree-(n+1) homology of its section Čech complex.
The free-abelian-Yoneda adjunction identifies Hom from the sheafified free
representable at the terminal object with evaluation. Computing Ext on an
injective resolution identifies the spectral sequence's H' abutment with derived
evaluation there. The existing
`Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ` then identifies
this derived evaluation with Ext-defined Sheaf.H. In each degree the set of cover tuples is finite.
Forgetting module scalars and lifting the groups preserves these products and
commutes with every restriction map and each signed summand of the alternating
differential. Thus the section complex is isomorphic to the stated image of the
module Čech complex; apply homology to that complex isomorphism and compose with
the edge isomorphism. This comparison stops at the homology of the lifted complex:
it does not assert a comparison of coefficient universes in sheaf cohomology.
For an empty scheme the same argument permits an empty cover, yielding zero
complexes; the zero module also yields zero complexes. -/
theorem nonempty_etaleTensorSectionsSheaf_ulift_finiteCech_succ
    (X : Scheme.{u}) [X.IsSeparated] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Nonempty (Sheaf.H
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (etaleTensorSectionsSheaf F)) (n + 1) ≃+
      (((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
          ((cechComplexFunctor U).obj F.presheafModuleCat)).homology (n + 1)) := by sorry

end AlgebraicGeometry.Scheme.Modules
