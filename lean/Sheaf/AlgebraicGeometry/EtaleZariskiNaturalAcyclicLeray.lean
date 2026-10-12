/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections
import Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Sheaf.Paper.ZariskiEtaleSheafLeftExact
import Sheaf.CategoryTheory.SitePullbackAbelianUnderlying
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # Natural acyclic Leray with two Ext models

Source: Stacks Project, Tags 03DW, 03P2 and 0733.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Natural mixed-universe Leray comparison on the subcategory of acyclic abelian
sheaves. No quasi-coherent module or tensor-sections construction is assumed.
Source: Stacks Project, Cohomology on Sites, Tag 0733(1), Tags 072Z and 0730;
Ext via injective resolutions, Tag 06XP.
(blueprint: lem-sc-etale-zariski-natural-acyclic-leray)

Proof: inverse image along a continuous finite-limit-preserving inclusion of opens
is exact, so its right adjoint T preserves injectives. If F is T-acyclic, pushing
an injective resolution of F through T gives an injective resolution of TF:
left exactness handles degree zero and the assumed vanishing handles positive
exactness. Sections at the terminal open agree with sections of F at its terminal
etale image. Compute both Ext models using these resolutions; the free abelian
representable at the terminal open represents sections, as does the constant
integer sheaf at the terminal etale object. Their Hom complexes are the same
section complex. Thus the resulting comparison is additive and invertible.
Comparison chain maps lifting any coefficient morphism commute with the section
identification. Any two lifts are homotopic, and induce the same cohomology map.
Hence the equivalences are simultaneous and natural, independently of resolution
choices and of the proofs of acyclicity. The small enough-injectives Ext model
and the standard large model have the same cocycle and coboundary computation.
This argument works in positive degree on the empty scheme as well. -/
theorem etaleZariskiNaturalAcyclicLeray
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology]
    [(i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits i] (hterminal : IsTerminal (i.obj ⊤))
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] :
    let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
    ∃ b : ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) (n : ℕ),
        Sheaf.H' (T.obj F) (n + 1) (⊤ : X.Opens) ≃+
          @Sheaf.H _ _ X.smallEtaleTopology F inferInstance (HasExt.standard _) (n + 1),
      ∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F))
        (hG : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj G))
        (φ : F ⟶ G) (n : ℕ) (x : Sheaf.H' (T.obj F) (n + 1) (⊤ : X.Opens)),
        b G hG n (((Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X.carrier) (n + 1)).map (T.map φ)).app (op ⊤) x) =
          @Sheaf.H.map _ _ X.smallEtaleTopology inferInstance (HasExt.standard _)
            _ _ φ (n + 1) (b F hF n x) := by sorry

end AlgebraicGeometry.Scheme.Modules
