/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.Algebra.Homology.LocallyFreeDerivedHom

/-! # The evaluation identification for finite locally free internal modules -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Derived maps from P[0] are derived sections of internal Hom from P.
Source: Stacks Project, Tag 08JJ; Hemo--Richarz--Scholbach, Lemma 5.3(2), evaluation.
(blueprint: lem-weil-pbc-condensed-finite-free-hom-evaluation)

Proof: on a pro-etale covering trivializing P, the tensor functor - tensor P is a
finite power of the identity and is exact. The module tensor-Hom adjunction therefore
shows that internal Hom from P preserves K-injective complexes: its acyclic Hom tests
are transported to acyclic Hom tests by this exact left adjoint. Resolve the input
complex by a functorial K-injective complex J. Internal Hom from P applied to J is
K-injective, so its ordinary sections compute the specified right derived sections.
Sections of internal Hom from P are ordinary additive maps from P. Degree n cycles of
that Hom complex are chain maps P[0] to J[n], and boundaries are their homotopies.
K-injectivity identifies the homotopy classes with maps in the ordinary derived
category. This identifies the two displayed abelian groups and their addition.
The evaluation identification commutes with every chain map, giving the natural
isomorphism of functors; it also commutes with the signed differential of the integer
shift. The ringed-site formulation is transported along the internal-module equivalence
for the identical coefficient sheaf and evaluation pairing. Rank zero and empty schemes
are included. There is no assertion about colimits or exactness in this conclusion. -/
theorem condensed_finite_free_hom_evaluation
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ X)).obj P))
    (n : ℤ) : Nonempty
      (DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
          preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj P)) ≅
        (Mod.ihom P).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
          (condensedModuleSections Λ X).rightDerivedFunctor ⋙
            DerivedCategory.homologyFunctor _ n) := by
  sorry

end AlgebraicGeometry.ProEtale
