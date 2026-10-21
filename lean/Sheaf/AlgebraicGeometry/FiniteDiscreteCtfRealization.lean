/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Reflection of finite discrete constructibility by coefficient realization

Source: blueprint main-20261015, finite-discrete coefficient identification in
`sk-prop-ctf-finite-compact-proetale.proof.md`
(blueprint: lem-finite-discrete-ctf-realization).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- The specified finite discrete coefficient realization reflects bounded
constructibility and finite Tor amplitude into ordinary fixed-scalar sheaves.

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-ctf-finite-compact/sk-prop-ctf-finite-compact-proetale.proof.md`, first paragraph;
`sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md`, coefficient
identification step (blueprint: lem-finite-discrete-ctf-realization).

Proof. The existing finiteComparisonRealization_exact identifies realization as an
exact equivalence, so it reflects boundedness. Since a Noetherian scheme is qcqs,
finiteComparisonGenerators_identification supplies an etale bounded constructible
finite-Tor complex L whose ordinary pro-etale comparison image is isomorphic to K.
For each cohomology object, convert the etale finite-constant-model predicate into
IsConstructibleSheaf, apply constructibility preservation by comparison inverse image,
and transport along the exact-functor homology isomorphism and the isomorphism to K.
Finally comparison inverse image preserves each Tor interval by
ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory; transport the resulting
interval along the same isomorphism. These arguments also cover the empty scheme and
the zero ring. -/
theorem finiteDiscreteCtfRealization
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
        Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X ⊓
      fun M ↦ DerivedCategory.finiteTorAmplitude _ M)
        ((finiteComparisonRealization A X eR).mapDerivedCategory.obj K)) :
    (DerivedCategory.TStructure.t.bounded K ∧
      ∀ q : ℤ, IsConstructible (ULift.{u + 1} A)
        ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
      DerivedCategory.finiteTorAmplitude _ K := by
  let F := finiteComparisonRealization A X eR
  let N := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let : F.IsEquivalence := (finiteComparisonRealization_exact A X eR).1
  obtain ⟨L, hL, ⟨e⟩⟩ := (finiteComparisonGenerators_identification A eR X).2 K hK
  refine ⟨⟨F.bounded_of_bounded_mapDerivedCategory_obj hK.1.1, ?_⟩, ?_⟩
  · intro q
    have : Scheme.IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ q).obj L) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hL.1.1 q)
    exact isConstructible_of_iso
      ((N.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e)
      (isConstructible_comparisonUpperStar_obj _)
  · obtain ⟨a, b, hab⟩ := hL.2
    exact ⟨a, b, (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e
      (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory
        (ULift.{u + 1} A) hab)⟩

end AlgebraicGeometry.ProEtale
