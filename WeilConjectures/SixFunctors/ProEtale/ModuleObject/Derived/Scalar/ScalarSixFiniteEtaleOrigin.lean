/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import all WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism

/-! # Finite scalar realization from the étale site

Source: blueprint scalar-six-ctf (1), finite coefficient comparison.
(blueprint: lem-sfb-finite-scalar-etale-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [DiscreteTopology A] [Finite A]
  {Λ : ScalarSixRing.{u}}
  (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]

/-- Exact étale inverse image, the existing constant-ring realization, and restriction
along the given condensed coefficient isomorphism. All three functors are specified
constructions; no constructible preimage is chosen in this definition.
Source: blueprint scalar-six-ctf (1), finite discrete comparison and transport along e.
(blueprint: lem-sfb-finite-scalar-etale-origin). -/
abbrev sfbFiniteScalarRealization (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1} A) T ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X T) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory ⋙
    (finiteComparisonRealization A T eR).mapDerivedCategory ⋙
      shriekCoefficientTransport e.symm T

/-- Étale descent retains bounded constructibility and finite Tor amplitude under the
specified small-ring finite scalar realization.

Source: blueprint scalar-six-ctf (1), coefficient comparison before flat-model generation;
Bhatt--Scholze, Proposition 5.3.2 and Corollary 5.1.6.
(blueprint: lem-sfb-finite-scalar-etale-origin).

Proof: Restrict K along the inverse of e. The coefficient-isomorphism constructibility
lemma preserves its finite constant models, cohomological bounds and finite Tor interval.
Invert the exact constant-ring module equivalence. Finite matrix presentations identify
constant scalar models with finite ordinary modules on the same constructible strata;
exactness and the monoidal comparison identify homology and every Tor interval. Over a
finite ring the resulting ordinary bounded constructible complex descends to the étale
site: descend its constructible cohomology sheaves and successively its truncation
triangles using full faithfulness of the bounded-below comparison. The existing Tor
comparison reflects the same interval. Compose the counit of the module equivalence,
the descent isomorphism, and the inverse coefficient-transport isomorphism. No
characteristic assumption is used. The zero ring and empty scheme descend in the same
way. -/
theorem sfbFiniteScalarEtaleOrigin
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1} A) X.left,
      finiteComparisonEtaleGenerators A X.left L ∧
      Nonempty ((sfbFiniteScalarRealization A e eR X.left).obj L ≅ K.obj) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let H := finiteComparisonRealization A X.left eR
  let : H.IsEquivalence := (finiteComparisonRealization_exact A X.left eR).1
  let F := H.mapDerivedCategory
  let : F.IsEquivalence := Functor.isEquivalence_mapDerivedCategory H
  let C := (shriekCoefficientTransport e X.left).obj K.obj
  let M := F.objPreimage C
  let i : F.obj M ≅ C := F.objObjPreimageIso C
  have hC : shriekCoefficientCtf
      (Λ := Profinite.continuousMapRingObj.{u} A) X.left C :=
    (shriekCoefficientIso_transport e X.left).2.2.2.1 K.obj |>.mpr K.property
  let : (shriekCoefficientCtf
      (Λ := Profinite.continuousMapRingObj.{u} A) X.left).IsClosedUnderIsomorphisms :=
    ctf_replete X.left
  have hM : finiteComparisonProEtaleGenerators A eR X.left M :=
    (shriekCoefficientCtf (Λ := Profinite.continuousMapRingObj.{u} A) X.left).prop_of_iso
      i.symm hC
  obtain ⟨L, hL, ⟨j⟩⟩ :=
    (finiteComparisonGenerators_identification A eR X.left).2 M hM
  refine ⟨L, hL, ⟨?_⟩⟩
  exact (shriekCoefficientTransport e.symm X.left).mapIso (F.mapIso j ≪≫ i) ≪≫
    (transportCompIso e X.left).app K.obj

end AlgebraicGeometry.ProEtale.CondensedRing
