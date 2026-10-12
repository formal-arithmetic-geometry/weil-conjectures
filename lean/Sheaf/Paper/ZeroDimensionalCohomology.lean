/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Artinian
import Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest

/-! # Étale cohomology in dimension zero

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-zero-dimensional-cohomology.md
(blueprint: lem-weil-pbc-zero-dimensional-cohomology).
-/

@[expose] public section


universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The underlying point type of a separated finite-type zero-dimensional scheme
over an algebraically closed field is finite.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, finiteness clause;
Stacks Project, Tag 00KH (blueprint: zero-dimensional-etale-finite).

Proof: By LocallyOfFiniteType.isLocallyNoetherian f, C is locally Noetherian. By
QuasiCompact.compactSpace_of_compactSpace f, C is compact.
IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim makes C locally Artinian and hence discrete.
Therefore finite_of_compact_of_discrete proves Finite C (node lem-weil-pbc-finite-type-dim-zero-
artinian).
-/
theorem zero_dimensional_etale_finite
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0) : Finite C := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyArtinian C := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  exact finite_of_compact_of_discrete

/-- Étale cohomology of a separated finite-type zero-dimensional scheme over an
algebraically closed field is a finite product of geometric stalks in degree zero
and vanishes in positive degrees.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, node lem-weil-pbc-zero-dimensional-cohomology,
order 1002; Stacks Project, Tags 03QT, 03QU, 03SI and 0A5B.
(blueprint: lem-weil-pbc-zero-dimensional-cohomology).

Proof: Pair `zero_dimensional_etale_finite`, obtained directly from Mathlib's Artinian
and compact-discrete finiteness results, with
`zero_dimensional_etale_cohomology_rest`. The latter reduces the scheme to a finite
coproduct of Spec k, computes its cohomology, transports it across the reduction
universal homeomorphism, and identifies the canonical stalk germs. The fields of
chosen geometric points may be arbitrary algebraically closed fields.
-/
theorem zero_dimensional_etale_cohomology
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    Finite C ∧
    (∀ q : ℕ, 0 < q → Subsingleton
      ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
        ((DerivedCategory.singleFunctor
          (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsIso
        ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫
          Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  exact ⟨zero_dimensional_etale_finite k C f hdim,
    zero_dimensional_etale_cohomology_rest k C f hdim F Ω s hs⟩

end AlgebraicGeometry
