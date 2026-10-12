/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.AlgebraicGeometry.GlobalDerivedHom

/-! # Derived global sections preserves quasi-coherent coproducts. -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Derived global sections takes an ambient coproduct of quasi-coherent complexes
on a qcqs scheme to a coproduct in the derived module category.
Source: Stacks Project, Tag 09M1, first paragraph of the proof.
(blueprint: lem-pc-derived-global-sections-preserves-coproducts)
Proof: Map X to Spec(ULift ℤ). This morphism is qcqs, so derived direct image
preserves the given coproduct and takes each summand into D_QCoh of that affine.
The affine derived equivalence identifies its inverse with derived global sections
with scalars restricted to ULift ℤ. Equivalences preserve coproducts. The comparison
of derived global sections after pushforward with global sections on X is obtained
on K-injective resolutions, using the equality of underived global sections.
This yields the canonical coproduct comparison after restricting scalars from
O_X(X) to ULift ℤ. Restriction of scalars preserves and reflects coproducts of
module complexes: sums are formed on the underlying abelian groups, their ring
operations act componentwise, and cohomology detects isomorphisms in the derived
category. Thus the comparison before restriction is an isomorphism too, so the
mapped cofan is colimiting. Naturality of the resolution and scalar comparisons
identifies its legs with the actual maps of derived global sections. The argument
includes the empty family and unbounded complexes. -/
theorem derivedGlobalSections_preserves_coproducts (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let G := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor
    ∀ (I : Type u) (E : I → schemeDerivedQCohCategory X)
      (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S),
      IsColimit (Cofan.mk S ι) →
      Nonempty (IsColimit (Cofan.mk (G.obj S) (fun i ↦ G.map (ι i)))) := by sorry

end AlgebraicGeometry
