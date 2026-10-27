/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ProEtaleCoefficientPullback
public import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
public import Sheaf.Paper.ProEtaleCoefficientTensorIsoNaturality

/-! # The normalized chain tensor isomorphism for coefficient restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The normalized chain tensor isomorphism supplied by ring-isomorphism transport.
(blueprint: def-pbc-coefficient-restriction-tensor-iso) -/
def tensorIso (o : SheafOfModules.RingIsoTensorTransport
    (J := ProEt.topology X)
    (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c) :
    total X S ⋙ (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ) ≅
      (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).prod
        ((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ))) ⋙
        total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  NatIso.ofComponents (fun Z ↦ o.totalIso Z.1 Z.2)
    (fun v ↦ tensorIso_naturality f R S c o _ _ v)

/-- The normalized tensor isomorphism has the prescribed map on every total summand.
Source: RingIsoTensorTransport.total_summand; Stacks Tag 07A4.
(blueprint: def-pbc-coefficient-restriction-tensor-iso)

Proof: the isomorphism is built from the supplied totalIso components. Substitute
that definition and apply the given summand normalization. This is an equation of
actual total complexes, including zero complexes and the identity coefficient map. -/
theorem tensorIso_summand
    (o : SheafOfModules.RingIsoTensorTransport (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (P Q : CochainComplex (proEtaleRingModules X S) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    (pbcRestrict c.hom).map
        (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor X S) a b n h) ≫
        ((tensorIso f R S c o).hom.app (P, Q)).f n =
      o.monoidal.toMonoidal.toOplaxMonoidal.δ (P.X a) (Q.X b) ≫
        CochainComplex.ιMapBifunctor
          (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).obj P)
          (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).obj Q)
          (proEtaleOrdinaryTensor X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
          a b n h := by
  simpa only [tensorIso, NatIso.ofComponents_hom_app] using o.total_summand P Q a b n h

end AlgebraicGeometry.Scheme.CoefficientTensorChain
