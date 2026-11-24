/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityDatum
import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumTransportDiagonal
import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumTransportCocycle
/-! # Identity and cocycle of compatible natural transport -/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
/-- Naturality and compatibility force the diagonal and cocycle identities of the transport. -/
theorem finiteLocalModels_descentDatum_compatibility_transport
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (t : FiniteLocalModelCompatibleTransport T E U Q e) :
    (∀ (W : Scheme.{u}) (a : W ⟶ U.left) (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      t.transport a a rfl x = x) ∧
    (∀ (W : Scheme.{u}) (a b c : W ⟶ U.left)
      (hab : a ≫ U.hom = b ≫ U.hom) (hbc : b ≫ U.hom = c ≫ U.hom)
      (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      t.transport b c hbc (t.transport a b hab x) =
        t.transport a c (hab.trans hbc) x) := by
  constructor
  · exact finiteLocalModels_descentDatum_compatibility_transport_diagonal T E U Q e t
  · exact finiteLocalModels_descentDatum_compatibility_transport_cocycle T E U Q e t
end AlgebraicGeometry.Scheme
