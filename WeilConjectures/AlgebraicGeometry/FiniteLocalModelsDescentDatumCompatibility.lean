/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityTransport
/-!
# Compatible transport on an etale local representative

## References

* Stacks Project, Tag 03RV and Descent Tag 02W5
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
/-- A representation on the localized small site induces compatible scheme descent data
(Stacks, Tags 03RV, 02W5). -/
theorem finiteLocalModels_descentDatum_compatibility
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale)
    (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    ∃ d : Over.DescentDatum U.hom (Over.mk Q.obj.hom),
      ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
        (d.transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
            (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
          ((e.hom.app (op (Over.mk b))) s).down.left := by
  obtain ⟨t⟩ := finiteLocalModels_descentDatum_compatibility_datum T E U Q e
  obtain ⟨hself, hcomp⟩ := finiteLocalModels_descentDatum_compatibility_transport T E U Q e t
  let d : Over.DescentDatum U.hom (Over.mk Q.obj.hom) :=
    { transport := t.transport
      transport_homMk_comp := t.naturality
      transport_self := fun a x ↦ hself _ a x
      transport_transport := fun a b c hab hbc x ↦ hcomp _ a b c hab hbc x }
  exact ⟨d, t.compatibility⟩
end AlgebraicGeometry.Scheme
