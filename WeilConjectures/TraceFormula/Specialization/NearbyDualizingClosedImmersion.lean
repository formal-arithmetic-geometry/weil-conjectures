/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF

/-!

# The dualizing maps along a proper morphism of trait models: the formal inputs

Let `D` be a family of dualizing maps of nearby cycles over generic bases
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`), and `i : Z' ⟶ Z` a morphism of proper
trait models over a generic base, over proper morphisms `i₁ : Y₁ ⟶ X₁` (generic) and
`i₂ : Y' ⟶ X'` (special), e.g. a closed immersion of trait models. Let
`ν_i : Ri₂_! Ψ_{Z'} ⟶ Ψ_Z Ri₁_!` invert the proper exchange `χ_i` under `Ri_! ≅ Ri_*`, and
`β_i : Ψ_{Z'} Ri₁^! ⟶ Ri₂^! Ψ_Z` be its exceptional adjoint
(`ProEtale.CondensedRing.exceptionalExchange`). The closed-immersion law of blueprint
`sk-lem-tf-nearby-mate-coherences` (4) (`det-tf-nearby-duality-slice`, "the map `θ`") is
```
θ_{Z'} ∘ Ψ_{Z'}(ρ) = ρ' ∘ Ri₂^!(θ_Z) ∘ β_i(ω_{X₁})
```
for the composition isomorphisms `ρ : Ri₁^! ω_{X₁} ≅ ω_{Y₁}`, `ρ' : Ri₂^! ω_{X'} ≅ ω_{Y'}`. Both
sides are maps to the dualizing complex of the proper `Y'`, hence determined by their traces
(`NearbyCyclesModel.eq_of_map_comp_trace_eq`), and the traces are compared after the invertible
proper exchange `χ_{Z'}`. This file provides the ingredients of that comparison:

* the counit of a composite adjunction through conjugate composition isomorphisms
  (`CategoryTheory.Adjunction.map_conjugateIsoEquiv_inv_app_comp_counit_app`), and the abstract
  composition of traces
  (`CategoryTheory.map_conjugateIsoEquiv_inv_app_comp_inv_app_comp_counit_app`);
* the composition of traces `tr_Y ∘ Rb_*(ρ) = tr_X ∘ Ra_*(Ri_* Ri^! ω_X ⟶ ω_X)` for
  `b = i ≫ a` proper
  (`ProEtale.CondensedRing.lowerStar_map_upperShriekUnitCompOfEq_hom_comp_counit`)
  and the naturality of the trace of `i`
  (`ProEtale.CondensedRing.lowerStar_map_upperShriek_map_comp_counit`);
* the exceptional adjunction defining `β_i`: `ε_{i₂} ∘ Ri₂_*(β_i) ∘ χ_i = Ψ_Z(ε_{i₁})`
  (`CategoryTheory.app_comp_map_mateEquiv_app_comp_inv_app_comp_counit_app`);
* the diagram chase assembling these with the trace identities of `θ_Z`, `θ_{Z'}` and the
  composition law of the proper exchanges (`CategoryTheory.closedImmersionLaw_aux`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section Abstract

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- The counit of a composite adjunction through a conjugate composition isomorphism: if
`u : Rb ≅ Ra ⋙ Ri` is the conjugate of `c : Lb ≅ Li ⋙ La`, the counit of `Lb ⊣ Rb` after
`Lb(u⁻¹)` is `c` followed by the counits of `Li ⊣ Ri` and `La ⊣ Ra`. -/
lemma Adjunction.map_conjugateIsoEquiv_inv_app_comp_counit_app {Li : C ⥤ D} {Ri : D ⥤ C}
    {La : D ⥤ E} {Ra : E ⥤ D} {Lb : C ⥤ E} {Rb : E ⥤ C} (adji : Li ⊣ Ri) (adja : La ⊣ Ra)
    (adjb : Lb ⊣ Rb) (c : Lb ≅ Li ⋙ La) (N : E) :
    Lb.map ((conjugateIsoEquiv adjb (adji.comp adja) c.symm).inv.app N) ≫ adjb.counit.app N =
      c.hom.app _ ≫ La.map (adji.counit.app (Ra.obj N)) ≫ adja.counit.app N := by
  have := conjugateEquiv_counit (adji.comp adja) adjb c.hom N
  rw [Adjunction.comp_counit_app] at this
  exact this

/-- **Composition of traces, abstractly**: for adjunctions `Li ⊣ Ri`, `La ⊣ Ra`, `Lb ⊣ Rb`, a
composition isomorphism `c : Lb ≅ Li ⋙ La` with conjugate `u : Rb ≅ Ra ⋙ Ri`, and identifications
`e : L ≅ S` of the left adjoints with functors `S` compatible with `c` and a composition
isomorphism `s : Si ⋙ Sa ≅ Sb`, the "trace" `Sb Rb N ≅ Lb Rb N ⟶ N` after `Sb(u⁻¹)` is the
composite of the traces of `Si` and `Sa`. -/
lemma map_conjugateIsoEquiv_inv_app_comp_inv_app_comp_counit_app {Li : C ⥤ D} {Ri : D ⥤ C}
    {La : D ⥤ E} {Ra : E ⥤ D} {Lb : C ⥤ E} {Rb : E ⥤ C} (adji : Li ⊣ Ri) (adja : La ⊣ Ra)
    (adjb : Lb ⊣ Rb) (c : Lb ≅ Li ⋙ La) {Si : C ⥤ D} {Sa : D ⥤ E} {Sb : C ⥤ E} (ei : Li ≅ Si)
    (ea : La ≅ Sa) (eb : Lb ≅ Sb) (s : Si ⋙ Sa ≅ Sb)
    (hcomp : ∀ K, c.hom.app K ≫ ea.hom.app (Li.obj K) ≫ Sa.map (ei.hom.app K) =
      eb.hom.app K ≫ s.inv.app K) (N : E) :
    Sb.map ((conjugateIsoEquiv adjb (adji.comp adja) c.symm).inv.app N) ≫ eb.inv.app _ ≫
        adjb.counit.app N =
      s.inv.app _ ≫ Sa.map (ei.inv.app _ ≫ adji.counit.app (Ra.obj N)) ≫ ea.inv.app _ ≫
        adja.counit.app N := by
  have hc : eb.inv.app (Ri.obj (Ra.obj N)) ≫ c.hom.app _ =
      s.inv.app _ ≫ Sa.map (ei.inv.app _) ≫ ea.inv.app _ := by
    rw [← cancel_mono (ea.hom.app _), ← cancel_mono (Sa.map (ei.hom.app _))]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, ← Sa.map_comp,
      CategoryTheory.Functor.map_id]
    rw [hcomp, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  have hn := eb.inv.naturality ((conjugateIsoEquiv adjb (adji.comp adja) c.symm).inv.app N)
  have hn' := ea.inv.naturality (adji.counit.app (Ra.obj N))
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn hn' ⊢
  rw [reassoc_of% hn, Adjunction.map_conjugateIsoEquiv_inv_app_comp_counit_app,
    reassoc_of% hc, Functor.map_comp, Category.assoc, reassoc_of% hn']

end Abstract

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Trace

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y P : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

end Trace

end AlgebraicGeometry.ProEtale.CondensedRing
