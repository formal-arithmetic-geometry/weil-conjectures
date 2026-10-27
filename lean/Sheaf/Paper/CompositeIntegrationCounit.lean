/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.CompositeIntegrationOperations
import Sheaf.Paper.NativeIntegrationContraction
import Sheaf.Paper.NativeIntegrationProjectionLaws

/-! # Coefficient factorization of the composite integration counit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityIntegration

section Calculation

variable {C E T : Type w} [Category.{v} C] [Category.{v} E] [Category.{v} T]
  [MonoidalCategory C] [MonoidalCategory E] [MonoidalCategory T]
  [BraidedCategory C] [BraidedCategory E] [BraidedCategory T]
  {o : CompositeOperations C E T}

private theorem inverse_projection_comp (d : CompositeIntegrationData o)
    (M : C) (K : T) (hM : d.domainX M) (hK : d.domainZ K) :
    o.fg.F.map (M ◁ (o.pullComp.app K).inv) ≫
      (o.alpha (M ⊗ o.f.P.obj (o.g.P.obj K))
        (d.origin _ (d.tensor_f _ _ hM (d.pull_g K hK)))).inv ≫
      o.g.F.map (q o.f M (o.g.P.obj K) (d.pf_f _ _ hM (d.pull_g K hK))) ≫
      q o.g (o.f.F.obj M) K (d.pf_g _ _ (d.af.push_closed _ hM) hK) =
      q o.fg M K (d.pf_fg _ _ hM hK) ≫ (o.alpha M (d.origin M hM)).inv ▷ K := by
  let := d.pf_f M (o.g.P.obj K) hM (d.pull_g K hK)
  let := d.pf_g (o.f.F.obj M) K (d.af.push_closed M hM) hK
  let := d.pf_fg M K hM hK
  have h : whiskerRightIso (o.alpha M (d.origin M hM)) K ≪≫
      asIso (o.fg.pf M K) =
      asIso (o.g.pf (o.f.F.obj M) K) ≪≫
        o.g.F.mapIso (asIso (o.f.pf M (o.g.P.obj K))) ≪≫
        o.alpha (M ⊗ o.f.P.obj (o.g.P.obj K))
          (d.origin _ (d.tensor_f _ _ hM (d.pull_g K hK))) ≪≫
        o.fg.F.mapIso (whiskerLeftIso M (o.pullComp.app K)) := by
    apply Iso.ext
    exact d.projection_comp M K hM hK
  simpa only [Iso.trans_inv, Functor.mapIso_inv, asIso_inv,
    whiskerRightIso_inv, whiskerLeftIso_inv, q, Category.assoc] using
      (congrArg Iso.inv h).symm

private theorem coefficientCounit_eq (p : IntegrationOperations C T) (L : C)
    (t : p.F.obj L ⟶ 𝟙_ T) (K : T) (hK : IsIso (p.pf L K)) :
    coefficientCounit p L t K hK =
      p.F.map (β_ (p.P.obj K) L).hom ≫ q p L K hK ≫
        (t ▷ K) ≫ (λ_ K).hom := by
  unfold coefficientCounit
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

private theorem formula_of_calculations (d : CompositeIntegrationData o)
    (hc : PrecompositorContraction o) (hp : IntegrationProjectionLaws o.fg) :
    d.CounitFormula := by
  have hf (K : T) (hK : d.domainZ K) : d.compositeCounit K hK =
      coefficientCounit o.fg (compositeTwist o d.Lf d.Lg)
        d.compositeTrace K (d.pf_fg _ K d.mem_fg hK) := by
    rw [coefficientCounit_eq, hc d K hK]
    have hi := inverse_projection_comp d (d.Lf ⊗ o.f.P.obj d.Lg) K d.mem_fg hK
    dsimp only [compositeTwist] at *
    rw [reassoc_of% hi]
    simp only [CompositeIntegrationData.compositeTrace, compositeTwist,
      comp_whiskerRight, Category.assoc]
  refine ⟨hf, ?_, ?_⟩
  · rw [hf, coefficientCounit_eq]
    rw [reassoc_of% (hp.2 _ (d.pf_fg _ _ d.mem_fg d.unitZ))]
    rw [← rightUnitor_inv_naturality_assoc, unitors_equal]
    simp only [Iso.inv_hom_id, Category.comp_id]
  · intro K K' hK hK' h
    rw [hf, hf, coefficientCounit_eq, coefficientCounit_eq]
    simp only [tensorHom_id, Category.assoc]
    rw [← o.fg.F.map_comp_assoc, BraidedCategory.braiding_naturality_left,
      o.fg.F.map_comp, Category.assoc]
    rw [reassoc_of% (hp.1 _ K K' h
      (d.pf_fg _ _ d.mem_fg hK) (d.pf_fg _ _ d.mem_fg hK'))]
    rw [whisker_exchange_assoc, leftUnitor_naturality]

end Calculation

/-- Coefficient factorization of the actual composite twisted-pullback counit, at both
sites, including its tensor-unit value and naturality on the supplied domain.
Source: blueprint main-20261015, lem-pur-projection-purity-agreement.proof.md, expanded
Step 6, final canonical-reassociation paragraph; Stacks Project, Tag 0DV0
(blueprint: lem-pur-composite-integration-counit).

Proof, following all seven steps of the node:
1. Expand `Adjunction.comp`: its counit is F_g(epsilon_f) followed by epsilon_g. Use the
canonical symmetry to put both twists first, and use the pullback/tensor comparison and
associator to identify the inner source with L_gf tensor P_f P_g K.
2. Invert the supplied action identity for f at (L_f,L_g,P_g K). Put
`a = q_f(L_f,L_g) ≫ (t_f ▷ L_g) ≫ lambda`. Substitution of the given f-counit formula
then gives `epsilon_f = q_f(L_gf,P_g K) ≫ (a ▷ P_g K)`, with the source constraints.
3. Substitute this and the given g-counit formula into the actual composite counit.
Functoriality of F_g produces the three factors q_f, F_g(a tensor 1), and q_g.
4. Naturality of the inverse projection in its first variable moves F_g(a) through q_g.
Bifunctoriality combines the remaining trace factors into t_g composed with F_g(a).
5. Invert the assumed projection/compositor identity and cancel its invertible factors.
It replaces q_g composed with F_g(q_f) and alpha inverse by q_gf followed by
alpha inverse tensor identity. The remaining trace is precisely `compositeTrace`.
Insert the two canonical symmetries to recover the requested order `(1_K tensor t) Pi`.
6. At the tensor unit the action identity says q=q squared after the canonical unit
constraints. Since q is invertible it is the identity. The formula is consequently
the stated equality of the unit counit and the four-arrow composite trace.
7. Naturality of the actual counits and compositor, inverse-projection naturality,
and tensor functoriality give the displayed square for every domain morphism.
The calculation uses only the supplied identities. `b=false` repeats it on the ordinary
etale site's actual maps; `b=true` uses the canonical pro-etale origin compositor.
-/
theorem compositeIntegrationCounit
    (b : Bool) (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of P.field.k))]
    [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [IsSeparated g] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    : integrationCounitAssertion b P.Coefficient f g := by
  have hc := nativePrecompositorContraction b P.Coefficient f g
  have hp := nativeIntegrationProjectionLaws b P.Coefficient f g
  cases b with
  | false =>
    let := nativeBraiding (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    let := nativeBraiding (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    let := nativeBraiding (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    exact fun d ↦ formula_of_calculations d hc hp
  | true =>
    let := nativeBraiding (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    let := nativeBraiding (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))
    let := nativeBraiding (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient))
    exact fun d ↦ formula_of_calculations d hc hp

end WeilConjectures.PurityIntegration
