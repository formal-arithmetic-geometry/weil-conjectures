/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Functoriality of the strict henselization

Let `g : T ⟶ S` be a morphism of schemes and `t : Spec Ω ⟶ T` a geometric point, so that
`t ≫ g` is a geometric point of `S`. We construct the local homomorphism
`h : 𝒪^{sh}_{S, t ≫ g} ⟶ 𝒪^{sh}_{T, t}` of strict henselizations
(`AlgebraicGeometry.Scheme.strictHenselizationMap g t`): it is the unique ring homomorphism such
that `Spec h` is compatible with the structure morphisms to `S` and `T` and `h` is compatible with
the evaluations at the geometric points. For an affine pointed étale neighbourhood `(V, v)` of
`t ≫ g`, the composite `S_(t) ⟶ T_(t ≫ g) ⟶ V` is the unique morphism `T_(t) ⟶ V` over `S`
through which `v` factors (`strictLocalizationLift`); in particular it agrees with
`T_(t) ⟶ W ⟶ V` for every affine pointed étale neighbourhood `(W, w)` of `t` mapping to `V`.

The key input is `AlgebraicGeometry.existsUnique_lift_of_etale`: morphisms from the spectrum of a
strictly henselian local ring `R` lift uniquely along étale morphisms through prescribed points
over the closed point.

## Main definitions

- `AlgebraicGeometry.Scheme.strictLocalizationLift g t x`: the morphism `T_(t) ⟶ V` over `S`.
- `AlgebraicGeometry.Scheme.strictHenselizationMap g t`: the map `𝒪^{sh}_{S,t ≫ g} ⟶ 𝒪^{sh}_{T,t}`.

## Main results

- `AlgebraicGeometry.Scheme.existsUnique_strictHenselizationMap`: clause 3 of the blueprint.
- `AlgebraicGeometry.Scheme.strictLocalizationCone_π_app_comp_eq`: clause 4 of the blueprint.

## References

- Stacks Project, Lemma 59.33.1 and Definition 59.33.4,
  <https://stacks.math.columbia.edu/tag/04HX>, <https://stacks.math.columbia.edu/tag/03PS>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing

namespace AlgebraicGeometry

/-- **Lifting along étale morphisms over a strictly henselian local ring.** Let `R` be a strictly
henselian local ring, `e : R ⟶ K` a ring map to a field with kernel the maximal ideal, `f : V ⟶ S`
an étale morphism, `ψ : Spec R ⟶ S` a morphism and `v : Spec K ⟶ V` a lift of
`Spec e ≫ ψ` along `f`. Then there is exactly one `φ : Spec R ⟶ V` with `φ ≫ f = ψ` and
`Spec e ≫ φ = v`.

(blueprint: `lem-weil-pbc-map-into-henselian-colimit`) -/
theorem existsUnique_lift_of_etale {R : CommRingCat.{u}} [IsStrictlyHenselianLocalRing R]
    {K : Type u} [Field K] (e : R ⟶ CommRingCat.of K)
    (he : RingHom.ker e.hom = maximalIdeal R) {S V : Scheme.{u}} (f : V ⟶ S) [Etale f]
    (ψ : Spec R ⟶ S) (v : Spec (.of K) ⟶ V) (hv : v ≫ f = Spec.map e ≫ ψ) :
    ∃! φ : Spec R ⟶ V, φ ≫ f = ψ ∧ Spec.map e ≫ φ = v :=
  sorry

namespace Scheme

variable {S T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (g : T ⟶ S)
  (t : Spec (.of Ω) ⟶ T)

instance (s : Spec (.of Ω) ⟶ S) : IsStrictlyHenselianLocalRing (strictHenselization s) :=
  ⟨inferInstance⟩

lemma strictLocalizationLift_aux (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    ∃! φ : strictLocalization t ⟶ x.obj.1.left,
      φ ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g ∧
        Spec.map (strictHenselizationEval t) ≫ φ = x.obj.2.left := by
  have : Etale x.obj.1.hom := x.obj.1.prop
  refine existsUnique_lift_of_etale (strictHenselizationEval t)
    (maximalIdeal_strictHenselization (s := t)).symm _ _ _ ?_
  refine (CategoryTheory.Over.w x.obj.2).trans ?_
  rw [← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
  rfl

/-- For an affine pointed étale neighbourhood `(V, v)` of `t ≫ g`, the unique morphism
`T_(t) ⟶ V` over `S` (via `T_(t) ⟶ T ⟶ S`) through which `v` factors as
`Spec Ω ⟶ T_(t) ⟶ V`. -/
noncomputable def strictLocalizationLift (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    strictLocalization t ⟶ x.obj.1.left :=
  (strictLocalizationLift_aux g t x).exists.choose

@[reassoc]
lemma strictLocalizationLift_comp_hom (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    strictLocalizationLift g t x ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g :=
  (strictLocalizationLift_aux g t x).exists.choose_spec.1

@[reassoc]
lemma spec_map_strictHenselizationEval_comp_strictLocalizationLift
    (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    Spec.map (strictHenselizationEval t) ≫ strictLocalizationLift g t x = x.obj.2.left :=
  (strictLocalizationLift_aux g t x).exists.choose_spec.2

/-- Uniqueness of `strictLocalizationLift`. -/
lemma eq_strictLocalizationLift (x : AffinePointedEtaleNeighborhood (t ≫ g))
    (φ : strictLocalization t ⟶ x.obj.1.left)
    (h₁ : φ ≫ x.obj.1.hom = strictLocalizationToBase t ≫ g)
    (h₂ : Spec.map (strictHenselizationEval t) ≫ φ = x.obj.2.left) :
    φ = strictLocalizationLift g t x :=
  (strictLocalizationLift_aux g t x).unique ⟨h₁, h₂⟩
    ⟨strictLocalizationLift_comp_hom g t x,
      spec_map_strictHenselizationEval_comp_strictLocalizationLift g t x⟩

/-- The local homomorphism `𝒪^{sh}_{S,t ≫ g} ⟶ 𝒪^{sh}_{T,t}` of strict henselizations induced
by `g : T ⟶ S`.

(blueprint: `lem-weil-pbc-strict-henselization-functoriality`) -/
noncomputable def strictHenselizationMap :
    strictHenselization (t ≫ g) ⟶ strictHenselization t :=
  colimit.desc (strictHenselizationDiagram (t ≫ g))
    { pt := strictHenselization t
      ι :=
        { app x := Scheme.Γ.map (strictLocalizationLift g t x.unop).op ≫
            (Scheme.ΓSpecIso (strictHenselization t)).hom
          naturality x y f := by
            have h : strictLocalizationLift g t y.unop ≫ f.unop.hom.1.left =
                strictLocalizationLift g t x.unop := by
              refine eq_strictLocalizationLift g t _ _ ?_ ?_
              · rw [Category.assoc, ← strictLocalizationLift_comp_hom g t y.unop]
                congr 1
                exact f.unop.hom.1.w.trans (Category.comp_id _)
              · rw [spec_map_strictHenselizationEval_comp_strictLocalizationLift_assoc]
                exact congrArg CommaMorphism.left f.unop.hom.2
            change Scheme.Γ.map f.unop.hom.1.left.op ≫ Scheme.Γ.map _ ≫ _ =
              (Scheme.Γ.map _ ≫ _) ≫ 𝟙 _
            rw [Category.comp_id, ← h, op_comp, Scheme.Γ.map_comp, Category.assoc] } }

/-- The composite `T_(t) ⟶ S_(t ≫ g) ⟶ V` is `strictLocalizationLift g t x`. -/
@[reassoc]
lemma spec_map_strictHenselizationMap_comp_strictLocalizationCone_π_app
    (x : AffinePointedEtaleNeighborhood (t ≫ g)) :
    Spec.map (strictHenselizationMap g t) ≫ (strictLocalizationCone (t ≫ g)).π.app x =
      strictLocalizationLift g t x :=
  sorry

/-- `Spec` of the strict henselization map is compatible with the structure morphisms:
`j_S ∘ Spec h = g ∘ j_T`.

(blueprint: `lem-weil-pbc-strict-henselization-functoriality`) -/
@[reassoc]
lemma spec_map_strictHenselizationMap_comp_strictLocalizationToBase :
    Spec.map (strictHenselizationMap g t) ≫ strictLocalizationToBase (t ≫ g) =
      strictLocalizationToBase t ≫ g :=
  sorry

/-- The strict henselization map is compatible with the evaluations at the geometric points,
i.e. it induces the inclusion of residue fields inside `Ω`.

(blueprint: `lem-weil-pbc-strict-henselization-functoriality`) -/
@[reassoc (attr := simp)]
lemma strictHenselizationMap_comp_strictHenselizationEval :
    strictHenselizationMap g t ≫ strictHenselizationEval t = strictHenselizationEval (t ≫ g) :=
  sorry

/-- The strict henselization map is a local homomorphism.

(blueprint: `lem-weil-pbc-strict-henselization-functoriality`) -/
instance isLocalHom_strictHenselizationMap : IsLocalHom (strictHenselizationMap g t).hom :=
  sorry

/-- **Functoriality of the strict henselization** (clause 3): the strict henselization map is the
unique (local) ring homomorphism `h : 𝒪^{sh}_{S,t ≫ g} ⟶ 𝒪^{sh}_{T,t}` with
`j_S ∘ Spec h = g ∘ j_T` inducing the inclusion of residue fields inside `Ω`.

(blueprint: `lem-weil-pbc-strict-henselization-functoriality`) -/
theorem existsUnique_strictHenselizationMap :
    ∃! h : strictHenselization (t ≫ g) ⟶ strictHenselization t,
      IsLocalHom h.hom ∧
      Spec.map h ≫ strictLocalizationToBase (t ≫ g) = strictLocalizationToBase t ≫ g ∧
      h ≫ strictHenselizationEval t = strictHenselizationEval (t ≫ g) :=
  sorry

/-- **Compatibility of the strict henselization map with neighbourhoods** (clause 4): if `(V, v)`
is an affine pointed étale neighbourhood of `t ≫ g`, `(W, w)` one of `t` and `w : W ⟶ V` is
compatible with the structure morphisms and the points, then `T_(t) ⟶ W ⟶ V` equals
`T_(t) ⟶ S_(t ≫ g) ⟶ V`.

(blueprint: `lem-weil-pbc-strict-henselization-functoriality`) -/
theorem strictLocalizationCone_π_app_comp_eq (x : AffinePointedEtaleNeighborhood (t ≫ g))
    (y : AffinePointedEtaleNeighborhood t) (w : y.obj.1.left ⟶ x.obj.1.left)
    (hw : w ≫ x.obj.1.hom = y.obj.1.hom ≫ g) (hpt : y.obj.2.left ≫ w = x.obj.2.left) :
    (strictLocalizationCone t).π.app y ≫ w =
      Spec.map (strictHenselizationMap g t) ≫ (strictLocalizationCone (t ≫ g)).π.app x :=
  sorry

end Scheme

end AlgebraicGeometry
