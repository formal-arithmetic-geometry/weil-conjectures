/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.TraitSpecializationTriples
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Etale sheaves on a strictly henselian trait as specialization triples

Source: ILO, Travaux de Gabber, Expose XVII, section 1.2.2, printed p. 260;
Stacks Project, Tags 03QO, 03QW and 04JQ (blueprint: lem-per-trait-sheaf-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The canonical global-section germ, including the usual comparison between global
sections and evaluation at the terminal object of the small etale site.
Source: Stacks Project, Tags 03QO and 03QW (blueprint: lem-per-trait-sheaf-gluing). -/
noncomputable def traitGlobalGerm (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
      (Scheme.pointSmallEtale t).sheafFiber.obj M :=
  (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (Scheme.Etale.isTerminalMkId X)).hom.app M ≫
    (Scheme.pointSmallEtale t).toPresheafFiber (Scheme.Etale.mk (𝟙 X))
      (Over.homMk t (Category.comp_id t)) M.obj

/-- Etale module sheaves on a strictly henselian trait are specialization triples.
Here `K` is the fraction field, `Ks` its chosen separable closure inside `Ω`, and
`s` a fixed geometric closed point. The comma category supplies exactly the pairs of
linear morphisms in the statement. `c` identifies its closed module with the closed
geometric stalk. `r` identifies its generic representation with the restriction to
`Spec K` followed by the field equivalence `Eη`. The comparison `g` is the actual
geometric stalk on the field, with its Galois action specified on every germ below;
`upperStarCompSheafFiberIso` identifies this with the generic stalk on the trait.
The comparisons `w` and `σ` give global sections and generic invariant sections.
Their germ equations fix these identifications canonically. The last equality says
that restriction is exactly the triple's arrow factored through invariants.
The final conjunct states the componentwise kernel and cokernel universal properties.

Source: ILO XVII 1.2.2, printed p. 260; Stacks Tags 03QO, 03QW, 04JQ
(blueprint: lem-per-trait-sheaf-gluing).

Proof:
1. A DVR has only the generic and closed points; its fraction field is the principal
open obtained by inverting a uniformizer. Its residue field is separably closed by
`def-weil-pbc-henselian-terminology` and `def-sc-discrete-valuation-ring`.
2. Apply `lem-exc-abelian-sheaves-gmodules` to K and Ω, then transport the scalar
endomorphisms and their equations across its full faithfulness. This gives the field
module equivalence for every commutative Λ, with no finite-coefficient hypothesis.
3. Apply the same equivalence to the separably closed residue field. Its Galois group
is trivial, so module sheaves on the closed point are modules. The adjunctions are
those of `prop-weil-pbc-inverse-image-modules-exact`.
4. Full faithfulness identifies Hom from the constant integer sheaf with invariant
stalk elements; `lem-weil-pbc-constant-sheaf-geometric-stalk` normalizes the constant
stalk. Thus generic sections are V^H with the actual germ map. By
`lem-weil-pbc-strictly-henselian-sections-stalk` and `def-weil-pbc-direct-image`,
the closed stalk of j_*F is V^H. `lemma-openclosed-stalk-upperstar` gives its closed
restriction, naturally the closed sheaf associated to V^H.
5. Send M to its closed stalk, the field representation of j^*M, and the generic germ
of the unique global representative of a closed germ. This arrow has invariant image.
`lemma-openclosed-stalk-upperstar` identifies the generic component with M's stalk.
Naturality supplies the commuting pairs on morphisms.
6. For (W,V,a), factor a through b:W→V^H. If F is the field sheaf corresponding to V,
put B=i^*j_*F and let C(W) be the closed sheaf for W. The inverse is the sectionwise
fiber product j_*F ×_{i_*B} i_*C(W), with maps given by the i-adjunction unit and i_*b.
7. Exact inverse image preserves this fiber product. The counits of `lem-kun-04ca`
and `lem-sc-open-immersion-pushforward-fully-faithful` identify its restrictions
with C(W) and F, and the adjunction triangle identity recovers b, hence a.
8. The two units give a natural reconstruction map from M to this fiber product.
It is an isomorphism at both geometric points, so
`lem-weil-pbc-sets-etale-iso-on-geometric-stalks` makes it an isomorphism.
Its inverse respects scalars. These natural comparisons give the equivalence.
9. Kernels are (ker f,ker g) with the restricted arrow; cokernels are the two module
quotients with the induced arrow. Kernel stabilizers are inherited and quotient
stabilizers contain those of representatives, hence are open. The componentwise
factorization properties prove both universal properties.
10. Strict-local sections equal the closed stalk and field sections equal the generic
invariants. Step 5 makes restriction exactly b. Its generic component is by definition
the field equivalence applied to j^*M, giving all the restriction assertions. -/
theorem traitSheaves_equiv_specialization
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ks Ω : Type u) [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (Ωs : Type u) [Field Ωs] [IsAlgClosed Ωs]
    (s : Spec (.of Ωs) ⟶ Spec (.of R)) (hs : s default = IsLocalRing.closedPoint R)
    (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ (Eη : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌
          Rep.DiscreteContinuousRep.{u + 1, u, u + 1} Λ (Gal(Ks/K)))
      (E : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌
          TraitSpecialization.{u, u + 1, u + 1} Λ (Gal(Ks/K)))
      (c : E.functor ⋙ traitSpecializationClosed Λ (Gal(Ks/K)) ≅
        (Scheme.pointSmallEtale s).sheafFiber)
      (g : Eη.functor ⋙ traitDiscreteRepInclusion Λ (Gal(Ks/K)) ⋙
          forget₂ (Rep.{u + 1} Λ (Gal(Ks/K))) (ModuleCat.{u + 1} Λ) ≅
        (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber)
      (r : upperStar (ModuleCat.{u + 1} Λ)
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⋙ Eη.functor ≅
        E.functor ⋙ traitSpecializationGeneric Λ (Gal(Ks/K)))
      (w : Sheaf.Γ (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≅
        E.functor ⋙ traitSpecializationClosed Λ (Gal(Ks/K)))
      (σ : Sheaf.Γ (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ≅
        Eη.functor ⋙ traitDiscreteRepInclusion Λ (Gal(Ks/K)) ⋙
          Rep.invariantsFunctor Λ (Gal(Ks/K))),
      (∀ M : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ),
        w.hom.app M ≫ c.hom.app M = traitGlobalGerm Λ s M) ∧
      (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
          (m : (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj F),
        g.hom.app F (σ.hom.app F m).val =
          traitGlobalGerm Λ (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) F m) ∧
      (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
          (h : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (_hτ : (algebraMap Ks Ω).comp h.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (X : (Spec (.of K)).Etale)
          (x x' : (Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
          (_hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
          (z : F.obj.obj (op X)),
        g.hom.app F ((Eη.functor.obj F).obj.ρ h
          (g.inv.app F ((Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z))) =
          ((Scheme.pointSmallEtale
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x'
            F.obj z)) ∧
      (∀ M : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ),
        globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) M ≫
          σ.hom.app ((upperStar (ModuleCat.{u + 1} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj M) ≫
          (Rep.invariantsFunctor Λ (Gal(Ks/K))).map
            ((traitDiscreteRepInclusion Λ (Gal(Ks/K))).map (r.hom.app M)) =
          w.hom.app M ≫ traitSpecializationInvariantArrow Λ (Gal(Ks/K)) (E.functor.obj M)) ∧
      (∀ (A B : TraitSpecialization.{u, u + 1, u + 1} Λ (Gal(Ks/K))) (f : A ⟶ B),
        HasKernel f ∧ HasCokernel f ∧
        PreservesLimit (parallelPair f 0) (traitSpecializationClosed Λ (Gal(Ks/K))) ∧
        PreservesLimit (parallelPair f 0) (traitSpecializationModule Λ (Gal(Ks/K))) ∧
        PreservesColimit (parallelPair f 0) (traitSpecializationClosed Λ (Gal(Ks/K))) ∧
        PreservesColimit (parallelPair f 0) (traitSpecializationModule Λ (Gal(Ks/K)))) := by
  sorry

end AlgebraicGeometry.Etale
