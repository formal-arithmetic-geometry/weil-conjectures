/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Strict-local model for the two maps in geometric-stalk reduction

This comparison does not use strict-local closed-fibre base change: it transports
stalk exchange to a local model and residue-field pullback to the chosen fields.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- The stalk exchange and the residue-field pullback admit a common strict-local model.
No equivalence between local stalks and closed-fibre cohomology is asserted here, and
no strict-local exchange hypothesis is assumed.

Source: Stacks Project, proof of Theorem Tag 095T, paragraphs 3--4, together with
Tag 03Q9 (strict-henselization stalk formula) and topological invariance Tag 04DY.
(blueprint: lem-weil-pbc-p1-strict-local-model-comparison).

Proof: choose compatible algebraic closures for the two geometric points. Take A
and B to be their strict henselization rings. Functoriality supplies the local map
phi and commuting residue-field embeddings. Restrict F to the projective line over A
to obtain F₀; inverse image preserves torsion, by the inverse-image stalk formula.
The pointed-neighbourhood stalk formula and that same inverse-image formula supply
a₁ and a₂: original and restricted higher-direct-image stalks are the same filtered
colimits of neighbourhood cohomology. Properness gives the qcqs hypotheses. Compare
module cohomology with underlying abelian cohomology using acyclicity after forgetting
coefficients at universe u+1, not preservation of injectives by the forgetful functor.
The underived exchange pulls sections back along the base-changed neighbourhood.
The functorial limit projections commute with phi, so these section maps agree on
every neighbourhood representative. Passing to the filtered colimit and homology
proves the first displayed equation, independently of any closed-fibre theorem.
The integral residue-field factorizations imply that k and k' are purely inseparable
extensions of the respective relative separable closures. Topological invariance
identifies the etale cohomology of these residue projective lines with the chosen
geometric fibres, giving b₁ and b₂. The commuting residue-field square and functoriality
of cohomology pullback prove the second equation; use the composite inverse-image
isomorphism for the target sheaf. Uniqueness of pullbacks handles the arbitrary X'.
These constructions include degree zero, zero sheaves, and nonperfect fields. -/
theorem Etale.projectiveLine_strictLocal_modelComparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k))
    (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (φ : S.residueField s ⟶ .of k),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (φ : T.residueField t ⟶ .of k'),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ T.fromSpecResidueField t = τ)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheaf F] (q : ℕ) :
    ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B),
      letI := cA
      letI := cB
      ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B),
        letI := hA
        letI := hB
        ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A))
          (sB : IsSepClosed (IsLocalRing.ResidueField B)),
          letI := sA
          letI := sB
          ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
            letI := hφ
            ∃ (F₀ : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
                (ModuleCat.{u + 1} Λ)) (hF₀ : IsTorsionSheaf F₀),
              letI := hF₀
              let t₀ := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))
              let rA := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
              let g₀ := Spec.map (CommRingCat.ofHom φ)
              let i₀ := Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ))
              let G₀ := (sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
                ((ProjectiveSpace.map _ rA)^*[ModuleCat.{u + 1} Λ].obj F₀)
              let G := (sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
                ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)
              ∃ (a₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
                (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeSourceFunctor Λ g₀
                    (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F₀))
                (a₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
                (t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
                  ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ g₀)
                    (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F₀))
                (b₁ : Sheaf.H G₀ q ≃+ Sheaf.H G q)
                (b₂ : Sheaf.H ((ProjectiveSpace.map _ i₀)^*[AddCommGrpCat.{u + 1}].obj G₀) q ≃+
                  Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj G) q),
                (∀ x, a₂ ((((pointSmallEtale τ).sheafFiber
                    (A := ModuleCat.{u + 1} Λ)).map
                    (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
                  ((t₀.sheafFiber (A := ModuleCat.{u + 1} Λ)).map
                    (Etale.baseChangeHomologyMap Λ
                      (ProjectiveSpace.isPullback_map _ g₀) q F₀)).hom (a₁ x)) ∧
                (∀ y, b₂ (Etale.cohomologyMap (ProjectiveSpace.map _ i₀) G₀ q y) =
                  Etale.cohomologyMap (ProjectiveSpace.map _ ι) G q (b₁ y)) := by sorry

end AlgebraicGeometry
