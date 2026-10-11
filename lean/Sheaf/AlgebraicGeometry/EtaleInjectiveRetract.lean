/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The retract supplied by a surjective scheme morphism

Source: Stacks Project, Etale Cohomology, Tag 0A4C, proof, first paragraph
(blueprint: lem-weil-pbc-retract-supplied).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An injective constant-ring module sheaf is a summand of any direct image into which
its inverse image embeds. Source: Stacks Project, Tag 0A4C, proof, first paragraph
(blueprint: lem-weil-pbc-retract-supplied).

RV and RU are lambda-bound to the constant commutative ring sheaves after forgetting
to rings, exactly as in prop-weil-pbc-inverse-image-modules-exact; etaV and etaU are
the forgotten sheafification units. The condition on gamma specifies the canonical constant-section
map. The arguments LM, am, e and
hunit specify the module inverse image, its adjunction and its underlying abelian unit
from prop-weil-pbc-inverse-image-modules-exact; they do not assume injectivity of J.
The finite direct sum is represented by the binary product in this abelian category.

Proof:
1. The adjunction of prop-weil-pbc-inverse-image-modules-exact identifies the adjoint
of j with the unit followed by the direct image of j, and the triangle identity says
j is the inverse image of this adjoint followed by the counit.
2. Kernels of module sheaves are computed sectionwise
(def-weil-sheaf-of-modules-category), so monicity can be tested on underlying abelian
sheaves. The functors def-weil-pbc-inverse-image and def-weil-pbc-direct-image and their
unit agree with the abelian functors by the same proposition.
3. Choose an algebraic closure of each residue field to obtain a geometric point over
each point of X (def-weil-geometric-point). Their composite images cover Y because f
is surjective (def-weil-surjective-morphism).
4. By lemma-openclosed-stalk-upperstar, inverse-image stalks at these points are the
stalks at their images, naturally in the sheaf. Taking stalks in the triangle identity
factors the stalk of j through the stalk of its adjoint.
5. By lem-weil-pbc-geometric-stalks-detect-mono, the stalks of j are injective, hence the
stalks of its adjoint are injective. The covering family on Y detects monomorphisms,
so the adjoint is monic, including as a module-sheaf morphism.
6. Injectivity of I (def-sp-injective-resolutions) extends its identity along this mono;
Injective.factorThru and Injective.comp_factorThru give rho and the retraction equation.
7. The endomorphism identity minus rho followed by the adjoint is killed by rho,
so factors uniquely through kernel rho as pi. The maps (rho, pi) and the map with
components the adjoint and kernel inclusion are inverse: use the retraction equation,
pi composed with the adjoint equals zero, and pi on the kernel equals the identity.
This gives precisely the displayed direct-summand isomorphism. -/
theorem Etale.exists_injective_retract_of_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (Λ : Type (u + 1)) [CommRing Λ] :
    (fun (RV : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (RU : Sheaf X.smallEtaleTopology RingCat.{u + 1})
      (etaV : (Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ RV.obj)
      (etaU : (Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ RU.obj) ↦
    ∀ (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        RingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
        (X.smallGrothendieckTopology @Etale)).obj RU),
    (∀ (W : Y.Etaleᵒᵖ) (r : Λ),
        gamma.hom.app W (etaV.app W r) =
          etaU.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) r) →
    ∀ (LM : SheafOfModules.{u + 1} RV ⥤ SheafOfModules.{u + 1} RU)
      (am : LM ⊣ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma))
      (e : LM ⋙ SheafOfModules.toSheaf RU ≅
        SheafOfModules.toSheaf RV ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f),
    (∀ G : SheafOfModules.{u + 1} RV,
      (SheafOfModules.toSheaf RV).map (am.unit.app G) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
          ((SheafOfModules.toSheaf RV).obj G) ≫
            (Etale.lowerStar AddCommGrpCat.{u + 1} f).map (e.inv.app G)) →
    ∀ (I : SheafOfModules.{u + 1} RV) [Injective I]
      (J : SheafOfModules.{u + 1} RU) (j : LM.obj I ⟶ J) [Mono j],
    Mono (am.unit.app I ≫ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).map j) ∧
      ∃ (rho : (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).obj J ⟶ I)
        (pi : (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).obj J ⟶ kernel rho)
        (s : (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).obj J ≅ I ⨯ kernel rho),
        (am.unit.app I ≫ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).map j) ≫ rho = 𝟙 I ∧
        pi ≫ kernel.ι rho = 𝟙 _ -
          rho ≫ (am.unit.app I ≫ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).map j) ∧
        s.hom = prod.lift rho pi)
      ((sheafCompose Y.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)))
      ((sheafCompose X.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)))
      (Functor.whiskerRight
        (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (Functor.whiskerRight
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) := by
  sorry

end AlgebraicGeometry
