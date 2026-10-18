/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.CategoryTheory.Sites.LocalOrientedProjectionArrows
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.CategoryTheory.Sites.OrientedProductUniversal
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.SitePointFibre
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites

/-!
# Gabber exactness of the local oriented-product projection

Source: Illusie–Laszlo–Orgogozo, Exposé XI §2.2, Proposition 2.3 and Corollary 2.3.1,
printed pp. 177–178 (blueprint: lem-trf-local-oriented-projection-exact).

The oriented product may be given by any small-site presentation satisfying the recorded
universal property. Its canonical section is characterized by that universal property and
the normalized closed-point counit. Constant-coefficient module lifts and their composition
identification are supplied, rather than assumed, and their units specify the comparison.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.GabberLocalProjection

/-- The second direct image on constant-coefficient module sheaves is canonically the
inverse image of the closed-point section, and is exact. The normalization of `d` fixes
the actual global-section germ, and `paste` fixes the canonical section's orientation.
The module composition isomorphism is normalized on underlying set sheaves by `β`;
`unitComparison` therefore is the specified map, rather than an arbitrary isomorphism.

Source: ILO Exposé XI §2.2 (2.a)–(2.f), Proposition 2.3 and Corollary 2.3.1
(blueprint: lem-trf-local-oriented-projection-exact).

Proof plan:
1. Apply lem-weil-pbc-sets-strictly-henselian-open-sections-stalk to the whole of A and S.
   Their closed-point germs are natural bijections. The local condition on a identifies
   the image point with the centre of S, so imageGerm is invertible and fixes d.
2. The counit defines closedOrientation. The universal property of
   lem-trf-oriented-product-universal gives σ, α and β with exactly this pasted orientation.
   Apply lem-pe-constant-left-module-inverse-image to obtain the module lifts with
   their scalar actions and compatible units; composition gives the normalized e.
3. On the triple site, put k(W)=(A→S←W). The projection formula on representables,
   sheafification adjunction and Yoneda identify (p₂,*H)(W) with H(k(W)). Representables
   on the triple site are sheafified; no subcanonicity of that site is assumed.
4. Fix a geometric point y of B and t=σy. A lift of t to a triple (U→V←W) has a
   closed-point lift to U and a y-lift to W with matching images in the pullback of V.
   The first extends uniquely to a section over A; its image extends uniquely over S.
   Injectivity of the A germ verifies compatibility of these two sections.
5. Pull W back along the resulting B-section of B×S V, obtaining an étale W₀→B.
   The matching germs give a y-lift to W₀ and a pointed refinement k(W₀)→(U→V←W).
6. lem-trf-site-point-fibre expresses both stalks as filtered colimits. The refinement
   proves surjectivity. For injectivity, equality has a common pointed triple refinement
   by lem-weil-pbc-filtered-colimit-modules-elementwise; refine it once more to k(W₀).
   Morphisms between the k(Wᵢ) are precisely the corresponding B-site morphisms.
7. Pulling back a section of H(k(W)) along σ and evaluating at y gives exactly that
   restriction of representatives. The unit identity and the module-lift homEquiv
   identify it with the stalk of unitComparison, proving the specified comparison.
8. The conservative geometric stalks of B (lemma-openclosed-point-ulift) make the
   comparison invertible, naturally in H. Exactness of σ inverse image from
   lem-pe-constant-left-module-inverse-image transfers across this natural isomorphism.
   No finiteness, coherence, torsion, or nonemptiness condition on B is used. -/
theorem local_oriented_projection_exact
    (R T : Type u) [CommRing R] [CommRing T]
    [IsStrictlyHenselianLocalRing R] [IsStrictlyHenselianLocalRing T]
    (A S B : Scheme.{u}) (eA : A ≅ Spec (.of R)) (eS : S ≅ Spec (.of T))
    (a : A ⟶ S) (b : B ⟶ S)
    (ha : (eA.inv ≫ a ≫ eS.hom) (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint T)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ A)
    (hx : (x ≫ eA.hom) default = IsLocalRing.closedPoint R)
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (p₁ : GeometricMorphism (Sheaf J (Type (u + 1)))
      (Sheaf A.smallEtaleTopology (Type (u + 1))))
    (p₂ : GeometricMorphism (Sheaf J (Type (u + 1)))
      (Sheaf B.smallEtaleTopology (Type (u + 1))))
    (τ : (p₂.comp (etale b)).direct ⟶ (p₁.comp (etale a)).direct)
    (hP : OrientedProduct.IsUniversal.{u + 1, u + 2, u + 1} (etale a) (etale b) p₁ p₂ τ) :
    ∃ d : sections S ≅ ((point x).comp (etale a)).inverse,
      d.hom = imageGerm a x ∧
      (∃ (σ : GeometricMorphism (Sheaf B.smallEtaleTopology (Type (u + 1)))
            (Sheaf J (Type (u + 1))))
        (α : (σ.comp p₁).direct ≅ ((epsilon B).comp (point x)).direct)
        (β : (σ.comp p₂).direct ≅ (identity _).direct),
        OrientedProduct.paste (etale a) (etale b) p₁ p₂ τ σ
          ((epsilon B).comp (point x)) (identity _) α β =
            (Functor.leftUnitor (etale b).direct).hom ≫ closedOrientation a b x d) ∧
      ∀ (σ : GeometricMorphism (Sheaf B.smallEtaleTopology (Type (u + 1)))
          (Sheaf J (Type (u + 1))))
        (α : (σ.comp p₁).direct ≅ ((epsilon B).comp (point x)).direct)
        (β : (σ.comp p₂).direct ≅ (identity _).direct),
        OrientedProduct.paste (etale a) (etale b) p₁ p₂ τ σ
          ((epsilon B).comp (point x)) (identity _) α β =
            (Functor.leftUnitor (etale b).direct).hom ≫ closedOrientation a b x d →
        ∀ (Λ : Type (u + 1)) [CommRing Λ],
        ∃ (pL : ModuleLift J B.smallEtaleTopology p₂ Λ)
          (sL : ModuleLift B.smallEtaleTopology J σ Λ)
          (e : sL.direct ⋙ pL.direct ≅ 𝟭 _),
          (∀ K : ringedSiteModules.{u + 1}
              ((constantSheaf B.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)),
            (underlying B.smallEtaleTopology Λ).map
              (e.hom.app K) =
            pL.underlyingDirect.hom.app (sL.direct.obj K) ≫
              p₂.direct.map (sL.underlyingDirect.hom.app K) ≫
              β.hom.app
                ((underlying B.smallEtaleTopology Λ).obj K)) ∧
          (∀ H : ringedSiteModules.{u + 1}
              ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of Λ)),
            IsIso ((unitComparison J B.smallEtaleTopology p₂ σ Λ pL sL e).app H)) ∧
          PreservesFiniteLimits pL.direct ∧ PreservesFiniteColimits pL.direct := by
  sorry

end CategoryTheory.GabberLocalProjection
