/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.DmStabilizerIsomorphismOpenLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
import Sheaf.AlgebraicGeometry.AffineStackStabilizerEtaleComparison
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.FiniteFlatAffineGroupoidModuli
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Stabilizer-preserving étale maps and categorical moduli spaces

Source: Stacks Project, `stacks-more-morphisms.tex`, Tag 0DUV,
`lemma-etale-separated-over-keel-mori`, restricted to DM stacks over a field
(blueprint: lem-sfb-keel-mori-stabilizer-preserving-etale).

Categorical moduli spaces are supplied with their universal property only.
The equivalence with the two-fibre product retains both specified projections.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A representable separated étale stabilizer-preserving map of finite-inertia DM
stacks induces a separated étale map of their categorical moduli spaces and a
cartesian square. Source: Stacks Project, Tag 0DUV
(blueprint: lem-sfb-keel-mori-stabilizer-preserving-etale).

Proof:
1. The étale atlas of X₂ is smooth by lem-sfb-stack-chartwise-smooth-etale-calculus.
   Apply lem-sfb-etale-smooth-atlas-fppf-descent, then
   lem-sfb-finite-inertia-etale-affine-charts to cover X₂ by separated étale
   stabilizer-preserving affine finite-flat-groupoid quotients Aᵢ. They are DM by
   lem-sfb-dm-etale-atlas-calculus. Apply lem-sfb-finite-flat-affine-groupoid-moduli
   to obtain uniform categorical maps Aᵢ → Bᵢ, universally homeomorphic and
   bijective on geometric isomorphism classes, with affine targets.
2. Apply lem-sfb-etale-stabilizer-preserving-affine-moduli to Aᵢ ×[X₂] Aⱼ.
   The two categorical spaces agree by inverse universal factorizations, giving
   Bᵢⱼ and cartesian squares over Bᵢ and Bⱼ. Use lem-sfb-etale-local-moduli-gluing
   to construct q₂ : X₂ → Q₂ and the étale cover Bᵢ → Q₂, with these overlaps.
   This map is a universal homeomorphism.
3. Prove q₂ uniform categorical: after a flat T → Q₂, factor a map to a space Z
   over each T ×[Q₂] Bᵢ using the uniform categorical local maps. On overlaps
   the factors agree by categorical uniqueness for Aᵢⱼ → Bᵢⱼ. Flatness follows
   from lem-sfb-stack-chartwise-smooth-etale-calculus; the cover is étale by
   lem-trf-space-fibre-products-etale-covers. The sheaf condition for Z glues
   the factors and proves uniqueness.
4. Pull h back to Aᵢ. The pullbacks Cᵢ are DM and remain separated étale and
   stabilizer-preserving by lem-sfb-dm-etale-atlas-calculus and
   lem-sfb-etale-stabilizer-preserving-affine-moduli. Apply
   lem-sfb-affine-stack-stabilizer-etale-comparison to obtain separated étale
   Nᵢ → Bᵢ and Cᵢ ≃ Aᵢ ×[Bᵢ] Nᵢ. Thus Cᵢ → Nᵢ is uniform categorical,
   being a flat base change of Aᵢ → Bᵢ.
5. Over Bᵢⱼ the two pullbacks of Nᵢ and Nⱼ are categorical spaces of the same
   stack. Their inverse universal factorizations give overlap isomorphisms over
   Bᵢⱼ; uniqueness proves the identity and triple-overlap cocycle equations.
6. Form the coproduct schemes U = ∐ Bᵢ and V = ∐ Nᵢ using
   lem-weil-pbc-scheme-coproduct-family and def-weil-size-convention. The map
   U → Q₂ is an étale cover and V → U is étale. The overlap isomorphisms give
   descent data on this single cover. Apply
   lem-sfb-etale-space-single-cover-effective-descent to obtain étale Q₁ → Q₂.
7. Glue the maps Cᵢ → Nᵢ → Q₁ by the sheaf condition. The local comparison
   equivalences glue to X₁ ≃ X₂ ×[Q₂] Q₁: full faithfulness gives unique overlap
   isomorphisms and the stack descent condition glues objects. Both projections
   are the specified maps. Scheme refinements use lem-sfb-dm-etale-atlas-calculus.
8. The map Q₁ → Q₂ is flat. The cartesian square makes q₁ a flat base change
   of q₂, hence uniform categorical and a universal homeomorphism. These
   statements persist under further flat base changes, since flat maps compose.
9. Compare the relative diagonals of h and Q₁ → Q₂. After arbitrary space
   base change the vertical maps are homeomorphisms. Properness of the upper
   diagonal makes it universally closed; transfer closed images through these
   homeomorphisms to prove universal closedness of the lower diagonal. Apply
   lem-sfb-space-separated-diagonal-closed to make it a closed immersion.
10. For each j, categoricality of qⱼ and pⱼ gives inverse maps Qⱼ ⇄ Mⱼ:
    their composites are identities by uniqueness. Conjugate Q₁ → Q₂ by these
    isomorphisms. Its composite with p₁ is h followed by p₂, so it is the unique
    induced map. Étaleness, separatedness and the cartesian comparison transport
    along the isomorphisms. All factorizations are over k.

The inertia comparison is the existing canonical comparison. Finiteness is
scheme representability of each inertia base change. Separatedness of h is
properness of each algebraic-space base change's diagonal. The final comparison
has first projection p₁ and second projection h, so is the natural comparison;
the comma isomorphism is the displayed commuting square. -/
theorem exists_keelMori_stabilizer_preserving_etale
    (k : Type u) [Field k]
    (X₁ : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (X₂ : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (hX₁ : IsDeligneMumfordModuliStack X₁) (hX₂ : IsDeligneMumfordModuliStack X₂)
    (hfinite₁ : IsRepresentableFiniteModuliMap (moduliInertiaProjection X₁))
    (hfinite₂ : IsRepresentableFiniteModuliMap (moduliInertiaProjection X₂))
    (h : BasedFunctor X₁ X₂) (hrep : IsRepresentableByAlgebraicSpaces h)
    (het : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X₂)
      (Z : AlgebraicSpace (Spec (.of k))) (a : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange h T t Z a → SpaceMapIsEtale Z T a)
    (hsep : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) X₂)
      (Z : AlgebraicSpace (Spec (.of k))) (a : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange h T t Z a →
        AlgebraicSpace.IsRepresentableWith (fun _ _ f ↦ IsProper f.left)
          (pullback.diagonal a))
    (hstab : (moduliInertiaComparison h).toFunctor.IsEquivalence)
    (M₁ M₂ : AlgebraicSpace (Spec (.of k)))
    (p₁ : BasedFunctor X₁ (discreteModuli M₁.obj.obj))
    (p₂ : BasedFunctor X₂ (discreteModuli M₂.obj.obj))
    (hp₁ : ∀ Z : AlgebraicSpace (Spec (.of k)),
      Function.Bijective (fun a : M₁.obj.obj ⟶ Z.obj.obj ↦ p₁.comp (discreteModuliMap a)))
    (hp₂ : ∀ Z : AlgebraicSpace (Spec (.of k)),
      Function.Bijective (fun a : M₂.obj.obj ⟶ Z.obj.obj ↦ p₂.comp (discreteModuliMap a))) :
    ∃ hbar : M₁.obj.obj ⟶ M₂.obj.obj,
      p₁.comp (discreteModuliMap hbar) = h.comp p₂ ∧
      (∀ b : M₁.obj.obj ⟶ M₂.obj.obj,
        p₁.comp (discreteModuliMap b) = h.comp p₂ → b = hbar) ∧
      AlgebraicSpace.IsEtale hbar ∧
      AlgebraicSpace.IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left)
        (pullback.diagonal hbar) ∧
      ∃ e : BasedFunctor X₁ (moduliTwoFiberProduct (discreteModuliMap hbar) p₂),
        e.toFunctor.IsEquivalence ∧
        e.comp (moduliTwoFiberFst (discreteModuliMap hbar) p₂) = p₁ ∧
        e.toFunctor ⋙ ObjectProperty.ι _ ⋙
          Comma.snd (discreteModuliMap hbar).toFunctor p₂.toFunctor = h.toFunctor := by
  sorry

end AlgebraicGeometry
