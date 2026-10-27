module

public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Relative pseudo-coherence is local on the source

Source: Stacks Project, More on Morphisms, Tags 09UI and 09UJ, and the neighbourhood
reduction in the proof of Tag 0CSL
(blueprint: lem-sfb-relative-pseudocoherence-local-on-source).

Both the fixed-degree condition and its all-degrees consequence descend along arbitrary
open covers of the source. No quasi-compactness or quasi-coherence is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Relative `m`-pseudo-coherence descends along an arbitrary open cover of the source.
Source: Stacks Project, More on Morphisms, Tag 09UJ,
`lemma-relative-pseudo-coherence-characterize`, using Tag 09UI
(blueprint: lem-sfb-relative-pseudocoherence-local-on-source).

Proof:
1. Fix m and choose affine opens V covering S, using lem-weil-pbc-affine-opens-basis.
   For each V and each cover member U k, take all affine opens W contained in both U k
   and the inverse image of V. The affine basis implies that these W cover that inverse
   image, since the U k cover X. This family is a set; no finite subcover is required,
   and no intersection of affine opens is asserted to be affine.
2. The restricted morphism (U k).ι followed by f is locally of finite type: open
   immersions have that property and it is stable under composition
   (def-pc-morphism-conventions and def-weil-finite-type-morphism).
   Apply lem-sfb-relative-pseudocoherence-all-affine-charts to the assumed relative
   m-pseudo-coherence on U k, with the affine opens W and V. It gives a closed embedding
   W into some finite affine space over V whose derived direct image is m-pseudo-coherent.
   The twice restricted E is canonically E restricted to W: the formula in
   def-pc-derived-pullback for an open immersion is ordinary termwise restriction, since
   its inverse-image structure sheaf is the structure sheaf of the open and tensoring
   with that ring is the identity. Restrictions through nested opens compose.
3. These affine covers and embeddings are exactly the witnesses required by
   def-sfb-relative-pseudo-coherent-complex for E relative to S. No compatibility between
   different embedding witnesses is needed. -/
theorem isMPseudoCoherentRelativeTo_of_iSup_eq_top
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (m : ℤ) (E : schemeDerivedCategory X) {I : Type v}
    (U : I → X.Opens) (hU : iSup U = ⊤)
    (hE : ∀ k : I, IsMPseudoCoherentRelativeTo ((U k).ι ≫ f) m
      ((derivedPullback (U k).ι).obj E)) :
    IsMPseudoCoherentRelativeTo f m E := by
  sorry

/-- Relative pseudo-coherence descends along an arbitrary open cover of the source.
Source: Stacks Project, More on Morphisms, Tags 09UI (2) and 09UJ, as used in the first
paragraph of the proof of Tag 0CSL
(blueprint: lem-sfb-relative-pseudocoherence-local-on-source).

Proof: By def-sfb-relative-pseudo-coherent-complex, the hypothesis gives the relative
m-condition on every cover member for every integer m. Fix m and apply the fixed-degree
locality argument of isMPseudoCoherentRelativeTo_of_iSup_eq_top: refine the source cover
by affine opens over each affine base open, use
lem-sfb-relative-pseudocoherence-all-affine-charts on the restrictions, and assemble the
embedding witnesses. Quantify the resulting relative m-condition for E over all integers.
The covers and embeddings may vary with m; neither a finite subcover nor a uniform
cohomological bound is needed. -/
theorem isPseudoCoherentRelativeTo_of_iSup_eq_top
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : schemeDerivedCategory X) {I : Type v}
    (U : I → X.Opens) (hU : iSup U = ⊤)
    (hE : ∀ k : I, IsPseudoCoherentRelativeTo ((U k).ι ≫ f)
      ((derivedPullback (U k).ι).obj E)) :
    IsPseudoCoherentRelativeTo f E := by
  sorry

end AlgebraicGeometry.Scheme
