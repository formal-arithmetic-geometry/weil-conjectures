module

public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.AffinePrincipalRelativePseudoCoherenceLocalization
import Sheaf.AlgebraicGeometry.AffinePrincipalRelativePseudoCoherenceGluing
import Sheaf.AlgebraicGeometry.AffinePolynomialEmbeddingPseudoCoherence

/-! # Relative pseudo-coherence on every affine polynomial chart

Source: Stacks Project, More on Morphisms, Tags 09UJ
(`lemma-relative-pseudo-coherence-characterize`) and 09VC
(`lemma-relatively-pseudo-coherent`), with the embedding existence preceding Tag 09UI
(blueprint: lem-sfb-relative-pseudocoherence-all-affine-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Relative `m`-pseudo-coherence is equivalent to absolute `m`-pseudo-coherence of the
derived direct image under every closed embedding of every compatible affine pair into
finite affine space. Each affine pair admits such an embedding independently of `E`.

Source: Stacks Project, More on Morphisms, Tags 09UJ and 09VC, and the paragraph before
Tag 09UI (blueprint: lem-sfb-relative-pseudocoherence-all-affine-charts).

Proof:
1. By lem-weil-pbc-lft-affine-pairs, each compatible affine pair gives a finitely
   generated algebra of sections. Choose finite generators. Evaluation from the finite
   polynomial ring is surjective, hence its spectrum is the required closed embedding
   by def-nagata-relative-affine-space and def-weil-closed-immersion. This proves the
   second conjunct without using any pseudo-coherence assumption.
2. Suppose E is relatively m-pseudo-coherent, and take its good affine covers from
   def-sfb-relative-pseudo-coherent-complex. For an arbitrary affine pair U,V and u in U,
   use lem-sc-affine-inter-principal-both first on the base to choose V' principal in
   both V and a good base open. Pull back V' to U and the good source open; both are
   principal affine opens. Use the same lemma on the source to obtain U'_u principal
   in both. A principal open in a principal open is principal, since
   D_{D(t)}(s/t^q) = D(ts); these U'_u form a principal cover of U.
3. Restrict the good embedding to affine space over V'. By
   lem-pc-restrict-derived-direct-image-open its pushforward is the restriction of
   the good pushforward, hence remains m-pseudo-coherent by restricting the local
   strictly perfect approximations of def-sfb-m-pseudo-coherent-complex. The source
   over V' is finite type as a quotient of a finite polynomial ring.
4. Apply lem-sfb-affine-principal-relative-pseudocoherence-localization to that source,
   its principal open U'_u and the principal base inclusion V' into V. This gives a
   good polynomial embedding of each U'_u over V.
5. The morphism U to V is finite type by lem-weil-pbc-lft-affine-pairs. Apply
   lem-sfb-affine-principal-relative-pseudocoherence-gluing to the principal cover
   just constructed. It gives one good embedding of U over V. Then
   lem-sfb-affine-polynomial-embedding-pseudocoherence-invariance gives the condition
   for every embedding, proving the forward implication for the arbitrary affine pair.
6. Conversely, use lem-weil-pbc-affine-opens-basis to choose an affine cover of S and
   affine covers of its inverse images. Step 1 gives embeddings; the universal
   hypothesis makes their derived direct images m-pseudo-coherent. These are exactly
   the witnesses of def-sfb-relative-pseudo-coherent-complex. -/
theorem isMPseudoCoherentRelativeTo_iff_all_affine_charts_and_exists_embedding
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : schemeDerivedCategory X) (m : ℤ) :
    (IsMPseudoCoherentRelativeTo f m E ↔
      ∀ (U : X.Opens) (V : S.Opens), IsAffineOpen U → IsAffineOpen V →
        ∀ (hUV : U ≤ f ⁻¹ᵁ V) (n : ℕ)
          (j : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme),
          IsClosedImmersion j →
          j ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) =
            f.resLE V U hUV →
          IsMPseudoCoherent (AffineSpace (ULift.{u} (Fin n)) V.toScheme) m
            ((schemeDerivedDirectImage j).obj ((derivedPullback U.ι).obj E))) ∧
      (∀ (U : X.Opens) (V : S.Opens), IsAffineOpen U → IsAffineOpen V →
        ∀ hUV : U ≤ f ⁻¹ᵁ V, ∃ n : ℕ,
          ∃ j : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme,
            IsClosedImmersion j ∧
            j ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) =
              f.resLE V U hUV) := by
  sorry

end AlgebraicGeometry.Scheme
