module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

/-! # Independence of affine polynomial embeddings for degreewise pseudo-coherence

Source: Stacks Project, More on Morphisms, Tag 09VC,
`lemma-relatively-pseudo-coherent`, comparison of two embeddings of a fixed affine morphism
(blueprint: lem-sfb-affine-polynomial-embedding-pseudocoherence-invariance).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wN wR

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- For a finite type morphism of affine schemes, degreewise pseudo-coherence of the
derived direct image is independent of the closed embedding into finite affine space
over the base. The derived object is arbitrary; no quasi-coherence is assumed.

Source: Stacks Project, More on Morphisms, Tag 09VC,
`lemma-relatively-pseudo-coherent`, comparison of two embeddings of a fixed affine morphism
(blueprint: lem-sfb-affine-polynomial-embedding-pseudocoherence-invariance).

Proof:
1. Write S = Spec R, X = Spec A. The two embeddings give surjections
   α : P = R[x₁,...,xₙ] → A and β : Q = R[y₁,...,yᵣ] → A. Lift the images of the
   y variables to f_b in P and those of the x variables to g_a in Q. Evaluation gives
   surjections u : T = R[x,y] → P and v : T → Q. Their composites to A agree on all
   generators, so the corresponding graph embeddings satisfy s i = t j = h.
2. The sequence y_b - f_b is weakly regular in T: after each preceding quotient the
   ring is the polynomial ring in the remaining variables, and multiplication by the
   next monic linear polynomial is injective by its leading coefficient. By
   lem-weil-pbc-regular-sequence-koszul-regular the Koszul complex of
   def-weil-pbc-koszul-complex is a bounded finite free resolution of P over T.
   The same construction resolves Q using x_a - g_a. Empty sequences give T in degree 0;
   the argument requires neither a domain nor a nonzero ring.
3. Rank-one tilde is the structure module by lem-weil-pbc-spec-tilde-free-module.
   By lem-weil-pbc-pushforward-tilde-spec the ordinary pushed-forward structure modules
   along s and t are the tilde sheaves of the evaluation modules P and Q over T.
   Their finite free resolutions and lem-pc-affine-pseudo-coherent-criterion show that
   these structure modules in degree zero are pseudo-coherent. This step makes no
   assertion about quasi-coherence of E.
4. Apply lem-sfb-closed-pushforward-pseudocoherence along s to Ri_*E and along t to Rj_*E.
   Step 3 supplies its structure-module hypothesis. At the same integer m this identifies
   each desired condition with m-pseudo-coherence of its further derived direct image.
5. By lem-pc-ringed-spaces-derived-direct-image-composition and s i = t j, both further
   images are canonically isomorphic to Rh_*E. The definition
   def-sfb-m-pseudo-coherent-complex is invariant under isomorphism: compose the local
   strictly perfect approximation with the restricted isomorphism. Its cohomology maps
   preserve isomorphisms above m and surjectivity in degree m. Combine the equivalences. -/
theorem isMPseudoCoherent_affine_polynomial_embedding_iff
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (n r : ℕ)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wN}
      (SheafOfModules.{u} (moduleRings (AffineSpace (ULift.{u} (Fin n)) S).toRingedSpace))]
    [HasDerivedCategory.{wR}
      (SheafOfModules.{u} (moduleRings (AffineSpace (ULift.{u} (Fin r)) S).toRingedSpace))]
    [∀ U : (AffineSpace (ULift.{u} (Fin n)) S).Opens,
      HasDerivedCategory.{wN} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ U : (AffineSpace (ULift.{u} (Fin r)) S).Opens,
      HasDerivedCategory.{wR} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (m : ℤ)
    (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S) [IsClosedImmersion i]
    (j : X ⟶ AffineSpace (ULift.{u} (Fin r)) S) [IsClosedImmersion j]
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f)
    (hj : j ≫ (AffineSpace (ULift.{u} (Fin r)) S ↘ S) = f) :
    IsMPseudoCoherent (AffineSpace (ULift.{u} (Fin n)) S) m
        ((schemeDerivedDirectImage i).obj E) ↔
      IsMPseudoCoherent (AffineSpace (ULift.{u} (Fin r)) S) m
        ((schemeDerivedDirectImage j).obj E) := by
  sorry

end AlgebraicGeometry.Scheme
