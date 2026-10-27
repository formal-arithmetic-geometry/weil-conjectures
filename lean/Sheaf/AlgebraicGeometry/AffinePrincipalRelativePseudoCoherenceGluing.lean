module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Span
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.RingTheory.LinearEquationLocalizationPolynomial
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Gluing polynomial-chart pseudo-coherence on a principal affine cover

Source: Stacks Project, More on Morphisms, Tag 09VE,
`lemma-glue-relative-pseudo-coherent`, implication (1) to (2)
(blueprint: lem-sfb-affine-principal-relative-pseudocoherence-gluing).

The index of the principal-open cover is arbitrary. Restrictions are derived pullbacks,
and the derived object need not have quasi-coherent cohomology.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

/-- Polynomial-chart `m`-pseudo-coherence glues along any principal-open cover of an
 affine scheme of finite type over an affine base. Finite type is expressed by
 `LocallyOfFiniteType f`: quasi-compactness follows from the two affine schemes.
 Source: Stacks Project, More on Morphisms, Tag 09VE, implication (1) to (2)
 (blueprint: lem-sfb-affine-principal-relative-pseudocoherence-gluing).

 Proof plan (the eight steps of the DAG node):
 1. The basic-open unit-ideal criterion gives a finite unit relation
    `∑ bᵢ cᵢ = 1`. Finite type supplies algebra generators `aⱼ`. Set
    `P = R[xⱼ,yᵢ,zᵢ]`, `h = ∑ yᵢ zᵢ - 1`, `B = P/(h)` and `T = Spec B`.
    The surjections to `A` give closed embeddings `k : X → T` and
    `q : T → Spec P`. Use the basic-open and affine finite-type nodes.
 2. Grading by total degree in the `yᵢ` shows multiplication by `h` injective.
    The tilde finite-limit and tilde-Gamma adjunction nodes sheafify
    `0 → P → P → B → 0`; the affine pushforward formula identifies its last
    sheaf with `q_* O_T`. This is a two-term finite free resolution, hence
    pseudo-coherent by `def-pur-pseudo-coherent-complex`.
 3. On `Wᵢ = D_T(yᵢ)`, polynomial elimination from the linear-equation
    localization node gives `B[1/yᵢ] = Cᵢ[1/yᵢ]`, where `Cᵢ` retains all
    variables except `zᵢ`. Write this Laurent ring as `Cᵢ[v]/(yᵢ v - 1)`
    to obtain a closed embedding `rᵢ : Wᵢ → Spec Cᵢ[v]`.
 4. Comparing coefficients in `v` shows multiplication by `yᵢ v - 1`
    injective over any coefficient ring. The same exact sheafification gives
    a two-term finite free resolution of `(rᵢ)_* O_{Wᵢ}`.
 5. The localized surjection gives a closed embedding `kᵢ : Uᵢ → Wᵢ`.
    Its composite `jᵢ = rᵢ ∘ kᵢ` embeds `Uᵢ` into finite affine space:
    the old generators together with `bᵢ⁻¹` generate its ring over `R`.
 6. Apply `lem-sfb-affine-polynomial-embedding-pseudocoherence-invariance`
    to transfer the supplied local hypothesis to `jᵢ`. Derived-direct-image
    composition identifies this with `R(rᵢ)_* R(kᵢ)_* (E|Uᵢ)`. Step 4 and
    the reverse implication of `lem-sfb-closed-pushforward-pseudocoherence`
    make `R(kᵢ)_* (E|Uᵢ)` `m`-pseudo-coherent.
 7. Open restriction of derived direct image identifies this with
    `(Rk_* E)|Wᵢ`, since `k⁻¹(Wᵢ) = Uᵢ`. The `Wᵢ` cover `T` by the unit
    relation. Refine their strictly perfect approximations to obtain
    `m`-pseudo-coherence on `T`; derived-pullback composition identifies
    the iterated restrictions. For an empty selected family, `T` is empty.
 8. Step 2 and the forward closed-pushforward implication give
    `m`-pseudo-coherence of `Rq_* Rk_* E`. Derived-direct-image composition
    gives the required global embedding and pushforward. These comparisons
    apply to arbitrary derived objects, as required. -/
theorem exists_affine_embedding_mPseudoCoherent_of_principal_cover
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : schemeDerivedCategory X) (m : ℤ)
    (I : Type v) (b : I → Γ(X, ⊤))
    (hcover : (⨆ t : I, X.basicOpen (b t)) = ⊤)
    (hlocal : ∀ t : I, ∃ n : ℕ,
      ∃ i : (X.basicOpen (b t)).toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) S,
        IsClosedImmersion i ∧
        i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = (X.basicOpen (b t)).ι ≫ f ∧
        Scheme.IsMPseudoCoherent (AffineSpace (ULift.{u} (Fin n)) S) m
          ((schemeDerivedDirectImage i).obj
            ((derivedPullback (X.basicOpen (b t)).ι).obj E))) :
    ∃ n : ℕ, ∃ i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S,
      IsClosedImmersion i ∧
      i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f ∧
      Scheme.IsMPseudoCoherent (AffineSpace (ULift.{u} (Fin n)) S) m
        ((schemeDerivedDirectImage i).obj E) := by
  sorry

end AlgebraicGeometry
