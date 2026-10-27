module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Sheaf.RingTheory.AlgebraicFieldImagePrincipalNeighbourhood
import Sheaf.AlgebraicGeometry.FerrandSchemePushout
import Sheaf.RingTheory.FibreProductAlgebraFlatPresentation
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.RingTheory.Etale.QuasiFiniteAtPrime
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism

/-! # Etale scheme patching over a Ferrand pushout

Source: Stacks Project, More on Morphisms, Tags 0ECK and 0ECL, with Situation 0ECI;
the arbitrary-etale counit uses the flat-algebra assertion of Tag 08KQ and Zariski gluing.
(blueprint: lem-sfb-ferrand-etale-scheme-patching).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separated etale schemes patch over a closed-integral Ferrand pushout, with the
specified cartesian component squares. Every etale base change of the original square
is again a scheme pushout, including non-separated and non-quasi-compact base changes.

Source: Stacks Project, More on Morphisms, Tags 0ECK and 0ECL, Situation 0ECI;
More on Algebra, Tag 08KQ (flat counit).
(blueprint: lem-sfb-ferrand-etale-scheme-patching).

The overlap isomorphism is over Z by `hφ`. Its composite with the first projection
is the specified map from Z' to T'. Each `IsPullback` conclusion says exactly that
the canonical comparison to the chosen fibre product is an isomorphism, preserving
both projections. In particular the overlap square uses this very `φ`, not an
unspecified isomorphic overlap. In the converse, `Over.pullback q` writes the inverse
images as Z ×_P U, X ×_P U and T ×_P U; symmetry identifies these with U ×_P Z,
U ×_P X and U ×_P T, with all the canonical maps preserved.

Proof plan from the node:
1. Base change makes Z' → X' closed and Z' → T' integral. Its fibre over t' is
   affine and integral over κ(t'), hence quasi-compact, using integral base change
   and lem-weil-pbc-affine-scheme-qcqs. Its image lies over a suitable affine A in X.
2. Cover this image by finitely many affine opens inside u⁻¹(A), with union Q.
   Q → A is separated and quasi-compact by qcqs permanence. Open-immersion etaleness,
   scheme-etale-source-target-properties and the affine etale criterion show its affine
   charts are etale. The etale-ring-map-quasi-finite lemma and pqf-def-quasifinite
   give local quasi-finiteness and finite type. Apply lemma-nagata-zmt-quasi-affine-source.
3. Embed Q into an affine scheme. Apply
   lem-sfb-algebraic-field-image-principal-neighbourhood to the integral field algebra
   of the fibre: a principal affine neighbourhood contains the whole image inside Q.
   Principal-localization-open-immersion identifies it as an affine open of X'.
   Empty fibres are allowed, with the empty affine open.
4. Apply lem-sfb-ferrand-scheme-pushout to construct P'. The compatible component
   maps induce r : P' → P by the pushout universal property. Uniqueness identifies
   the supplied P with the Ferrand pushout and its quotient topology and affine charts.
5. On a compatible affine W in P, write R = A ×_C B with A → C surjective.
   The restricted primed data still have affine fibre neighbourhoods by steps 1–3,
   now inside X'_W. The open-restriction clause of the Ferrand theorem identifies
   r⁻¹(W) with their pushout. Its compatible affine charts have E = A₁ ×_C₁ B₁.
   The specified cartesian overlap gives C₁ = A₁/IA₁ = B₁ ⊗_B C, respecting φ,
   by lem-weil-pbc-fibre-product-affine-spectra.
6. The component ring maps are etale. Apply lem-sfb-fibre-product-algebra-etale
   to obtain R → E etale. The affine etale criterion and source-target locality
   give Etale r.
7. Lem-sfb-patched-module-base-change identifies the canonical ring maps
   E ⊗_R A → A₁ and E ⊗_R B → B₁ as bijections. The affine fibre-product formula
   gives the component comparison isomorphisms; their inverses agree on overlaps.
   The fibre-product universal property gives the Z' comparison, preserving φ
   and every projection.
8. On each affine W, the primed components are separated schemes by separated
   base change and lem-sc-separated-over-affine-scheme-separated. The separatedness
   clause of the Ferrand theorem over Spec ℤ makes r⁻¹(W) separated. Pull back
   its absolute diagonal to its relative diagonal over W using closed-immersion
   base change. Lem-sfb-separated-lfp-target-open-locality proves IsSeparated r.
9. For arbitrary etale q, choose an affine H₀ in U mapping into a compatible W.
   The affine flat criterion gives R → H flat. The flat clause of
   lem-sfb-fibre-product-algebra-flat-presentation gives the canonical isomorphism
   H ≅ (H ⊗_R A) ×_(H ⊗_R C) (H ⊗_R B). The affine fibre-product formula and
   lem-sfb-affine-closed-pinching-pushout make the inverse-image square a pushout
   over H₀; the same holds on affine refinements of intersections.
10. Compatible maps from the two inverse images to any scheme glue uniquely on
    these affine charts by lem-weil-pbc-affine-opens-basis and
    lem-weil-pbc-scheme-morphism-gluing. This gives the global pushout, requiring
    neither separatedness nor quasi-compactness of q.
-/
theorem ferrand_etale_scheme_patching
    (S : Scheme.{u}) (Z X T P : Over S)
    (i : Z ⟶ X) (j : Z ⟶ T) (a : X ⟶ P) (b : T ⟶ P)
    [IsClosedImmersion i.left] [IsIntegralHom j.left]
    (h : ∀ t : T.left, ∃ A : X.left.Opens, IsAffineOpen A ∧
      ∀ z : Z.left, j.left z = t → i.left z ∈ A)
    (hs : IsPushout i.left j.left a.left b.left)
    (X' T' : Scheme.{u}) (u : X' ⟶ X.left) (v : T' ⟶ T.left)
    [IsSeparated u] [Etale u] [IsSeparated v] [Etale v]
    (φ : pullback u i.left ≅ pullback v j.left)
    (hφ : φ.hom ≫ pullback.snd v j.left = pullback.snd u i.left) :
    (∃ (P' : Scheme.{u}) (a' : X' ⟶ P') (b' : T' ⟶ P') (r : P' ⟶ P.left),
      IsPushout (pullback.fst u i.left) (φ.hom ≫ pullback.fst v j.left) a' b' ∧
      IsSeparated r ∧ Etale r ∧
      IsPullback a' u r a.left ∧ IsPullback b' v r b.left ∧
      IsPullback (pullback.fst u i.left ≫ a') (pullback.snd u i.left)
        r (i.left ≫ a.left)) ∧
    (∀ (U : Scheme.{u}) (q : U ⟶ P.left), Etale q →
      IsPushout
        ((Over.pullback q).map
          (Over.homMk i.left rfl : Over.mk (i.left ≫ a.left) ⟶ Over.mk a.left)).left
        ((Over.pullback q).map
          (Over.homMk j.left hs.w.symm : Over.mk (i.left ≫ a.left) ⟶ Over.mk b.left)).left
        (pullback.snd a.left q) (pullback.snd b.left q)) := by
  sorry

end AlgebraicGeometry
