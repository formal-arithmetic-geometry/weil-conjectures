module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.UnmarkedFiniteOpenPartsSpace
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.UniversalIsomorphismOpen
import Sheaf.AlgebraicGeometry.SpaceOpenChartTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Étale section spaces along finite locally free morphisms

Source: Stacks Project, Criteria for Representability, Tag 05XR,
lemma-space-of-sections (blueprint: lem-sfb-etale-sections-finite-locally-free).

Sections of `W_V → Z_V` are written as maps `Z_V → W` over `Z`. The missing component
of the map to `W_V` is the structure map to `V`, so these are exactly the sections
in the source. `Over.pullback` supplies the actual base changes and restriction maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The section functor along a finite locally free map is represented by an algebraic
space over `U`, étale on every étale scheme chart. The equivalences are natural for
all scheme maps over `U`, not only étale maps. No fixed rank, positive rank,
separatedness or quasi-compactness of `q` is assumed.
Source: Stacks Project, Criteria for Representability, Tag 05XR,
lemma-space-of-sections (blueprint: lem-sfb-etale-sections-finite-locally-free).

Proof:
1. Representability of `q` makes `W` a scheme by the identity test on `Z`. Sections
   are maps to `W` over `Z`. They glue uniquely for fppf covers, since their base
   changes cover `Z_V` (lem-trf-fppf-covering-base-change). The finite, flat and
   locally finitely presented properties of `p` survive base change by
   lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change
   and lem-weil-pbc-qcqs-morphism-permanence.
2. If `q` is separated, `W → U` is separated and locally of finite type, by
   lem-weil-pbc-finite-proper and lem-weil-pbc-proper-fp-permanence. Apply
   lem-sfb-unmarked-finite-open-parts-space. A section is an étale monomorphism
   (lem-trf-space-chartwise-etale-permanence), hence an open immersion by
   lem-sfb-space-etale-monomorphism-open. Its image is finite over the test.
   The image determines the section as the inverse of its map to `Z_V`.
3. For any finite open part `D`, apply lem-sfb-universal-isomorphism-open to
   `D → Z_V` over `V`. Its hypotheses follow from finite-implies-proper,
   lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-etale-base-change-finite-limits,
   lem-pc-flat-compose and lem-sbc-locally-finite-presentation-composition.
   The resulting open of `V` represents exactly those base changes where
   `D → Z_V` is an isomorphism, equivalently a section with image `D`.
4. Thus the section functor is open in the finite-open-part space. Apply
   lem-sfb-presheaf-space-target-bootstrap, lem-a1-space-open-chart-tests and
   lem-trf-space-chartwise-etale-permanence to finish the separated case.
5. In general choose an affine étale scheme cover `W' → W` by
   lem-a1-space-affine-etale-cover. Its maps to `W` and `Z` are separated,
   using lem-weil-pbc-affine-source-morphism-separated on components. The
   separated case gives its section space `F'`. Above a section over `V`, the
   lifting functor is the section functor of `K = W'_V ×_{W_V} Z_V → Z_V`.
   This is separated surjective étale, by
   lem-trf-space-representable-etale-scheme-tests and lem-weil-pbc-separated-base-change.
6. A lift corresponds to a section of `K` by pairing with the identity of `Z_V`;
   projection is the inverse, compatibly with every base change. The separated
   case represents this functor by a space étale over `V`.
   Lemma lem-sfb-finite-etale-cover-local-sections supplies sections étale locally,
   so `F' → F` is surjective and étale on all scheme tests.
7. Apply lem-sfb-fppf-space-atlas-bootstrap to the fppf sheaf `F`. Compose a scheme
   atlas of `F'` with `F' → F`; its scheme tests are surjective étale by
   lem-trf-space-chartwise-etale-permanence. Its composite to `U` is étale.
   Clause (3) of lem-trf-space-etale-source-atlas-detection proves the asserted
   étaleness on every scheme chart. The section bijections and their restriction
   law are the original functor's, giving the displayed natural equivalences.
   No step uses constant rank or excludes the empty finite scheme. -/
theorem exists_etale_sections_finite_locally_free {S : Scheme.{u}} (Z U : Over S)
    (p : Z ⟶ U) [Scheme.Hom.IsFiniteLocallyFree p.left]
    (W : AlgebraicSpace S) (q : W ⟶ schemeSpace Z) (hq : IsEtale q.hom.hom) :
    ∃ (E : AlgebraicSpace S) (r : E ⟶ schemeSpace U)
      (e : ∀ V : Over U,
        {a : yoneda.obj V.left ⟶ E.obj.obj // a ≫ r.hom.hom = yoneda.map V.hom} ≃
          {s : yoneda.obj ((Over.pullback p).obj V).left ⟶ W.obj.obj //
            s ≫ q.hom.hom = yoneda.map ((Over.pullback p).obj V).hom}),
      (∀ (V V' : Over U) (f : V' ⟶ V)
        (a : {a : yoneda.obj V.left ⟶ E.obj.obj // a ≫ r.hom.hom = yoneda.map V.hom})
        (a' : {a : yoneda.obj V'.left ⟶ E.obj.obj //
          a ≫ r.hom.hom = yoneda.map V'.hom}),
        yoneda.map f.left ≫ a.val = a'.val →
          (e V' a').val = yoneda.map ((Over.pullback p).map f).left ≫ (e V a).val) ∧
      (∀ (T : Over S) (c : yoneda.obj T ⟶ E.obj.obj),
        IsEtale c → Etale (yoneda.preimage (c ≫ r.hom.hom)).left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
