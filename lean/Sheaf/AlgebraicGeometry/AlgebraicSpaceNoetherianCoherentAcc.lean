module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.NoetherianQuasicoherentSubmodules

/-! # Noetherian algebraic spaces: coherence and ascending chains

Source: Stacks Project, Spaces Cohomology, Tags 07UB and 07UJ;
Morphisms of Spaces, Tag 04ZK
(blueprint: lem-sfb-space-noetherian-coherent-acc).

Local Noetherianity is tested on every small étale scheme chart. Noetherianity
adds quasi-compactness of the point space and of the diagonal in presheaves over S.
Coherence is quasi-coherence together with Stacks coherence on every chart's
Zariski restriction. Subobjects identify submodules up to isomorphism over the
ambient module; hence their equality expresses equality as subsheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-separated finite-type space over a Noetherian space is Noetherian.
Source: Stacks, Morphisms of Spaces, Tag 04ZK, and quasi-compactness and
quasi-separated composition
(blueprint: lem-sfb-space-noetherian-coherent-acc).

Proof:
1. For an étale chart T of X choose a surjective étale atlas V of B. The scheme
   W = T ×_B V covers T étale, by lem-trf-space-fibre-products-etale-covers.
   Étale composition (lem-weil-pbc-etale-composition-cancellation) makes W an
   étale chart of X. Thus W → V is locally of finite type by the chart test.
   Apply pqf-lem-locnoeth-lft and lem-trf-etale-local-noetherian-descent to T.
2. An atlas by a quasi-compact scheme gives a compact point space, by the final
   atlas topology (def-a1-space-point-topology); the converse follows from
   lem-sfb-qc-space-affine-etale-atlas. Choose such an affine atlas V of B.
   Finite type includes quasi-compactness, so X ×_B V is quasi-compact by
   lem-sfb-space-quasicompact-affine-tests. Choose an affine atlas U of that
   space. Its composite U → X is surjective étale, so X is quasi-compact.
3. The product for the absolute diagonal is over the final object S in sheaves
   over S. Compose the quasi-separated maps X → B → S, using
   lem-sfb-space-quasiseparated-test-calculus. This gives the required
   quasi-compact absolute diagonal of X. -/
theorem noetherian_of_quasiSeparated_finiteType
    {S : Scheme.{u}} (X B : AlgebraicSpace S) (f : X ⟶ B)
    (hBln : ∀ T : B.EtaleSite, IsLocallyNoetherian (B.etaleForget.obj T))
    (hBqc : CompactSpace (Point B.obj.obj))
    (hBqs : MapIsQuasiCompact (prod.lift (𝟙 B.obj.obj) (𝟙 B.obj.obj)))
    (hfqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (hfft : MapIsFiniteType f) :
    (∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)) ∧
      CompactSpace (Point X.obj.obj) ∧
      MapIsQuasiCompact (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)) := by
  sorry

/-- Coherent, quasi-coherent of finite type, and finitely presented are equivalent
on a locally Noetherian algebraic space.
Source: Stacks, Spaces Cohomology, Tag 07UB
(blueprint: lem-sfb-space-noetherian-coherent-acc).

Proof:
1. Restrict a quasi-coherent F to each étale scheme chart. Use
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
   lem-sfb-scheme-etale-module-exact-finiteness-comparison. Every chart is
   locally Noetherian, so pqf-lem-coherent-ft-locnoeth identifies coherence
   with quasi-coherence and finite type there. Local generating epimorphisms
   restrict to slice sites and glue over covering families. Thus finite type
   is detected on those charts, proving the first equivalence.
2. A local finite presentation is a quasi-coherent presentation, and its last
   map gives finite type, so a finitely presented module is coherent by step 1.
3. Conversely take a quasi-coherent finite-type module. On an affine open of
   a chart, pqf-lem-affine-open-locnoeth gives a Noetherian ring and
   lem-weil-pbc-quasi-coherent-finite-type-affine gives a finite module.
   Apply lem-sc-noetherian-finite-module-finite-presentation and the affine
   finite-presentation criterion. These affine presentations cover the chart.
   The exact finiteness comparison transfers them to the étale site, where
   the chart covers give precisely a finite presentation of F. -/
theorem coherent_iff_finiteType_iff_finitePresentation
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (F : X.Modules) :
    ((F.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F)) ↔ F.IsQuasicoherent ∧ F.IsFiniteType) ∧
    ((F.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F)) ↔ F.IsFinitePresentation) := by
  sorry

/-- Increasing sequences of quasi-coherent submodules of a coherent module
stabilize on a Noetherian algebraic space.
Source: Stacks, Spaces Cohomology, Tag 07UJ
(blueprint: lem-sfb-space-noetherian-coherent-acc).

Proof:
1. By lem-sfb-qc-space-affine-etale-atlas choose an affine surjective étale
   atlas p : U → X. The chart condition makes U locally Noetherian; since U
   is affine it is a Noetherian scheme. Étale pullback is restriction to the
   localized site (def-trf-algebraic-space) and preserves submodule inclusions.
2. Transfer the chain to Zariski modules on U using
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and exactness in
   lem-sfb-scheme-etale-module-exact-finiteness-comparison. The module is
   coherent by hypothesis. Apply lem-weil-pbc-noetherian-acc-quasi-coherent
   to get a single index n where every later pulled-back submodule agrees.
3. For any chart T and section of G m, pull back to T ×_X U. Stabilization
   puts it in G n there. These local sections agree on overlaps, since their
   images in F agree and G n → F is mono. Glue by the sheaf axiom. This
   gives G m ≤ G n on every chart; monotonicity gives the reverse inclusion.
   Equality of subobjects is exactly equality of these subsheaves. -/
theorem noetherian_coherent_submodules_acc
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : MapIsQuasiCompact (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (F : X.Modules) (hFqc : F.IsQuasicoherent)
    (hFcoh : ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F)) :
    ∀ G : ℕ → Subobject F, Monotone G →
      (∀ n : ℕ, (G n : X.Modules).IsQuasicoherent) →
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m → G m = G n := by
  sorry

/-- Every nonempty set of quasi-coherent ideals on a Noetherian algebraic space
has a maximal member for inclusion.
Source: Stacks, Spaces Cohomology, Tags 07UB and 07UJ; Spaces More Morphisms, Tag 08BE
(blueprint: lem-sfb-space-noetherian-coherent-acc).

Proof:
1. The structure module is coherent by Tag 07UB: its restriction to each chart
   has the one-generator free presentation, and is therefore coherent by
   the preceding equivalences. A quasi-coherent ideal is a quasi-coherent
   submodule of this structure module.
2. Apply the ascending chain conclusion above to these submodules. If a
   nonempty set Z of ideals had no maximal member, choose I₀ in Z and,
   recursively by classical choice, a strictly larger Iₙ₊₁ in Z. This gives
   a strictly increasing sequence of quasi-coherent submodules of O_X,
   contradicting stabilization. Thus Z has a maximal member, including
   for the empty space, where its only ideal is the zero ideal. -/
theorem noetherian_quasiCoherent_ideals_maximal
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : MapIsQuasiCompact (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))) :
    ∀ Z : Set (QuasiCoherentIdeal X), Z.Nonempty →
      ∃ I ∈ Z, ∀ J ∈ Z, I ≤ J → J = I := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
