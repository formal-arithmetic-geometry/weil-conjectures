## Worker report

The delivery states `AlgebraicGeometry.ProEtale.integralModel_open_closed_pieces` in
`Sheaf.Paper.IntegralModelOpenClosedPieces`. Its only postponed proof is that theorem.
The other four declarations have real construction data and specialize published
operations to the continuous coefficient presentation already used by the constructibility
definition. The node changes only in `lean`. No statement correction or new node is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A prime ell and finite E/Q_ell | `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` in the explicitly bound section. |
| The ring of integers, canonical topology, and chosen uniformizer | `latticeCoefficientIntegers l E` inside `WithAbs (Padic.coefficientExtensionAbsoluteValue l E)` is the published valuation subring with its actual induced topology. The coefficient-extension node already chooses `Padic.coefficientExtensionUniformizer`; the present statement uses no particular uniformizer or power and does not restrict that choice. |
| X is a noetherian scheme | `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's class is locally noetherian and quasi-compact, equivalently a finite affine cover by noetherian spectra. |
| X has finite dimension | `_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n`. This retains the empty scheme, whose dimension is bottom. |
| ell is invertible on X | `_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`. This is the local-ring criterion for invertibility of the global natural-number section. |
| A_Y(V)=C(|V|,A) and E_Y(V)=C(|V|,E) | The existing `latticeCoefficientSheaf` and `latticeModuleRing`, using the integer subring and `WithAbs` field above. These use `ULift C(|V|,T)`, preserving exactly continuous functions and their pointwise operations. They are the coefficient presentation of the recorded constructibility definition. |
| Sheaf modules and S_Y(M)=E_Y tensor_(A_Y) M | `SheafOfModules.{u+1}` and `integralModelRationalize`. The latter is exactly `SheafOfModules.changeOfRings` along the published `integralLatticeCoefficientMap`, hence ordinary sheafified scalar extension, with the target E_Y action. |
| Closed immersion and complementary open immersion | `(i : Z ⟶ X) [IsClosedImmersion i]`, `(U : X.ProEt) [IsOpenImmersion U.hom]`, and `hU : Set.range U.hom = (Set.range i)ᶜ`. An open immersion is weakly etale, so packaging it as a site object discards no case. Quasi-compactness is not an extra hypothesis: it follows from noetherianity as in proof step 1. |
| Module inverse images, direct image and extension by zero | `Scheme.proEtaleRingModulePullback`, `continuousModuleDirectImage`, and `continuousModuleExtensionByZero`. Direct image first restricts scalars along the actual continuous coefficient map and then uses the recorded `Scheme.proEtaleRingedDirectImage`. Extension uses `openSliceModules` and the recorded `Scheme.proEtaleRingedExtensionByZero`, retaining its direct-sum presheaf/sheafification construction. |
| Coefficients identified by continuous pullback | The existential coefficient isomorphisms `cU,cZ` have homs equal to `continuousCoefficientInverseImageMap` for the rational field. Thus the displayed inverse-image functors have the specified continuous coefficient action. The integral direct image uses that same canonical map in its definition, and the open slice map is sectionwise the identity. The coefficient restriction theorem supplies invertibility; no arbitrary ring map is an input hypothesis. |
| M_U and M_Z are constructible integral sheaves | Universally quantified `MU,MZ` and the two `IsContinuousConstructible` hypotheses. Their noetherian-space arguments are the explicit consequences of the immersions being embeddings into X, with source `α := X`. The published predicate includes its finite stratification, covering families, and finitely presented A-module local models; none is replaced by finite freeness or global constancy. |
| Q=j_! M_U is constructible | The first `IsContinuousConstructible X ... ((continuousModuleExtensionByZero ...).obj MU)` conjunct. |
| P=i_* M_Z is constructible | The second `IsContinuousConstructible X ... ((continuousModuleDirectImage ...).obj MZ)` conjunct. |
| S_X Q isomorphic to j_! S_U M_U | The displayed E_X-module isomorphism `eU`. |
| S_X P isomorphic to i_* S_Z M_Z | The displayed E_X-module isomorphism `eZ`. |
| Any E_X-module L with specified isomorphisms on U and Z | The final universal quantifiers `L`, `α`, `β`, with targets the actual coefficient-identified inverse images. L has no constructibility assumption. |
| Comparisons identify the canonical open-closed sequence | `aj` and `ai` are adjunctions for the displayed geometric module functors. The first arrow is `eU.hom ≫ j_!.map α.hom ≫ aj.counit.app L`; the second is `ai.unit.app L ≫ i_*.map β.inv ≫ eZ.inv`. These are precisely the maps in node proof step 6, so they specify the end maps, rather than merely asserting the existence of some exact sequence. |
| The displayed sequence is short exact | `Mono` of the first arrow, `Epi` of the second, and `(ComposableArrows.mk₂ first second).Exact`. In the abelian sheaf-module category this is exactly the recorded exact-sequence definition, including zero composition. |

The coefficient isomorphisms and adjunctions are existential construction witnesses in the
conclusion, not additional hypotheses. Both rationalization comparisons are supplied before
quantifying over L, alpha, beta, so the same comparisons work for every specified L.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient-extension
  constructions: `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  and `coefficientExtensionUniformizer`; the node's primary theorem is
  `Padic.finite_coefficientExtensionRing`, read with its positive-level signature.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the exact
  abbreviation of `SheafOfModules`, with the Mathlib category and abelian structures.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the published tensor
  universe interface. The ordinary scalar extension is the public
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct` construction
  `SheafOfModules.changeOfRings`, already used by the constructibility dependency.
- `Sheaf.Paper.ContinuousConstructibleModule`: `IsContinuousConstructible`,
  `continuousCoefficientModule`, `continuousModulePullback`, and
  `continuousCoefficientInverseImageMap`, including the latter's direct-image adjunct.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`: `proEtaleModuleCoefficients`,
  `proEtaleRingedDirectImage`, `proEtaleRingedExtensionByZero`, and the full
  `proEtale_ringed_open_closed` signature, including its slice equivalence,
  adjunction witnesses and unit/counit exactness.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `continuousCoefficientImmersionRestriction`. Its rational and integral comparison
  maps are normalized on continuous functions and compatible with coefficient inclusion.
  This module is a proof import: the statement uses the lattice coefficient encoding
  already fixed by `IsContinuousConstructible`, rather than making another coefficient ring.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  `proEtaleModuleInverseImage`, `proEtaleSheafAdjunction`. The published
  `Sheaf.AlgebraicGeometry.ProEtaleOperations.proEtaleRingModulePullback` specializes
  inverse image followed by `changeOfRings` to the displayed coefficient isomorphisms.
- `Mathlib.Algebra.Homology.ExactSequence`: `ComposableArrows.Exact`, with the
  recorded `ShortComplex.ShortExact` equivalent used for the semantic check.

Recorded proof dependencies have their stated module imports, notably
`FiniteLocallyClosedStratification`, `ProEtaleInverseImageTensorComparison`,
`ProEtaleWeaklyEtaleLocalization`, and `RingedSliceExtensionTensor`. The noetherian
minimal-element and compact-subsets nodes are Mathlib leaves, whose listed matches
were read in `Noetherian.lean` and `Topology/NoetherianSpace.lean`.
`lem-weil-pbc-proetale-closed-underived-projection` has no Lean record yet and is a
proof-only dependency: its mathematical statement is reproduced in the proof plan,
not assumed as a hypothesis or used to manufacture definition data. No missing object
is needed from it for this stage-2 signature.

Edge cases checked before finalizing: X empty (finite-dimension bound still holds), U
empty, Z empty, i the identity with empty complement, zero MU/MZ/L, torsion integral
modules whose rationalization vanishes, and MU/MZ that are constructible but not
locally free. The slice transport handles empty objects and has no nonempty-index
hypothesis. The finite-stratification predicate permits an empty scheme. No flatness,
torsion-freeness, lissity of L, or restriction to connected schemes was added.
The site retains object universe u+1, Hom universe u, and module universe u+1.

Searches made:

- `msearch.py ... leanfinder "Extension by zero and closed direct image preserve continuous
  constructible integral sheaves and commute with rationalization on the proetale site"`:
  eight unrelated condensed/profinite and restriction-adjunction results; no match.
- `msearch.py ... loogle "SheafOfModules.changeOfRings, ShortComplex.ShortExact"`:
  zero hits, service reported unknown `SheafOfModules.changeOfRings` (it is a project
  declaration, whose actual source was then read).
- `msearch.py ... grep "extensionByZero|closed.*projection" Algebra/Category/ModuleCat/Sheaf`:
  zero hits for the statement.
- `msearch.py ... leansearch "Extension by zero and closed direct image commute with scalar
  extension for constructible sheaves"`: eight general function-extension, sheafification,
  and module-localization hits; none states this theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id, integral/open/closed
  combinations and `IsContinuousConstructible`: found the recorded predicate and several
  condensed integral-model theorems, not this theorem on the recorded module category.
  The condensed gluing theorem was read; it has different objects and omits the two
  specified ordinary comparison isomorphisms and their transported arrows.
- Exact-name searches in both project roots found no declaration named by this delivery.

Sources checked directly: Bhatt--Scholze PDF, Lemma 6.8.13 (its final constructible
filtration paragraph), and the local Stacks source at `proetale.tex`,
`lemma-ses-associated-to-open`, and `sites-modules.tex`, `lemma-extension-by-zero`.
The theorem docstring retains all six proof steps and names the nodes they use.
No statement fault or disputed assertion was found.

Validation: the final module passed `scompile.py NO
lem-weil-pbc-integral-model-open-closed-pieces <module>` in both sandbox and library-name
modes, with no warnings or errors (11.4 and 9.0 seconds respectively).

## Second reading by NO

I reopened the node and complete final module for a separate clause-by-clause rereading;
the correspondence table above records that check. This was a second pass by the same
worker, not an independent agent review: the dispatch brief prohibits starting agents
and assigns the independent review to the maintainer.

The rereading checked that the displayed isomorphisms are E_X-linear, that the coefficient
maps are fixed to continuous pullback, that `MU` and `MZ` use the recorded integral
constructibility predicate, that no quasi-compactness assumption was added, and that L
is arbitrary with supplied rather than merely existential restriction isomorphisms.
The arrow directions agree with node proof step 6: alpha hom on the open side, beta
inverse on the closed side, followed by eZ inverse. It also checked that the comparison
witnesses precede L and that the exactness assertion includes both outer zero terms via
Mono/Epi. Initial compiler diagnostics exposed an inference issue for the noetherian
structure of the open source and invalid attempts to project functors from an adjunction;
these were repaired by fixing the inducing map's source to X and spelling out the actual
functors. Final compilation is clean. No mathematical mismatch remained.
