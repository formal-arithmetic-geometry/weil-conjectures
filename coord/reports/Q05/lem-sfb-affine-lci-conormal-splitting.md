## Worker report

The module `Sheaf.AlgebraicGeometry.AffineLciConormalSplitting` states
`AlgebraicGeometry.AlgebraicSpace.affine_lci_conormal_splitting`, with its sole
proof `sorry`. Two real helper definitions belong to this same conormal notion:
`IsSpaceConormalQuotient` fixes the quotient on ideal tensor generators, and
`conormalOpenMap` is the actual Yoneda map of a Zariski open immersion.
No data are chosen from an existence theorem. No node statement was corrected.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`,
lemma-unramified-lci (06CB) and lemma-transitivity-conormal-lci (06CC), and
`literature/stacks-project/criteria.tex`, lemma-lci-unobstructed (06D8), first
paragraph. The former gives variable-rank finite local freeness and exactness;
the latter explicitly uses affineness to choose the splitting.

Hypothesis and clause correspondence:

- Base scheme S: `{S : Scheme.{u}}`. The explicit universe u is that of the
  existing algebraic-space and small-site module constructions; scheme objects
  and site morphisms retain their existing sizes. No equality of independent
  universes or extra size hypothesis is imposed.
- Affine source Z over S: `(Z : Over S) [IsAffine Z.left]`, regarded as the
  actual Yoneda algebraic space `schemeSpace Z`. This covers every affine scheme
  over S, including the empty affine scheme.
- Spaces Y and X and their maps: `{Y X : AlgebraicSpace S}`,
  `(u : schemeSpace Z ⟶ Y) (v : Y ⟶ X)`.
- Both maps formally unramified, using the square-zero scheme tests of the
  dependency: `hu : SpaceFormallyUnramified u` and
  `hv : SpaceFormallyUnramified v`. No representability or finite presentation
  of v is added.
- The lci condition on u: `RelativeFiniteHilbert.SpaceProperty
  (fun _ _ f ↦ RelativeFiniteHilbert.SchemeLci f) u.hom.hom`. The first predicate
  gives compatible surjective etale target and source scheme charts. The second
  gives, near each source point, a closed immersion followed by a smooth map,
  with `CotangentPresentation.IsKoszulImmersion` for the actual immersion ideal.
  That existing predicate uses finite Koszul-regular generators of `i.ker` on
  affine neighbourhoods and permits the empty sequence and varying length.
  It does not substitute classical regularity for Koszul regularity.
- Universal conormals: WYX, WZX, WZY and their inclusions and structure maps are
  arbitrary specified universal first-order thickenings, with hypotheses hYX,
  hZX, hZY using `IsUniversalSpaceFirstOrderThickening` for v, u followed by v,
  and u respectively. Their existence is the recorded dependency theorem, so
  these are presentations of the named conormals, not extra geometric
  assumptions. `spaceConormal kYX`, `spaceConormal kZX`, `spaceConormal kZY`
  are the dependency's tensor pullbacks of the actual structural kernel ideals.
- Canonical map of universal thickenings extending u: the existential a satisfies
  `kZX ≫ a = u ≫ kYX` and `a ≫ qYX = qZX`. Universality of hYX makes it unique.
  `IsSpaceConormalMap u a kZX kYX lam` fixes the first arrow on every compatible
  chart and every actual ideal tensor. The domain is exactly
  `(moduleTensorPullback u).obj (spaceConormal kYX)`.
- Canonical quotient for the composite: b satisfies `kZY ≫ b = kZX` and
  `b ≫ qZX = qZY ≫ v`. Universality of hZX makes it unique.
  `IsSpaceConormalQuotient b kZY kZX ρ` says that rho sends the pullback of each
  ideal section in WZX to its ring-map image in the ideal of WZY, for every
  compatible chart and lift. It is the identity-source specialization of the
  dependency's tensor normalization, rather than an arbitrary epimorphism.
  For closed v, the dependency's normalized closed-immersion identification
  gives precisely the pulled-back defining ideal modulo its square; the same
  section formulas retain that normalization.
- Finite locally free quotient, Zariski locally and with variable rank:
  `∀ z : Z.left, ∃ U : Z.left.Opens, z ∈ U ∧ ∃ r : ℕ, Nonempty (...)`.
  The displayed isomorphism identifies the tensor restriction along the actual
  open immersion with `∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit ...`.
  A finite product of modules is canonically their finite direct sum, including
  the empty product. The rank r is chosen after U, with no constant-rank bound.
  This explicitly states Zariski local freeness, not merely etale local freeness.
- All terms are quasi-coherent: the three `.IsQuasicoherent` clauses, using the
  existing Mathlib predicate on the algebraic-space module category.
- Short exact sequence with these very arrows: `∃ h : lam ≫ ρ = 0,
  (ShortComplex.mk lam ρ h).ShortExact`. Mathlib's ShortExact means exactness,
  monicity of lam and epimorphicity of rho. Thus both endpoint zeroes and the
  middle exactness are present.
- Linear section: `∃ s : spaceConormal kZY ⟶ spaceConormal kZX,
  s ≫ ρ = 𝟙 (spaceConormal kZY)`. These are module-sheaf morphisms, hence linear.
- The specified direct-sum isomorphism: `IsIso (prod.fst ≫ lam + prod.snd ≫ s (with fully annotated product morphism types))` on the product of the first and last terms. Module sheaves
  have sectionwise finite products and additive Hom groups; the product is the
  canonical finite biproduct, with inclusions `(id,0)` and `(0,id)`. Consequently
  the first summand of this exact arrow is lam and the second is s. Using the
  finite-product realization needs no global sheafification or arbitrary
  coproduct structure. An IsIso assertion on the specified arrow, rather than
  a bare Nonempty isomorphism, retains both summands.

Dependency declarations used, with their source modules opened:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and Scheme.Hom;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, EtaleSite,
  structureSheaf, Modules, IsEtale and IsSurjective.
- `Sheaf.AlgebraicGeometry.SpaceUniversalConormal`: SpaceFormallyUnramified,
  spaceKernel, spaceConormal, spaceConormalSection, IsSpaceConormalMap; its
  universal-conormal, closed-identification and map theorems supply the proof
  interfaces. Their full declarations and normalization docstrings were read.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: IsClosedImmersion;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: Smooth. These occur in SchemeLci.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  RingTheory.Sequence.IsKoszulRegular, using vanishing of nonzero Koszul homology.
- `Sheaf.CategoryTheory.RingedSiteModules`: CategoryTheory.ringedSiteModules,
  the transparent general-site SheafOfModules category, and Mathlib's actual
  sectionwise linear morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the specialized
  quasi-coherence infrastructure; the predicate is SheafOfModules.IsQuasicoherent.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: moduleTensorPullback,
  moduleTensorAdjunction and moduleTensorSection. The last is multiplication of
  the chart projection of the adjunction unit, fixing local tensor normalization.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: schemeSpace, owned by the
  already-landed definition node `def-trf-scheme-algebraic-space`.
- `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`:
  RelativeFiniteHilbert.SpaceProperty and RelativeFiniteHilbert.SchemeLci, owned
  by already-landed `def-sfb-relative-finite-hilbert-groupoids`.
- `Sheaf.AlgebraicGeometry.SpaceUniversalThickeningEtaleTransfer`:
  IsUniversalSpaceFirstOrderThickening, owned by already-landed definition node
  `def-sfb-space-universal-first-order-thickening`.

Only these three already-landed definition owners were added to stmt_deps.
No new node or dependency repair module is necessary. All recorded proof-dependency
modules that already have Lean records are imported privately, unless already
public statement dependencies. The not-yet-stated proof nodes are not imported:
lem-sfb-unramified-lci-koszul-etale-charts,
lem-sfb-universal-conormal-chart-transitivity,
lem-sfb-etale-finite-free-zariski-descent,
lem-sfb-h1-regular-quotient-ideal-intersection, and
lem-sfb-scheme-etale-module-exact-finiteness-comparison.
Their arguments and uses are retained in the theorem's seven-step proof docstring.

Edge cases checked before writing: empty Z (the frame condition is vacuous and
module splitting is unique), rank zero and the empty Koszul sequence (finite
product over Fin 0 is the zero module), identities/etale u (zero conormal
quotient and an isomorphic first arrow), identity/etale v (zero first term),
v a closed immersion (the ideal-square identification above), arbitrary
nonrepresentable formally unramified v, and disconnected affine Z with different
ranks on different components. No nonzero ideal, nonempty scheme, globally
constant rank, Noetherian, separated, or representability hypothesis is added.

Searches made for an existing statement:

- `msearch.py ... leanfinder`, query: "For affine Z and formally unramified maps
  Z to Y to X with Z to Y a local complete intersection the canonical conormal
  transitivity sequence is split short exact and its quotient is finite locally
  free". Eight hits about formally unramified/smooth/etale maps; no conormal
  splitting for algebraic spaces.
- `msearch.py ... leansearch`, query: "Split short exact conormal sequence of
  formally unramified algebraic spaces with affine local complete intersection
  source". Eight hits: formal unramifiedness, ring cotangent split injections,
  and generic ShortComplex splitting; none gives this geometric statement.
- `msearch.py ... loogle`, query:
  "Algebra.Generators.Cotangent.exact, SheafOfModules.IsLocallyFree". Zero hits.
- `msearch.py ... grep`, query:
  "conormal.*transitiv|transitiv.*conormal|universal.*[Tt]hicken". Zero Mathlib hits.
- `rg` of WeilConjectures and Sheaf for conormal transitivity/splitting and the
  exact item ID: no existing space statement; ring presentation splitting and
  Koszul conormal-basis results are different statements.
- `rg` for local complete intersection/Koszul predicates found the already
  recorded SchemeLci, SpaceProperty and IsKoszulImmersion, which are reused.
- `rg` of DAG records for schemeSpace and universal-thickening predicates found
  the two already-landed definition owners, which are cited rather than copied.
  `tools/blueprint_refs.py search 'scheme as algebraic space'`: zero blueprint
  text matches. No new notion node is required.

Initial compile diagnostics identified global-site coproduct instance requirements;
finite products give the canonical finite direct sums of these module sheaves
without adding such requirements. No blanket global sheafification assumptions
were added. Compilation and delivery validation are recorded below.

## Second reading by Q05

The dispatcher explicitly requires a solo worker and prohibits starting other
agents. This is a separate manual second pass over the final node and module,
not a claim that another agent reviewed the delivery; the maintainer's independent
review remains required.

Re-read the TeX against every binder and clause. S and the maps over S match;
Z is affine via IsAffine, Y and X remain spaces; both formal unramifiedness
hypotheses use the specified square-zero tests. The lci hypothesis reuses the
compatible-chart predicate and its actual closed-immersion/smooth factorization,
with the Koszul rather than classical regularity condition. The universal
thickenings are arbitrary presentations with their complete universal property,
not chosen objects with an added assumption. Both induced thickening maps have
their equations over the relevant base, and both conormal arrows have local
ideal-section normalizations. Finite local freeness is explicitly Zariski and
variable-rank. The three quasi-coherence clauses and ShortExact retain all
sequence clauses. The section equation has the correct Lean composition order.
The IsIso statement is on the specified sum of the two projections followed by
lam and s, so its first summand is canonical. No arbitrary comparison is substituted.

The second pass corrected the finite-sum realization to use canonical sectionwise
finite products: source ranks use Fin r without a universe restriction, rank zero
still works, and the final arrow explicitly supplies both product object types.
The only binder named lam avoids Lean's reserved lambda token. No statement
correction, false edge case, missing hypothesis, or additional independent notion
was found. Helpers have real data; the only postponed proof is the named theorem.

Validation: scompile.py compiled the final module separately as sandbox and
library modules (20.0 s and 17.5 s), exit 0, no errors or warnings. Explicit
morphism type annotations avoid an elaborator instance-search timeout without
raising any timeout or adding an assumption.
