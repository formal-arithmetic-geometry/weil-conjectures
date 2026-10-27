## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedLciKoszulEtaleCharts` states
`AlgebraicGeometry.AlgebraicSpace.exists_unramified_lci_koszul_etale_charts`.
Its only theorem proof is `sorry`. No definitions, arbitrary choices, new nodes,
dependency repairs, or statement corrections are introduced.

Hypothesis and clause correspondence:

- The base scheme and algebraic spaces over it are `{S : Scheme.{u}}` and
  `{Z Y : AlgebraicSpace S}`; `uMap : Z ⟶ Y` is the given morphism.
  The fixed scheme universe is `u`; a prescribed covering can have any explicit
  index universe `w`. Test schemes, smooth ambients and base-change schemes
  all remain in the original scheme universe. The output has `I : Type u`:
  one can choose charts indexed by the points of a scheme atlas of Z, which
  are a u-small set. No nonemptiness or finiteness assumption is made on I.
- Formal unramifiedness is exactly `hunramified : SpaceFormallyUnramified uMap`,
  the dependency's restriction-injectivity predicate on all scheme square-zero
  thickenings, not a stronger representability assumption on uMap.
- The lci hypothesis `hlci` quantifies over EVERY compatible pair of scheme
  charts `U V : Over S`, maps `p`, `q`, and scheme map `g : U ⟶ V`, with
  `IsEtale p`, `IsEtale q`, and `p ≫ uMap.hom.hom = yoneda.map g ≫ q`.
  For each `x : U.left` it gives `O : U.left.Opens` containing x, a scheme P,
  and maps `j : O.toScheme ⟶ P`, `s : P ⟶ V.left` with
  `IsClosedImmersion j`, `CotangentPresentation.IsKoszulImmersion j`,
  `Smooth s`, and `j ≫ s = O.ι ≫ g.left`. This writes out exactly the
  local Koszul-regular closed immersion followed by a smooth map. Locality
  on the source allows restricting the target as well: compose a smooth
  map to an open target with its open inclusion. The converse is immediate.
- The first conjunct asserts existence without a prescribed target covering.
  Its `W V : I → Over S` are the schemes with their structural S maps.
  `IsAffine (W a).left ∧ IsAffine (V a).left` states that BOTH are affine.
- The natural transformations p and q are the scheme charts to Z and Y.
  The next conjunct gives `IsEtale (p a) ∧ IsEtale (q a)` for every a,
  and `IsJointlySurjective p` is exactly joint surjectivity on point classes.
- The Over morphism `i a : W a ⟶ V a` is a map of schemes over S.
  `IsClosedImmersion (i a).left` and
  `yoneda.map (i a) ≫ q a = p a ≫ uMap.hom.hom` express the closed
  immersion and the required commuting square, with the same chart maps.
- Global generators for each affine chart are the existential
  `r : ℕ`, `f : Fin r → Γ((V a).left, ⊤)`, with
  `RingTheory.Sequence.IsKoszulRegular f` and
  `Ideal.span (Set.range f) = RingHom.ker (i a).left.appTop.hom`.
  This is the actual kernel of the structural map on global functions.
  For an affine closed immersion this is its defining ideal, and its affine
  source is Spec of the quotient. These are global generators on V_a,
  rather than merely a local regularity assertion. The tuple is the
  already recorded Koszul-regularity notion; r may be zero.
- The following conjunct quantifies over EVERY `T : Scheme.{u}` and EVERY
  `g : T ⟶ (V a).left` with `Etale g`. The base-changed map is the actual
  `Limits.pullback.snd (i a).left g`. It is asserted closed and satisfies
  `CotangentPresentation.IsKoszulImmersion`, the recorded local affine
  finite-Koszul-generator predicate. T need not be affine or separated.
- The second main conjunct quantifies over an arbitrary prescribed scheme
  covering `T : B → Over S`, `b : ∀ β, yoneda.obj (T β) ⟶ Y.obj.obj`,
  with `(∀ β, IsEtale (b β))` and `IsJointlySurjective b`. Its conclusion
  repeats all the preceding chart properties on ONE family and adds
  `∀ a, ∃ (β : B) (r : V a ⟶ T β), yoneda.map r ≫ b β = q a`.
  This is precisely refinement of that covering. The refinement morphism
  is automatically étale by cancellation between the two étale maps to Y;
  no arbitrary base map or extra condition replaces its factorization.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms
  and `Scheme.Hom.appTop`; affineness is Mathlib `IsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicSpace.IsEtale` (scheme-test representable étaleness).
- `Sheaf.AlgebraicGeometry.SpaceUniversalConormal`:
  `AlgebraicSpace.SpaceFormallyUnramified`, read with its full square-zero
  restriction-injectivity definition. The main conormal existence theorem
  is not used to choose any data.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`, read with the nonzero Koszul homology
  vanishing definition and the empty-sequence convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, exactly the recorded
  notion of the smoothness dependency (not the more specialized LciPresentation).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, the recorded scheme notion.
- The metatheoretic size-convention dependency is rendered by the explicit
  universes and binders; it has no Lean declaration to import.
- Two already landed definition owners are added to stmt_deps, as authorized
  by brief-stage2 §5: `def-trf-algebraic-space-jointly-surjective-family`
  owns `AlgebraicSpace.IsJointlySurjective` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`;
  `def-sfb-koszul-closed-immersion-chart` owns
  `CotangentPresentation.IsKoszulImmersion` in
  `Sheaf.AlgebraicGeometry.LciCotangentPresentation`. Their full definitions
  were read; the latter is paired with IsClosedImmersion every time it is used.
  These existing notions are reused without a second definition.

The module publicly imports all statement-dependency modules. Plain proof imports
include the recorded chartwise permanence, affine basis, étale permanence,
finite-presentation and finite-type criteria, formally-unramified diagonal,
finite unramified neighbourhoods, common field extensions, fibre-product points,
and finite-one-point closed-immersion modules. The proof dependencies
`lem-sfb-space-formally-unramified-etale-charts`,
`lem-sfb-koszul-immersion-smooth-ambient-independence`,
`lem-sfb-koszul-closed-immersion-affine-criterion`, and
`lem-sfb-koszul-immersion-flat-ascent-etale-descent` have no recorded Lean
module in the current DAG, so cannot yet be imported. They are retained in
proof_deps and explicitly named in the seven-step theorem proof docstring.
No import cycle is introduced by these currently stated proof dependencies.

Sources read: spaces-more-morphisms.tex, definition-lci (06C4) and lemma-lci
(06C5); etale.tex, lemma-unramified-etale-local (04HH); divisors.tex,
lemma-flat-base-change-regular-immersion (067P). The chart construction uses
04HH before 06C5 supplies Koszul regularity; flatness is needed only for the
base-change preservation clause. The natural-language proof in the docstring
follows the node's seven steps, including finite type without Noetherianity,
the marked-point exhaustion argument, smooth-ambient independence, global
shrinking, and flat ascent.

Edge cases checked by reading the definitions and the source proof:
empty Z admits I empty; an empty covering can cover only empty Y and hence
has empty Z; identity charts allow r=0 with zero kernel; a chart with empty
source can be omitted; sequence lengths may vary with a; the zero ring and
empty affine scheme are not excluded; prescribed covers and resulting
families need not be finite; arbitrary characteristics and non-Noetherian
schemes are included; non-affine étale base changes are included. No lci,
formal-unramifiedness, or affineness hypothesis is tautological.

Searches for an existing statement (all with msearch.py, group Q03, this item):

- LeanFinder: "unramified local complete intersection algebraic space etale
  charts Koszul regular closed immersion" returned 8 hits: étale implies
  formally unramified/smooth, ring étale-locus and related étale API.
  None supplies the asserted affine Koszul-regular charts of algebraic spaces.
- Loogle: "IsKoszulImmersion, IsLocalCompleteIntersection" returned zero
  hits and unknown Mathlib identifier IsKoszulImmersion.
- Mathlib grep: "IsKoszul|CompleteIntersection|Unramified.*[Cc]hart" in
  AlgebraicGeometry returned zero hits.
- LeanSearch: "unramified local complete intersection admits etale local
  Koszul regular closed immersion charts" returned 8 hits about formal
  unramifiedness and étaleness, not this statement.
- Direct rg searches of WeilConjectures, Sheaf and dag/lean_names_upstream.json
  for IsKoszulImmersion, complete-intersection chart names and the proposed
  theorem name found the existing local predicate in LciCotangentPresentation,
  the near-point predicate, and unrelated presentations, but no theorem match.
  Searching this item id in WeilConjectures returned no match.
- Searching DAG records located the existing closed-chart and joint-surjectivity
  definition owners; no new node was necessary.

Validation: the required scompile.py single-file invocation reported a clean
server compile (2.4 seconds, no errors or warnings). The local fallback attempt
reported disk full; scompile automatically confirmed against current server
sources successfully. The required deliver2.py --no-push dry run passed preflight and compilation
(candidate commit 7d8e53ad212).

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
