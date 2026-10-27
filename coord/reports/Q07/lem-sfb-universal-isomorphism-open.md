## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalIsomorphismOpen` states
`AlgebraicGeometry.exists_universalIsomorphismOpen`, with its whole proof `sorry`.
There are no new definitions, additional nodes, dependency repairs, or statement
corrections. The source read is Stacks Tag 05XD, label
`spaces-more-morphisms-lemma-where-isomorphism`, in
`literature/stacks-project/spaces-more-morphisms.tex:11791-11831`.
Its six assumptions and universal conclusion agree with the node's scheme
specialization. No statement fault or disputed claim was found.

The hypothesis and conclusion correspondence is:

- The schemes B, A, C are `{B A C : Scheme.{u}}`, with arbitrary explicit
  universe `u`. The three morphisms are `(p : A ⟶ B) (q : C ⟶ B)
  (f : A ⟶ C)`. Commutativity `q ∘ f = p` is `(hf : f ≫ q = p)`.
- Flatness of p is `[Flat p]`. Local finite presentation of p is
  `[LocallyOfFinitePresentation p]`. Universal closedness of p is
  `[UniversallyClosed p]`.
- Local finite type of q is `[LocallyOfFiniteType q]`. Separatedness of q is
  `[IsSeparated q]`. Topological closedness of q, without asserting universal
  closedness, is the explicit hypothesis `(hq : IsClosedMap q)`.
- The open subscheme is `∃ U : B.Opens`. Its scheme structure is the existing
  `U.toScheme`, and its inclusion is the existing `U.ι`, which has the Mathlib
  `IsOpenImmersion U.ι` instance. Thus an open subscheme, rather than just a
  set without its restricted structure sheaf, is specified.
- Every scheme B′ and morphism h is `∀ (T : Scheme.{u}) (h : T ⟶ B)`.
  The arbitrary universe u is shared with B, A and C, as required for morphisms
  in Mathlib's category of schemes; no separate smaller test universe is used.
- The canonical base change `A ×_B T ⟶ C ×_B T` is
  `pullback.map p h q h f (𝟙 T) (𝟙 B) ... ...`. Its two components are
  the projection to A followed by f and the projection to T. The first
  commutative-square witness is obtained from `hf.symm` by the right-identity
  law; the other is the identity-square law. Neither witness adds a hypothesis.
- Invertibility is `IsIso` of this canonical morphism. The final `↔` relates
  it to `∃ l : T ⟶ U.toScheme, l ≫ U.ι = h`, exactly factorization through
  the open subscheme. There is no assumption that h is a geometric point,
  reduced, flat, affine, or of finite type.

Dependency declarations read and used (the declaration docstrings and signatures
were read, not just the node records):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`, lines 37-47
  and 73-76. Schemes are locally ringed spaces locally isomorphic to spectra;
  morphisms are morphisms of their locally ringed spaces.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`, lines 37-45. The recorded affine-local notion
  agrees with the stalkwise formulation by its documented
  `Flat.iff_flat_stalkMap` equivalence.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`, lines 41-48.
- `def-weil-proper-morphism`: imported recorded module
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`. The notions used are its
  `AlgebraicGeometry.UniversallyClosed` (defined in
  `Morphisms.UniversallyClosed`, lines 38-44) and
  `AlgebraicGeometry.IsSeparated` (defined in `Morphisms.Separated`,
  lines 42-46). No `IsProper p` assumption is imposed.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, lines 39-46.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, lines 34-39. The implementation of
  the open subscheme and its canonical inclusion was also read in
  `Mathlib.AlgebraicGeometry.Restrict`, lines 44-60:
  `Scheme.Opens.toScheme`, `Scheme.Opens.ι`, and its open-immersion instance.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections and universal lift
  (lines 94-131), and `CategoryTheory.Limits.pullback.map` (lines 257-275).
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.

The docstring contains all five proof steps of the node: p closed and locally
of finite type; the surjective-flat open from 05XC; the closed-immersion open
from 05XA; their intersection and factorization criterion; both directions
using the surjective-flat-closed-immersion isomorphism criterion. The two open
locus proof dependencies currently have no recorded Lean declaration, so there
is no module to import for them; they are not needed to type this statement.
The Mathlib proof dependency `lem-sfb-surjective-flat-closed-immersion-isomorphism`
is imported privately through `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`,
whose `AlgebraicGeometry.Flat.isIso_of_surjective_of_mono` signature at lines
24-26 was read. The other definition proof dependencies are already available
through the public statement imports.

Edge cases checked before writing:

- If B is empty, all schemes over B are empty and its unique open works.
- For f the identity of a family satisfying the assumptions, U is the whole
  base, as every base change is an isomorphism.
- If A and C are empty, the same whole-base answer works for every test T.
  If A is empty and C = B with q the identity, only empty test schemes give
  an isomorphism; the empty open represents this case. This confirms the
  direction of the factorization equivalence and allows the empty open.
- For the fold from two copies of a point to a point, p is flat, finitely
  presented and universally closed and q is the identity. No nonempty base
  change is an isomorphism, so the empty open is again necessary.
- Nonreduced tests are retained: the displayed quantifiers are over schemes,
  and the condition is invertibility of the scheme morphism, rather than
  bijectivity of points or isomorphism only on residue-field fibres.

Searches actually run with the prescribed msearch wrapper (group Q07, this item):

- `leanfinder`, query: "The base changes making a morphism between a flat
  locally finitely presented universally closed family and a separated locally
  finite type closed family an isomorphism are represented by an open subscheme
  of the base". Eight hits: universal openness, fpqc descent, Flat,
  `Flat.isIso_of_surjective_of_mono`, and universal closedness. No universal
  isomorphism open statement.
- `loogle`, query: `"AlgebraicGeometry", "IsIso"`. Twelve hits concerning
  isomorphisms of ringed-space components, stalks and spectra, none representing
  this universal locus in the base.
- `grep`, query:
  `whereIsomorphism|isomorphismLocus|universal.*isomorphism|isomorphism.*locus`,
  subdirectory `AlgebraicGeometry`. Zero hits.
- `leansearch`, query: "Universal isomorphism locus in the base of a morphism
  of flat finitely presented universally closed schemes is open". Eight hits:
  universal openness, universal closedness, ordinary restriction of an
  isomorphism and fpqc descent, none the present statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `universal.*[Ii]so|whereIsomorphism|isomorphismLocus|lem-sfb-universal-isomorphism-open`:
  many unrelated comparison-map docstrings and one vector-bundle result.
  I read `WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeMapIsoOpen`:
  `Scheme.Modules.exists_finiteLocallyFreeMapIsoOpen` concerns a map of
  vector bundles and its scalar-extension invertibility, not a morphism of
  scheme families. It cannot serve this node.
- An exact follow-up search in both Lean roots and `dag/lean_names_upstream.json`
  for `universalIsomorphismOpen|universal_isomorphism_open|lem-sfb-universal-isomorphism-open|whereIsomorphism|isomorphismLocus`
  gave no hits before creation. Thus the proposed declaration name is unused.

Validation: scompile.py compiled the sandbox probe and the final library module
separately, each in 1.5 seconds, without errors or warnings. `autoImplicit` is
explicitly false, and every variable and universe is bound. The node's only
changed field is `lean`, whose statement is extracted verbatim from the module.

## Second reading by Q07

I reread the node statement beside the completed module after compilation.
The three morphism domains/codomains and `hf` match the diagram; p has exactly
flatness, local finite presentation and universal closedness; q has exactly
local finite type, separatedness and ordinary topological closedness. In
particular closedness of q has not become universal closedness, and separatedness
of p and properness of either morphism have not been added. The output
`B.Opens` uses the canonical restricted scheme and its inclusion. The
`pullback.map` has source `pullback p h` and target `pullback q h`, with
components f and the identity of T, as the node requires. Both sides of the
iff are asserted for every T and h, including empty and nonreduced T.
No mismatch was found and no statement changed. This is a worker self-check;
the dispatcher's instruction forbids starting another agent, and the
maintainer's independent review reads this delivery.
