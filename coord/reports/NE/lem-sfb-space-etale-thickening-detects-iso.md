## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceEtaleThickeningDetectsIso` states
`AlgebraicGeometry.AlgebraicSpace.isIso_of_chartwiseEtale_of_thickening`, with its entire
proof postponed as `sorry`. No definition is introduced, and no mathematical node field changes.
The docstring carries all six steps of the accepted DAG proof, including its named inputs.

Hypothesis and clause correspondence:

- The base scheme is `{B : Scheme.{u}}`, with the explicit universe `u` covering both the
  schemes and the existing fppf presheaves. The existing point spaces live in `u + 1`.
- The algebraic spaces over that base are `(V W W₀ : AlgebraicSpace B)`, and the morphisms
  are `(f : V ⟶ W) (i : W₀ ⟶ W)` in their existing full subcategory of fppf sheaves.
- Chartwise etaleness is exactly `(hf : IsChartwiseEtale f)`. Its existing definition
  quantifies over every representable etale scheme-source map and requires its composite
  with `f` to be representable etale. No representability of `f` is added.
- The thickening's representable closed immersion condition is
  `(hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)`.
  This quantifies over all scheme tests, with actual representing pullback squares and
  closed-immersion scheme projections.
- Its homeomorphism condition is `(hiTop : IsHomeomorph (mapPoint i.hom.hom))`.
  `mapPoint` is the existing map on common-field-extension point classes; the existing
  `pointTopologicalSpace` instance is final for etale scheme maps, equivalently the
  quotient topology from any surjective etale atlas. No arbitrary homeomorphism is used.
- The isomorphism hypothesis is `(h₀ : IsIso (enlargedFibreProductFst i f))`.
  This is the canonical projection `W₀ ×_W V → W₀`, the symmetric ordering of the
  displayed `V ×_W W₀ → W₀`; the existing actual sheaf pullback is used. Exchanging
  its two factors gives the canonical comparison preserving the projection to `W₀`.
- The conclusion is precisely `IsIso f`.
- There is no quasi-compactness, separation, finite-order, finite-presentation, or
  representability assumption on `f`, and no additional hypothesis on `B`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and `AlgebraicSpace.IsEtale`, with actual
  scheme-test pullback squares and natural transformations as morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, whose algebraicity proof is used
  by the existing bundled fibre product.
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`:
  `AlgebraicSpace.chartwise_etale_permanence`; this publicly imports
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, the owner of
  `IsChartwiseEtale`, `enlargedFibreProduct`, and `enlargedFibreProductFst`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, a closed embedding with surjective stalk maps.
- The size-convention dependency is metatheoretic: its recorded Lean attachment is a
  convention, with no module or declaration; the explicit universe binder implements it.
- Supporting existing declarations: `Sheaf.AlgebraicGeometry.ProperCurveModuli` owns
  `AlgebraicSpace.mapPoint`; `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`
  owns the point topology and imports its existing field-valued point classes.
  Only the generic map on points is used from the moduli module; no curve predicate
  or curve restriction enters the theorem.
- Proof-only imports for the stated DAG inputs are Mathlib's `Etale` and
  `IsOpenImmersion`. Three further proof inputs (space thickening base change,
  unramified space open diagonal, and etale monomorphism open) currently have no
  Lean attachment and therefore supply no import. Their named use remains in the docstring.

Source checked: local `literature/stacks-project/spaces-more-morphisms.tex`,
`theorem-topological-invariance` (Tag 05ZH), especially its faithful and fully faithful
arguments; `lemma-thickening-equivalence` (Tag 05ZS). A thickening is an integral,
universally injective, surjective map, so the cited equivalence reflects the displayed
projection being an isomorphism. The explicit accepted proof avoids assuming its source
space is separated or a scheme.

Edge cases checked before writing:

- Empty `W`: all spaces mapping to it are empty; the statement remains valid.
- Identity thickening: its pullback projection is `f` up to the canonical pullback
  identification, so the conclusion is exactly the hypothesis transported along that iso.
- Arbitrary nil ideals without a uniform nilpotence exponent: the thickening condition
  has only the closed-immersion and homeomorphism tests, so none are excluded.
- Nonseparated and non-quasi-compact etale spaces: no such instance is requested;
  the open-diagonal argument in the proof applies without either assumption.
- The etale assumption is essential: `Spec k → Spec k[ε]/(ε²)` becomes an isomorphism
  after pullback to the reduction but is not an isomorphism.

Searches made for an existing statement:

- `msearch.py ... leanfinder` with query "An etale morphism of algebraic spaces that
  becomes an isomorphism after base change along a thickening is an isomorphism":
  eight hits, all scheme-level etaleness/permanence declarations; no match.
- `msearch.py ... loogle '\"Etale\", \"IsIso\"'`: zero hits.
- `msearch.py ... grep 'thicken.*[Ee]tale|[Ee]tale.*thicken|[Ee]tale.*[Ii]so|[Ii]so.*[Ee]tale'
  AlgebraicGeometry`: six hits, concerning scheme etale instances and etale sites;
  no algebraic-space thickening detection statement.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item id and etale/thickening
  combinations: scheme topological-invariance and finite etale lifting results, and
  algebraic-space proof-docstring references; no declaration stating this result.
- Additional `rg` for isomorphism/thickening names and the upstream name index likewise
  found only scheme/coefficient or other specialized theorems. The existing weakly-etale
  universal-homeomorphism result concerns scheme morphisms, not these algebraic spaces.
- Searches for supporting notions located the existing chartwise predicate, fibre product,
  point topology and point map; all are reused rather than duplicated.

No statement fault or disputed statement was found. No new or dependency node is needed.

## Second reading by NE

I reread the node and completed signature against each other after drafting; this is a
worker self-check, not an assertion that another agent reviewed it. The dispatcher brief
forbids starting other agents; the maintainer's independent review remains separate.
The explicit `IsRepresentableWith` condition supplies both representability and every
closed-immersion scheme test; `IsHomeomorph` supplies exactly the underlying-space
condition. `IsChartwiseEtale` is the chartwise predicate, rather than representable
etaleness of `f`. I reopened `enlargedFibreProductFst` to verify that its first argument
is the retained projection: `i f` therefore projects to `W₀`, as required. Reversing the
factor order is the canonical fibre-product symmetry and adds no mathematical content.
All object and universe variables are explicitly bound, and no extra finiteness or
separation hypothesis appears. No mismatch requiring a correction was found.
