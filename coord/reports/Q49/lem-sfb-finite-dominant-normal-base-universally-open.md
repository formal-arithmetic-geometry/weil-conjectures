## Worker report

Stage 2, Q49, 2026-10-22. This delivery states
`AlgebraicGeometry.universallyOpen_of_finite_dominant_normal` in
`Sheaf.AlgebraicGeometry.FiniteDominantNormalUniversallyOpen` with proof `sorry`.
No definition or proof is added. The natural-language statement is unchanged.
The module docstring and theorem docstring cite the source and blueprint node;
the theorem docstring carries all six steps of the reviewed node proof.

The retained sandbox had only dispatcher markers, so this packet was reconstructed
from the live node. The live `reviewed` record is the NQ stage-1 review of its
split, not a Lean statement or stage-2 review: the item has no `lean` record.
The previous attempt's “already split and reviewed” result therefore does not
justify treating the stage-2 task as complete. This packet uses deliver2.py.

Clause-by-clause correspondence:

- “Let q:V -> B be a morphism of schemes”: `{V B : Scheme.{u}}` and `(q : V ⟶ B)`.
  The arbitrary universe `u` is declared explicitly.
- “of integral schemes”: `[IsIntegral V]` gives integrality of V. The first
  conjunct of `(hB : IsNormalScheme B)` gives `IsIntegral B`. Its nonemptiness,
  reducedness and irreducibility are the dependency's existing Mathlib notion.
  There is no need to add a second integrality hypothesis for B.
- “finite”: `[IsFinite q]`, exactly the affine-local module-finiteness definition.
  Finiteness of a morphism does not mean just finiteness of its fibres.
- “dominant means its image is dense”: `[IsDominant q]`, whose `denseRange` field
  is `DenseRange q`. Surjectivity or flatness is not assumed.
- “B is locally Noetherian”: `[IsLocallyNoetherian B]`, the Mathlib affine-local
  definition equivalent to an affine Noetherian cover, as in pqf-def-locnoeth.
- “B is normal, meaning every local ring is an integrally closed domain”:
  the second conjunct of `hB : IsNormalScheme B` is exactly
  `∀ b : B, IsDomain (B.presheaf.stalk b) ∧ IsIntegrallyClosed (B.presheaf.stalk b)`.
- “Then q is universally open”: `UniversallyOpen q`. Read its definition in
  Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen: its field is
  `MorphismProperty.universally (topologically @IsOpenMap) q`.
  The `universally` definition quantifies over every cartesian square; in
  particular, for each B' and h:B' -> B it gives
  `IsOpenMap (CategoryTheory.Limits.pullback.snd q h)`, with the requested
  pullback and projection of def-pc-fibre-product. IsOpenMap means the image of
  every open is open. Conversely all these chosen pullback projections give the
  cartesian-square formulation by the unique isomorphism of pullbacks. Thus the
  conclusion includes every scheme B' and map h, with no finiteness or normality
  restriction on B'.

Dependency declarations used (the recorded signatures and docstrings were read):

- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- def-weil-finite-integral-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`; its companion `IsIntegralHom` in Morphisms.Integral
  is read and supplied by the finite module import.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- def-pc-fibre-product:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, and `.snd`. Mathlib's
  AlgebraicGeometry.Pullbacks supplies HasPullbacks Scheme.
- Added the already landed def-sbc-normal-dominant-galois to stmt_deps to reuse
  `AlgebraicGeometry.IsNormalScheme` from
  `WeilConjectures.AlgebraicGeometry.NormalScheme`. This is exactly integral B
  together with its displayed normal-stalk condition. Its Galois and fibre
  notions are not assumptions of this theorem. There is no new normality predicate.
- The explicitly stated dominance and openness notions are Mathlib
  `AlgebraicGeometry.IsDominant` (Morphisms.UnderlyingMap) and
  `AlgebraicGeometry.UniversallyOpen` (Morphisms.UniversallyOpen).

The available proof-dependency modules are imported without `public`:
AlgebraicGeometry.AffineScheme (`IsAffineOpen.isLocalization_stalk` and related
chart identifications), AlgebraicGeometry.Scheme (`Spec`), Algebra.MvPolynomial.Basic
(`MvPolynomial` and its domain instance), RingTheory.LocalProperties.IntegrallyClosed
(`IsIntegrallyClosed.of_localization_maximal`), RingTheory.Polynomial.IsIntegral
(normal-polynomial instance), RingTheory.FiniteType (`Algebra.FiniteType.isNoetherianRing`),
RingTheory.FinitePresentation (`Algebra.FinitePresentation.of_finiteType`),
RingTheory.IntegralClosure.Algebra.Basic (`Algebra.IsIntegral.of_finite`),
RingTheory.IntegralClosure.GoingDown (normal integral going-down instance), and
RingTheory.Spectrum.Prime.Chevalley
(`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`). The
statement-dependency modules also serve the other proof dependencies.
lem-sfb-polynomial-test-universally-open has no Lean record or Mathlib match yet;
there is no module to import for this proof-only dependency. The complete proof
plan explicitly names it; its statement is not needed to elaborate this theorem.

Edge cases checked before writing: V and B are nonempty by integrality, so the
empty source over a nonempty base is excluded as the node requires. The identity
of any normal integral locally Noetherian B satisfies the conclusion. A finite
extension of fields gives an allowed zero-dimensional example, without a
separability assumption. A closed-point inclusion into a positive-dimensional
integral B fails dominance, so it cannot contradict openness. The theorem does
not impose normality on V, finite presentation or flatness of q as extra
hypotheses, or global Noetherianity/quasi-compactness on B. Empty B', nonreduced
B', and non-Noetherian B' are all included in UniversallyOpen. The polynomial
proof explicitly includes n=0. The single scheme universe is Mathlib's ordinary
Scheme.{u} convention, with no smaller independent universe of test schemes.

Searches made with msearch.py on 2026-10-22:

- leanfinder: “A finite dominant morphism of integral schemes with normal locally
  Noetherian target is universally open”. Eight results, including dominant
  relative-normalization maps, integral maps universally closed, finite maps
  integral, and normalization open covers. None states this universal-openness
  theorem; universal closedness is a different conclusion.
- loogle: `AlgebraicGeometry.UniversallyOpen, AlgebraicGeometry.IsFinite`.
  Zero results.
- grep: `UniversallyOpen|universally_open`, subdirectory AlgebraicGeometry.
  Twenty-three matches: definitions, geometrically integral/irreducible/connected
  permanence, site imports, and flat descent. No finite dominant normal-target
  universal-openness theorem.
- leansearch: same natural-language query as leanfinder. Eight results including
  UniversallyOpen, its constructor and equivalent definition, open immersions,
  and `UniversallyOpen.of_flat`. The flat theorem has an additional assumption
  not present here and is not a match.
- rg of Mathlib, dag/lean_names_upstream.json, lean/WeilConjectures and lean/Sheaf
  for `universallyOpen_of_finite_dominant_normal`, normal/universally-open name
  combinations: no duplicate declaration. Text searches for finite/normal and
  universal openness likewise found only unrelated uses. Searching the exact
  blueprint id in lean/WeilConjectures and lean/Sheaf found no declaration.
- rg for normal schemes and integrally closed stalks located the existing
  `IsNormalScheme` definition; read its full definition and reused it, adding
  its owning landed node to stmt_deps.

Sources read: literature/stacks-project/more-morphisms.tex, complete statements
and proofs of lemma-test-universally-open (0F31) and
lemma-quasi-finite-Noetherian-universally-open (0F32). The latter specializes to
this finite dominant integral case with a normal target, exactly as recorded in
the node. The affine polynomial-test proof is preserved rather than replaced.
No statement correction, new node, dependency-interface repair, or dispute.

Validation: scompile.py compiled the sandbox and final library module separately,
cleanly, in 1.6 and 1.7 seconds respectively. Every binder and universe is
explicit. There are no diagnostic commands in the delivered module.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
