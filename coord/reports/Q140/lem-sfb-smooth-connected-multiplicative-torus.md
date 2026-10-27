## Worker report

The delivery states `AlgebraicGeometry.smooth_connected_multiplicativeType_isRelativeTorus`
in `Sheaf.AlgebraicGeometry.SmoothConnectedMultiplicativeTorus`. Its only theorem
proof is `sorry`. The added module gives a real Prop-valued relative
multiplicative-type definition; it has no postponed data or proofs.

Clause-by-clause correspondence with the unchanged item:

- An arbitrary scheme S is `{S : Scheme.{u}}`. No base field, normality,
  Noetherian, reducedness, connectedness, or nonemptiness restriction is imposed.
- An S-group scheme is `P : Grp (Over S)`. The bundled group object includes
  multiplication, identity, inverse and the group diagrams. Local isomorphisms
  below are in this group-object category and hence preserve all operations.
- Finite presentation is `[LocallyOfFinitePresentation P.X.hom]` together with
  `[QuasiCompact P.X.hom]`, Mathlib's stated convention in
  `AlgebraicGeometry/Morphisms/FinitePresentation.lean`. These render the node's
  explicit finite-presentation hypothesis. There is no extra flatness hypothesis.
- Multiplicative type is `hP : IsRelativeMultiplicativeType P`: an fppf cover
  by spectra of commutative rings, on each of which P is group-isomorphic to the
  recorded `ringDiagonalizableGroup (R i) M` with `AddCommGroup M` and `AddGroup.FG M`.
  This is exactly the node's fppf-local form condition after affine refinement;
  it does not require P or S themselves to be affine. Refinement is legitimate:
  the affine open covers of the original splitting schemes are jointly
  surjective, open immersions are flat and locally of finite presentation,
  their composites with the fppf maps have these same properties, and a
  diagonalizable group restricts to the group algebra over the new affine ring.
  Conversely, the displayed affine cover is itself a cover of the required kind.
- Smoothness is `[Smooth P.X.hom]`, the dependency's exact Mathlib class.
- Every geometric fibre is connected is `hconn : ∀ (Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S), ConnectedSpace
  (pullback P.X.hom s : Scheme.{u})`. This quantifies over all geometric points
  in the scheme universe, uses the whole fibre product, and includes the
  nonempty condition in `ConnectedSpace`. There is no identity-component proxy.
- The conclusion `IsRelativeTorus P.X` is the already landed relative-torus
  definition. Unfolding it gives an fppf cover, ranks `r : I → ℕ`, and
  isomorphisms of group-valued functors with `relativeSplitTorusFunctor`.
  That functor is the actual finite product of units of global functions,
  so the node's explicit local G_m^r conclusion is included, with varying ranks.

Dependencies used (source declarations and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec` and `Spec.map` (def-pc-scheme and def-weil-affine-spectrum).
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup`, defined by `hopfSpec` applied to
  `AddMonoidAlgebra`, with its actual coproduct, counit and antipode.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`. The former is the jointly-surjective precoverage for
  flat locally finitely presented maps. The splitting cover uses it directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Sheaf.AlgebraicGeometry.RelativeTorus`: `AlgebraicGeometry.IsRelativeTorus`
  and `relativeSplitTorusFunctor` (def-sfb-relative-torus, added to stmt_deps).
- `Sheaf.AlgebraicGeometry.RelativeMultiplicativeType`:
  `AlgebraicGeometry.IsRelativeMultiplicativeType` (new definition node below).

Proof dependencies are imported without public visibility: algebraic closure
(`AlgebraicClosure`, `IsAlgClosed`); geometric points (`Scheme.SpecToEquivOfField`
in `Mathlib.AlgebraicGeometry.ResidueField`); affine fibre products
(`pullbackSpecIso` in `Mathlib.AlgebraicGeometry.Pullbacks`); tensor universal
property (`Algebra.TensorProduct.productMap`, includeLeft/includeRight and ext,
`Mathlib.RingTheory.TensorProduct.Maps` and its Basic import); smooth geometric
reducedness (`AlgebraicGeometry.Smooth.geometricallyReduced` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`); affine
reducedness (`affine_isReduced_iff` in `Mathlib.AlgebraicGeometry.Properties`);
clopen idempotents (`PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`
and `isIdempotentElemEquivClopens` in `Mathlib.RingTheory.Spectrum.Prime.Topology`);
finite free integral basis (`Module.basisOfFiniteTypeTorsionFree'` in
`Mathlib.LinearAlgebra.FreeModule.PID`); affine adjunction
(`AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` in
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`). The theorem docstring carries
all four accepted proof steps, including the explicit nilpotent and averaging
idempotent calculations, then the basis-to-Laurent-algebra identification.
No new proof lemma or alternative proof route is introduced.

Edge cases checked before writing: empty base (empty fppf cover and vacuous
geometric-point condition); rank zero (empty product of units); disconnected
base (rank varies by member); nonreduced base (the proof only uses reducedness
of smooth geometric fibres); characteristic p (μ_p is connected but fails
smoothness), prime-to-p torsion (μ_n is smooth but its whole geometric fibre
is disconnected); characteristic zero (the averaging idempotent excludes every
nontrivial finite-order character). No positive rank or constant rank is assumed.
All types used for rings, character groups and geometric fields use the same
universe u as the schemes; in particular no smaller independent universe makes
the geometric-fibre hypothesis vacuous.

Searches performed using msearch.py:

- LeanFinder: “A smooth group scheme of multiplicative type with connected
  geometric fibres is a torus”: eight hits, analytic tori, Lie groups and affine
  space, no exact theorem.
- Loogle: `"torus"`: twelve hits, topological tori and compiler names, no
  relative group-scheme assertion.
- Mathlib grep: `diagonali[sz]able|multiplicative.?type|torus`, subdirectory
  AlgebraicGeometry: zero hits.
- LeanSearch: “A relative group scheme of multiplicative type is fppf locally
  diagonalizable with a finitely generated abelian character group”: eight
  hits about MulChar and type tags, no relative group-scheme definition.
- LeanFinder: “A group scheme over an arbitrary scheme is of multiplicative
  type if fppf locally a diagonalizable group of a finitely generated abelian
  group”: eight hits about group objects and base change, no exact predicate.
- rg over the project's Sheaf and WeilConjectures sources found
  `MultiplicativeType.IsMultiplicativeType` in ToriMultiplicativeType.lean,
  which binds `[Field k]` and splits only after algebraic closure; it cannot
  express this arbitrary-base hypothesis. Other relative-torus interfaces
  were inspected and the existing `IsRelativeTorus` is reused.
- rg for this item's id in WeilConjectures found no existing theorem; rg for
  the chosen new declaration names in Mathlib, upstream source and the
  upstream-name index found no collision.
- DAG title/concept searches found only field multiplicative-type definitions,
  the existing ring diagonalizable groups, and relative tori. The blueprint
  search `python3 tools/blueprint_refs.py search multiplicative type` returned
  three unrelated imported nodes; none gives this relative definition.

Source read: Conrad's online PDF, Definition B.1.1 and its preceding paragraph
(printed p.280), Proposition B.3.4 (pp.290–291) and its torus character-sheaf
application at the proof of Proposition B.3.8 (p.296).
Source URL: https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf .
The local PDF is still absent as the original node notes; the published PDF
was opened directly. No statement correction or statement dispute is needed.

## New nodes

`def-sfb-relative-multiplicative-type` defines the exact fppf-local finite
character-group condition over arbitrary schemes, using affine refinements
and the existing `ringDiagonalizableGroup` construction. Source: Conrad,
Definition B.1.1, printed p.280. The three registered searches above are stored
verbatim in its mathlib_searches; project and DAG searches rule out a duplicate.
Its module has one real definition, no sorry. It is cited by the item, as is
already landed def-sfb-relative-torus. The blueprint ancestor utility reports
`None` for this existing item's broken ancestry; the new node preserves that
reported null ancestor and prepends the item to the existing via chain.

Validation: both delivered modules compiled independently in dependency order
through scompile.py against the published library. The first theorem attempt
needed an explicit `: Scheme.{u}` on its fibre-product expression to prevent
inference in Type; the corrected statement compiles cleanly. The dry-run and
final delivery results are checked using deliver2.py.

## Second reading by Q140

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
