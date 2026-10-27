## Worker report

The module `Sheaf.AlgebraicGeometry.KoszulImmersionSmoothPush` states
`AlgebraicGeometry.isKoszulRegularImmersion_of_smooth_comp`, with its whole proof
`sorry`. It introduces no definitions. The source is Stacks Project, Divisors,
Tag 0693 (`lemma-push-regular-immersion-thru-smooth`), Koszul-regular case, read
in `literature/stacks-project/divisors.tex:5741`. The local definition is Tag
063J; its affine form is already encoded in the existing closed-chart predicate.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes Z, P, S: `{Z P S : Scheme.{u}}`, with the universe explicitly declared.
- The three named morphisms: `(i : Z ⟶ P) (p : P ⟶ S) (j : Z ⟶ S)`.
- The commuting triangle p composed with i equals j: `(h : i ≫ p = j)`.
- Smooth ambient projection p: `[Smooth p]`.
- Both i and j are immersions: `[IsImmersion i] [IsImmersion j]`; neither
  is required to be globally closed.
- Koszul regularity of i at every source point:
  `(hi : ∀ z : Z, IsKoszulRegularImmersionNear i z)`.
- Conclusion, Koszul regularity of j at every source point:
  `∀ z : Z, IsKoszulRegularImmersionNear j z`.
- The local meaning in the node uses precisely the landed definition
  `IsKoszulRegularImmersionNear`: there is an open source V containing z,
  an open target U, a closed immersion from V to U, and the equation identifying
  its composite with the restriction of the original morphism. Its last clause
  is `CotangentPresentation.IsKoszulImmersion` of that closed immersion.
- The closed-chart predicate quantifies over every source point, chooses an
  affine target neighbourhood W, and chooses `r : ℕ` and equations
  `a : Fin r → Γ(P, W.1)` satisfying `RingTheory.Sequence.IsKoszulRegular a`
  and `Ideal.span (Set.range a) = i.ker.ideal W`. Thus the ideal really is the
  kernel ideal of the closed immersion, the equations are finite, and their
  length can vary. No fixed codimension is imposed.
- No Noetherian, separation, or quasi-compactness hypothesis occurs, either
  in the theorem signature or in the two reused local predicates.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
  This is the smoothness interface recorded on def-sbc-smooth-morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, reexported by the public immersion
  import. `Mathlib.AlgebraicGeometry.Morphisms.Immersion` supplies
  `AlgebraicGeometry.IsImmersion`, exactly the immersion clause in the
  dependency's mathlib_match, not a replacement by closed immersions.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular`, whose full definition is vanishing
  of every nonzero natural-degree homology module of the Koszul complex.
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear`:
  `AlgebraicGeometry.IsKoszulRegularImmersionNear` (def-sfb-koszul-regular-immersion-near).
  Its full definition and docstring were read, together with
  `AlgebraicGeometry.CotangentPresentation.IsKoszulImmersion` in
  `Sheaf.AlgebraicGeometry.LciCotangentPresentation:417`. The former node is
  added to stmt_deps as an already landed definition. No node is duplicated.

All stated proof dependencies are imported as proof imports, including the
regular-to-Koszul theorem, split conormal cancellation, flat base change,
smooth affine space, and regular equations for a smooth pair. The Mathlib
leaves are imported from AffineSpace, Flat.Localization, RingHomProperties,
and Smooth.Basic; smooth restriction is already supplied by the public
Smooth import. The not-yet-recorded proof dependencies
`lem-sfb-koszul-closed-immersion-affine-criterion` and
`lem-sfb-koszul-immersion-composition` have no modules to import. They are
retained in the DAG proof and explained in the theorem docstring. They are
not missing notions needed to type this statement.

Edge cases checked against the signature and the definitions before writing:
empty Z makes both pointwise assertions vacuous, as it should; an empty target
forces the corresponding source empty. Empty equation sequences are included
by `r = 0`, with no nonempty or positive-rank binder. The affine-space proof
includes dimension zero. Lengths vary independently at each point. The theorem
allows open immersions, the identity projection, non-Noetherian bases, and
nonseparated or non-quasi-compact schemes. There is no field or characteristic
restriction. One arbitrary universe u is the usual scheme-category convention;
no unequal-universe test-object quantification is used.

Searches for an existing statement and reusable notions:

- msearch.py LeanFinder: "A Koszul regular immersion remains Koszul regular
  after composition with a smooth morphism when the composite is an immersion".
  Eight hits on smooth composition, relative dimension, and standard smooth
  ring maps; none states Koszul-regular immersion descent.
- msearch.py LeanSearch: "Push a Koszul regular immersion through a smooth
  morphism of schemes". Eight hits on smoothness and ordinary immersion
  composition; no matching statement.
- msearch.py Loogle: `"Smooth", "IsImmersion"`. One unrelated manifold
  smooth-embedding result; no matching algebraic-geometric statement.
- msearch.py Mathlib grep: `KoszulRegular|koszul.regular|IsKoszulRegularImmersionNear`
  in AlgebraicGeometry. Zero hits.
- rg in lean/WeilConjectures and lean/Sheaf, using `KoszulRegular|koszulRegular|koszul_regular`
  and `immersion.*smooth|Immersion.*[Ss]mooth|IsKoszulRegularImmersionNear`:
  found the reusable near-point and closed-chart definitions; the regular
  immersion smooth-structure theorem has different hypotheses and conclusion.
  No existing theorem states the assigned smooth-push implication.
- grep for the item id in lean/WeilConjectures returned no match. The upstream
  name index was searched alongside both source trees. DAG search found the
  already landed near-point definition and its recorded declaration.

No statement correction, disputed statement, new definition node, or dependency
interface repair is needed. Only lean and the addition of the landed local
predicate to stmt_deps change in the item JSON.

Validation: scompile.py compiled this delivered file in sandbox and library
module modes without errors or warnings (18.3 s and 6.1 s respectively).

## Second reading by Q104

A separate rereading pass opened the source node, the completed theorem, the
near-point definition, and the closed-chart definition. This was performed by
the same worker; the dispatcher's instructions prohibit starting other agents,
and the maintainer supplies independent review after delivery.

The three morphism types and `i ≫ p = j` give precisely the source's triangle.
Smoothness belongs to p, and both immersion instances belong to the appropriate
maps. The input and output universally quantify the same source Z. Expanding
`IsKoszulRegularImmersionNear` gives actual closed charts on open source and
target neighbourhoods, not a bare stalk condition or an arbitrary ideal.
Expanding its closed-chart predicate gives exactly finite Koszul-regular
kernel generators, with no globally fixed rank or positivity condition.
Hence the two universal assertions are the global local conditions in the
node. The empty-source and empty-sequence cases survive both expansions.
The theorem does not strengthen the conclusion to ordinary regularity and
adds none of the Noetherian, separation, or quasi-compactness assumptions
excluded by the node. No mismatch was found and no mathematical change was
made in the rereading pass.
