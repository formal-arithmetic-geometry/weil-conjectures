## Worker report

The module states the full conjunction in lem-weil-pbc-reduction-universal-homeomorphism,
with a single sorry proof. It introduces no definitions and does not change the node statement.

Hypothesis and clause correspondence:

- “Let X be a scheme”: `(X : Scheme.{u})`, with its universe explicitly bound.
- “its reduction and canonical immersion i_X”: `X.nilradical.subscheme` and
  `X.nilradical.subschemeι`, exactly the dependency's mathlib_match specialization.
- “X_red is reduced”: `IsReduced X.nilradical.subscheme`.
- “i_X is a surjective closed immersion”: `IsClosedImmersion X.nilradical.subschemeι`
  and `Surjective X.nilradical.subschemeι`.
- “a universal homeomorphism: for every X' → X the base change projection is a
  homeomorphism”: `(topologically IsHomeomorph).universally X.nilradical.subschemeι`.
  The recorded `universally` quantifies over every pullback square and asserts
  `IsHomeomorph` for the corresponding projection. This expresses the stated clause
  without replacing the canonical base change by an unrelated map. It covers the
  chosen `pullback.snd` and, by unique pullback isomorphisms, all representatives.

Dependency declarations read and used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and Scheme.Hom.
- def-weil-pbc-scheme-reduction: its mathlib_match is Scheme.nilradical from
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic, and Scheme.IdealSheafData.subscheme
  and subschemeι from Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme. These are
  usable as recorded; the node has no lean field but has this precise match.
- def-pc-reduced-scheme: mathlib_match AlgebraicGeometry.IsReduced,
  Mathlib.AlgebraicGeometry.Properties. The sectionwise definition is equivalent
  to the node's stalkwise definition, by the two adjacent stalk reducedness lemmas.
- def-weil-closed-immersion: mathlib_match AlgebraicGeometry.IsClosedImmersion,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion. It combines a closed embedding
  and surjectivity on stalks, the sheaf-surjectivity characterization in the node.
- def-weil-surjective-morphism: AlgebraicGeometry.Surjective,
  Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap.
- def-weil-universal-homeomorphism: CategoryTheory.MorphismProperty.universally,
  Mathlib.CategoryTheory.MorphismProperty.Limits; AlgebraicGeometry.topologically,
  Mathlib.AlgebraicGeometry.Morphisms.Constructors; IsHomeomorph,
  Mathlib.Topology.Homeomorph.Defs. The recorded inline form is used verbatim.
- def-pc-fibre-product: CategoryTheory.Limits.pullback/fst/snd,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback. The universal predicate
  uses IsPullback rather than spelling out the chosen pullback, which is equivalent
  because all pullbacks of schemes exist and all choices are uniquely isomorphic.

Edge cases checked: the empty scheme remains allowed (no nonemptiness binder);
nonreduced schemes are allowed (no reducedness hypothesis); already reduced schemes
are allowed; no finite type, Noetherian, affine, characteristic, or base field
hypothesis is added. Base changes range over all schemes in the scheme universe;
there is no independent smaller test universe. Nilpotent quotients include arbitrary
commutative rings, including the zero ring.

Searches:

- msearch.py leanfinder, “The reduction of a scheme is reduced and its inclusion is
  a surjective closed immersion and universal homeomorphism”: eight hits, including
  IsReduced and affine_isReduced_iff; no declaration of the full conjunction.
- msearch.py loogle, “AlgebraicGeometry.Scheme.nilradical,
  AlgebraicGeometry.Scheme.IdealSheafData.subschemeι”: zero hits.
- msearch.py grep, “nilradical|reduction|universally.*IsHomeomorph”,
  AlgebraicGeometry/IdealSheaf: five hits for nilradical and support_nilradical.
- rg in WeilConjectures and lean/Sheaf for the item id, nilradical.subscheme and
  the proposed theorem name: the upstream isReduced_nilradical_subscheme instance
  supplies reducedness alone; UniversalHomeomorphism supplies the surjective
  closed immersion instance and a bridge to the universal topological predicate.
  None states the whole conjunction. The local project's occurrences of the item
  are proof docstrings in ExistsAmpleOfDimLEOne and DimensionLocallyAlgebraic.
- The proposed fully qualified theorem name has no existing match in the source,
  Mathlib, or project; the upstream node-name table is also checked.

Sources read: [Stacks 054M](https://stacks.math.columbia.edu/tag/054M),
[01J3](https://stacks.math.columbia.edu/tag/01J3), and
[01J4](https://stacks.math.columbia.edu/tag/01J4). The literature checkout has no
morphisms.tex on this machine, so the corresponding original Stacks pages were read.
The first gives the canonical reduction universal homeomorphism; the latter two
supply its reduced induced structure on the full underlying subset.

No statement dispute, node correction, new node, or dependency module is required.

## Second reading by M1

Independently read the item node, its seven statement-dependency nodes, their
recorded declaration signatures and implementations, and the delivered module.
The statement is faithful; no mathematical mismatch or missing dependency was found.

Object, hypothesis, and conclusion checklist:

- Object X, an arbitrary scheme: `(X : Scheme.{u})`. PASS. Scheme extends
  LocallyRingedSpace with local affine charts; Scheme.Hom is the locally ringed
  space morphism. No additional binder or instance is assumed.
- Object X_red, the reduction: `X.nilradical.subscheme`. PASS. Basic.lean defines
  nilradical as the radical of the zero ideal sheaf. Subscheme.lean constructs
  the associated scheme by gluing affine quotient spectra, with underlying space
  the ideal sheaf support. `support_nilradical = ⊤` identifies this with all of X.
- Object i_X, the canonical immersion: `X.nilradical.subschemeι`. PASS. Its point
  map is Subtype.val and its structure morphism is the canonical quotient map;
  this is the specialization recorded by def-weil-pbc-scheme-reduction.
- Conclusion X_red reduced: `IsReduced X.nilradical.subscheme`. PASS. The recorded
  sectionwise class in Properties.lean is equivalent to stalkwise reducedness by
  isReduced_of_isReduced_stalk and isReduced_stalk_of_isReduced, read directly.
- Conclusion i_X closed immersion: `IsClosedImmersion X.nilradical.subschemeι`.
  PASS. The recorded class has a closed embedding and surjective stalk maps,
  expressing the node's topological and sheaf-surjectivity conditions.
- Conclusion i_X surjective: `Surjective X.nilradical.subschemeι`. PASS. The
  recorded class is precisely Function.Surjective on underlying points.
- Conclusion every base change is a homeomorphism:
  `(topologically IsHomeomorph).universally X.nilradical.subschemeι`. PASS.
  Constructors.lean applies the predicate to the underlying point map;
  IsHomeomorph requires continuity, openness, and bijectivity. Limits.lean
  quantifies over arbitrary X', Y', i₁, i₂, f' with
  `IsPullback f' i₁ i₂ i_X`, and requires IsHomeomorph f'. In this square Y'
  is the test scheme over X and f' is the projection to Y'. This covers the
  node's chosen pullback.snd; conversely all other pullback representatives are
  uniquely isomorphic to it. Thus it adds no conclusion beyond the node.
- Quantifier order: first arbitrary X, then a conjunction of the three concrete
  properties and the universal condition, whose test morphisms are internal.
  PASS. No hypothesis is strengthened, weakened, added, or dropped.

Source check: the literature Stacks checkout is absent on this machine. Read
[054M](https://stacks.math.columbia.edu/tag/054M),
[01J3](https://stacks.math.columbia.edu/tag/01J3), and
[01J4](https://stacks.math.columbia.edu/tag/01J4), and fetched the original
morphisms.tex and schemes.tex into the sandbox scratchpad. Read the exact labels
lemma-reduction-universal-homeomorphism, lemma-reduced-closed-subscheme, and
definition-reduced-induced-scheme, plus the introductions to Reduced schemes and
Universal homeomorphisms. There are no ambient field, characteristic, finiteness,
separatedness, or Noetherian assumptions. The case T = X of 01J3/01J4 gives the
reduced induced structure on all points; 054M gives its universal homeomorphism.

Edge cases: empty schemes and their base changes are included; no Nonempty
assumption occurs. Affine zero rings are allowed. Already reduced and nonreduced
schemes are both allowed, including nilradicals which are not nilpotent ideals.
All characteristics are allowed. The declared universe u covers arbitrary
Scheme.{u}; all test schemes are in that same category, with no smaller independent
test universe. Empty index sets, zero objects of additive categories, and n = 0
are not parameters of this statement. The proof's nilpotence exponents are
existential witnesses, not extra theorem assumptions.

Independent searches (alternative wording to the first reader):

- msearch leanfinder: “nilradical closed subscheme reduced surjective inclusion
  remains homeomorphism after arbitrary pullback”: eight hits, including
  PrimeSpectrum.isHomeomorph_comap, quotient-spectrum bijectivity, and
  isIso_of_isClosedImmersion_of_surjective (which additionally assumes the target
  reduced). None states the full conjunction.
- msearch loogle: “AlgebraicGeometry.Scheme.IdealSheafData.subscheme,
  AlgebraicGeometry.IsReduced”: zero hits.
- msearch grep: “subschemeι|support_nilradical|IsHomeomorph” in
  AlgebraicGeometry/IdealSheaf: fourteen hits, construction/support facts only.
- rg in Mathlib, WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json
  for nilradical.subscheme, reduction/homeomorphism in either order,
  reduced/closed/surjective, and the proposed theorem name. Opened upstream
  isReduced_nilradical_subscheme (reducedness alone) and UniversalHomeomorphism.lean
  (general surjective closed immersion instance and bridge to the universal
  topological predicate). Neither is the item's full statement. The project
  references are proof docstrings, not another declaration of this statement.
  No duplicate notion is introduced: every notion uses its recorded dependency.

H5/H6/H8/H9: no definitions, private copies, or proved auxiliary statements.
The sole theorem has a sorry proof. Its docstring follows all three node proof
steps, cites the relevant DAG nodes, and names 054M and 01J3/01J4 with the exact
blueprint marker. Imports supply the six constructions/properties used. Explicit
universe u, bound X, correct namespace and topic, and lines at most 100 characters.
There are no new nodes, dependency modules, or statement corrections to review.
The node's lean.statement was checked verbatim against the theorem signature.

Changes: appended this independent review only; retained the correct Lean and node
record. Server scompile of the module succeeded (exit 0, 1.6 seconds) with no
warnings. The first local invocation used a relative path from the repository;
re-running with the absolute sandbox path compiled successfully.
