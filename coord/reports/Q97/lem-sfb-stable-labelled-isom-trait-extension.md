## Worker report

The module `Sheaf.AlgebraicGeometry.StableLabelledIsomTraitExtension` states
`AlgebraicGeometry.existsUnique_stable_labelled_isom_trait_extension`. Its only theorem
has proof `sorry`; it introduces no definitions, axioms, helper theorems, or new DAG nodes.
The item's natural-language statement and dependency lists are unchanged.

Hypothesis and conclusion correspondence:

- The schemes `S W W' : Scheme.{u}` and `[IsLocallyNoetherian S]` give the locally
  Noetherian base and the two total spaces. The maps `f`, `f'` are their structural maps.
- `n : ℕ` includes zero. The families `s`, `s' : Fin n → ...` are labelled sections;
  `hs`, `hs'` assert their section identities. The hypotheses `hstable`, `hstable'`
  use exactly the recorded `IsStablePointedCurve`, including projective-bundle
  projectivity, flatness, finite presentation, connected nonempty nodal geometric
  fibres, reducedness, pure dimension one, disjoint smooth markings, and the
  component-normalization stability inequalities.
- `σ : Equiv.Perm (Fin n)` is the prescribed permutation of the labels, with
  the zero-based `Fin n` convention merely reindexing the node's one-based labels.
- `R K : Type u`, the commutative-domain and DVR instances on `R`, and `[Field K]`,
  `[Algebra R K]`, `[IsFractionRing R K]` give an arbitrary DVR and its fraction field.
  No excellence, finite-type, residue-characteristic, or uniformizer choice is required.
- `b : Spec (.of R) ⟶ S` is arbitrary. There is no condition on its underlying points.
- `Over.pullback b` makes `W_R`, `W'_R` with second projections as structural maps.
  Applying `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))` gives the
  iterated generic fibre products `W_K`, `W'_K`. These are the node's fibre products,
  with the canonical associativity convention made explicit rather than an arbitrary
  identification with the direct pullback to `S`.
- `uK` is an isomorphism in `Over (Spec (.of K))`, so it is precisely a K-isomorphism,
  with base compatibility included in its type. It is not required to be an identity,
  and neither generic fibre has a smoothness hypothesis.
- `hmarks` says that the iterated canonical pullback of `s i`, followed by `uK.hom.left`,
  equals the iterated canonical pullback of `s' (σ i)`. The equations are equations
  of scheme morphisms, not pointwise agreement on the underlying spaces.
- `∃! uR : ... ≅ ...` quantifies over R-isomorphisms of the two trait pullbacks.
  The first conjunct gives every required equation on the trait's pulled sections.
  The second conjunct, `(...).mapIso uR = uK`, says the generic restriction is the
  specified isomorphism, including both arrows and the structure-map compatibility.
  Equality of isomorphisms in `Over` is equivalent to equality of the underlying
  scheme isomorphisms: the remaining compatibility fields are propositions.
  The unique-existence binder gives exactly one R-isomorphism satisfying both clauses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  its full class signature and every-affine Noetherian-ring interpretation.
- `Sheaf.AlgebraicGeometry.StablePointedCurve`: `AlgebraicGeometry.IsStablePointedCurve`,
  including its full body, normalized-component genus and special-point construction.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`, extending
  principal ideal ring and local ring with nonzero maximal ideal, together with `IsDomain`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`, used
  through the public imports of the statement dependencies.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  `pullback.snd`, through the existing scheme-pullback interface.
- `WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection`:
  `Scheme.Hom.baseChangeSection` and `baseChangeSection_snd`, already publicly
  imported by the recorded stable-pointed-curve module. Their bodies were read:
  these are the universal-property lift `(b ≫ s, 𝟙)` and its second projection equation.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`, whose object is
  `Over.mk (pullback.snd g.hom f)`, and its functorial action on isomorphisms.
  This uses the recorded fibre-product construction rather than a new base-change notion.

Proof-only imports preserve all available modules of the node's proof dependencies:
ClosedImmersionProducts, ProjectiveSpace, QuasiSeparated, Etale,
NodalLogCanonicalReconstruction, SemistableLogPluricanonicalLattices,
RelativeProj.Functoriality, Morphisms.ProjectiveImpliesProper, Cohomology.EulerChar,
Flat.Localization, and Morphisms.Separated. Flat and closed-immersion base change
are already present transitively. `lem-trf-projective-bundle-affine-presentations`
and `lem-sfb-proper-ample-section-proj-reconstruction` have no recorded module in
this checkout, so no speculative import is added for them; they are proof-only
prerequisites and are named in the complete six-step theorem docstring.

Sources read: the node's entire statement and six-step proof, every statement-dependency
record, the Lean dependency declarations above, and Stacks moduli-curves.tex
`lemma-unique-stable-model` (Tag 0E97). The latter assumes a smooth unmarked generic
curve and is motivation only, as the node explicitly says; no such restriction was
introduced. Also read de Jong (1997), §3.8, printed pp.608–609, from
https://www.numdam.org/item/10.5802/aif.1575.pdf: its last paragraph uses finiteness
and unramifiedness of the Isom scheme of unordered stable marked curves over a normal
base. The present node supplies the labelled DVR extension prerequisite, rather than
replacing it by the source’s smooth-generic-fibre model lemma.
The theorem docstring carries the full marked log-canonical route.

Edge cases checked by reading the resulting signature:

- `n = 0` leaves both marking quantifiers empty, with the unique permutation on `Fin 0`.
- Arbitrary residue characteristic and nonexcellent DVRs are covered by the exact
  Mathlib DVR class; no extra instances restrict them.
- A trait whose generic point maps to a closed or nongeneric point of `S` is allowed.
- Persistently nodal generic fibres and nontrivial generic automorphisms are allowed.
- Empty bases are not excluded by a new binder; with a DVR trait the map `b` into an
  empty base cannot exist, exactly as in the node. Empty total spaces are ruled out
  only by the existing nonempty-geometric-fibre stability predicate.
- A single arbitrary ambient universe contains all the schemes and rings, matching
  the recorded stable-curve predicate; no independent smaller test universe is imposed.
- Pulling back in two stages includes canonical marking maps at both stages and
  supplies the required parenthesization without arbitrary choices or added hypotheses.

Searches actually run (2026-10-24):

- `msearch.py leanfinder`: “A generic labelled isomorphism of stable pointed curves
  over any discrete valuation ring extends uniquely over the ring”. Eight hits were
  general valuative-criterion declarations and minimal Weierstrass models; none states
  extension for stable pointed families.
- `msearch.py loogle`: `IsStablePointedCurve, IsDiscreteValuationRing` returned zero
  hits, with `IsStablePointedCurve` unknown to the Mathlib search service.
- `msearch.py leansearch`: “A generic isomorphism of stable pointed curves over a
  discrete valuation ring extends uniquely”. Eight hits were good-reduction congruence,
  stalk and normalization isomorphisms, and general base-change properties; no match.
- `msearch.py grep`: `IsStablePointedCurve|stable.*[Ii]som|[Ii]som.*[Ss]table` in
  `AlgebraicGeometry` returned zero Mathlib hits.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for stable/isomorphism phrases and canonical section names found the recorded
  stable predicate, generic spreading extension, moduli groupoids and downstream
  arithmetic Isom finiteness; none is this unique DVR-extension theorem.
- `grep -rn` for this item id in `lean/WeilConjectures` returned no match.
- `rg` for `stable_labelled_isom_trait_extension|existsUnique_stable_labelled` over
  both libraries and the upstream-name index returned no existing declaration.

No statement discrepancy, disputed mathematical claim, dependency-interface repair,
or new-node requirement was found. The withdrawn CompactObject example module was
also opened; it currently has no declarations, so the current stage-2 module header
conventions were taken from the standing brief and the recorded StablePointedCurve module.

## Second reading by Q97

No second reading by a worker: the dispatcher's direct-delivery instruction reserves
independent review for the maintainer. No other agent was started.

Validation: `scompile.py Q97 lem-sfb-stable-labelled-isom-trait-extension` compiled
this module against the live server library with no errors or unexpected warnings.
`deliver2.py Q97 lem-sfb-stable-labelled-isom-trait-extension --no-push` returned
`OK (dry run): commit 32a2b1e4a06 passes the preflight and compiles; nothing pushed`.
