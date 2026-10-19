## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianChowModification` states
`AlgebraicGeometry.exists_projective_modification_of_isAffine_isNoetherian`.
Its only proof is `sorry`; it adds no definitions.

Clause-by-clause correspondence:
- Schemes S and X: `{S X : Scheme.{u}}`, with the universe explicitly declared.
- S affine: `[IsAffine S]`.
- S Noetherian: `[IsNoetherian S]` (locally Noetherian and quasi-compact).
- The given proper morphism X → S: `(f : X ⟶ S) [IsProper f]`.
- X reduced: `[IsReduced X]`, exactly the section-wise equivalent condition in the node.
- Existence of Y and π : Y → X: `∃ (Y : Scheme.{u}) (π : Y ⟶ X)`.
- A dense open U in X: `(U : X.Opens)` and `Dense (U : Set X)`.
- π proper: `IsProper π`.
- The induced map π⁻¹(U) → U is an isomorphism: `IsIso (π ∣_ U)`.
  Mathlib's `Scheme.Hom.morphismRestrict` has precisely source `(π ⁻¹ᵁ U).toScheme`
  and target `U.toScheme`, using the canonical open-pullback identification.
- Y → S projective: `IsProjective (π ≫ f)`; the structural map is the given composite.

Dependency declarations read and used:
- `def-pc-projective-morphism`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective`, extending `IsHProjective` and `QuasiCompact`.
  Read the current source via `scompile.py --source` because this extracted module is
  absent in the older local checkout. Its finite coordinate type is the canonical
  upstream encoding of finite projective dimension; no substitute definition is introduced.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, defining reducedness on all open sections; its stalk
  equivalence is supplied by `isReduced_of_isReduced_stalk` and `isReduced_stalk_of_isReduced`.
- `def-weil-pbc-scheme-conventions` is explicitly a convention node without a declaration.
  Its canonical Mathlib notions `Scheme`, `IsAffine`, `IsProper` and the restriction API
  are used. `IsNoetherian` is from `Mathlib.AlgebraicGeometry.Noetherian`.
- Proof-plan imports include `WeilConjectures.AlgebraicGeometry.ChowLemma`
  (`ChowModification.nonempty_data`), `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
  (`ProjectiveSpace.instIsProper`), and Mathlib's Proper, ClosedImmersion and FiniteType
  modules for the remaining recorded proof dependencies. The proof docstring writes
  out all three node proof steps, including the closed-immersion and quasi-compactness checks.

Edge cases checked: no nonempty or irreducibility assumption is imposed on X or S.
For empty X, the empty open is dense in X and its identity restriction is an isomorphism;
Y may be empty. An empty base forces empty X. Disconnected reduced schemes are allowed;
the dense open need not be affine or connected. U may be all of X when f is projective.
No surjectivity or reducedness of Y is added to the conclusion. Although the general Chow
argument needs neither affineness of S nor reducedness of X, both hypotheses are retained
because they occur in this node. There is no change to the natural-language statement.

Searches:
- `msearch.py ... leanfinder "A reduced proper scheme over an affine Noetherian scheme
  admits a proper projective modification isomorphic over a dense open"`: eight hits,
  on Proj properness, projective spectrum and related declarations; no exact match.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, AlgebraicGeometry.IsProjective"`:
  zero hits; IsProjective is unknown to that Mathlib search service (it is upstream).
- `msearch.py ... leansearch "Chow lemma projective modification proper scheme"`:
  service unavailable, Internal Server Error; this is an unavailable search, not a negative result.
- `msearch.py ... grep "Chow|projective.*modification" AlgebraicGeometry`: zero Mathlib hits.
- `rg` searches of `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf` for Chow,
  modification and projective modifications: the upstream Chow API supplies separate
  construction properties, not this existential theorem. Read `ChowModification.Data`,
  `nonempty_data`, `exists_dense_isIso_restrict` and `isClosedImmersion_toProjectiveSpace`.
  Project `ChowFactorization` has no dense-open conclusion; `ChowModificationData` instead
  assumes a nonempty scheme and returns an immersion and an ideal. Neither is this statement.
- Search of all upstream WeilConjectures for the exact blueprint id returned no match.

No new nodes, dependency repairs, statement corrections or disputed statements.

## Second reading by ND

I read the item node and its blueprint source, Stacks `coherent.tex`, Section
Chow's Lemma, Tag 0200 (statement and proof), and `morphisms.tex`, Tag 01W8.
The section assumes only the explicitly stated Noetherian base and separated
finite-type map. Properness supplies the latter assumptions. The blueprint adds
an affine base and reduced source, both retained here. Its projectivity convention
is H-projective plus quasi-compact, not the broader projective-bundle convention.

Object/hypothesis/conclusion checklist (each verdict: exact):
- Base scheme S and source scheme X: `{S X : Scheme.{u}}`.
- S affine: `[IsAffine S]`; S Noetherian: `[IsNoetherian S]`.
- Given structural morphism X → S: `(f : X ⟶ S)`.
- That morphism proper: `[IsProper f]`.
- X reduced: `[IsReduced X]`.
- A scheme Y and map π : Y → X: `∃ (Y : Scheme.{u}) (π : Y ⟶ X)`.
- An open U of X: the next existential binder `(U : X.Opens)`.
- π proper: `IsProper π`.
- U dense in X: `Dense (U : Set X)`.
- The induced map π⁻¹(U) → U an isomorphism: `IsIso (π ∣_ U)`.
  I opened Mathlib `Restrict.lean`: `Scheme.Hom.morphismRestrict` has source
  `(π ⁻¹ᵁ U).toScheme` and target `U.toScheme`, constructed using the canonical
  pullback-restriction isomorphism. Thus this is exactly the requested map.
- Y projective over S with the inherited structure map: `IsProjective (π ≫ f)`.
  The existential quantifiers precede all four simultaneous conclusions; no
  extra surjectivity, reducedness of Y, or condition on U is imposed.

I opened all three statement dependency nodes and their declarations. The
convention node deliberately has no independent declaration. Mathlib's
`IsReduced.component_reduced` gives reduced sections; the adjacent stalk
implication and converse identify this with the node's reduced local rings.
Mathlib's `IsNoetherian` is locally Noetherian plus compact. `IsProper` extends
separated, universally closed and locally finite type; universal closedness
supplies quasi-compactness, hence the node's finite type. I read the current
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective` through
`scompile.py --source`: `IsHProjective.exists_isClosedImmersion` uses a finite
coordinate type, an actual closed immersion, and the equation over the base;
`IsProjective` adds quasi-compactness. This is the recorded node convention.
Allowing an empty coordinate type only adds the empty projective space, whose
empty closed subscheme also embeds into P⁰, and changes no projectivity case.

Edge cases: X and S may be empty; Y may be empty and U may be empty when X is
empty (the empty subset is dense in the empty space). No Nonempty or
irreducibility hypothesis excludes disconnected reduced schemes. U may be X.
No characteristic, field, dimension, or numerical index is fixed. In particular
P⁰ is allowed by the projectivity interface. The declared universe u is arbitrary;
all schemes and morphisms use the standard Scheme.{u} category, and finite
coordinate types can be lifted into u. No independent test-object universe or
unbound universe/variable occurs.

Independent searches used different terms from the worker:
- LeanFinder via msearch: "proper birational morphism from a projective scheme
  to a proper scheme over a noetherian affine base". Eight hits, including Proj
  properness and finite-morphism characterizations; none states this theorem.
- Loogle via msearch: `AlgebraicGeometry.IsProper, Dense`: zero hits.
- LeanSearch via msearch: "A proper scheme is dominated by a projective scheme
  with isomorphism on a dense open": unavailable (Internal Server Error), not
  counted as a negative search result.
- Independent rg in Mathlib, upstream WeilConjectures and project lean/Sheaf
  for birational, Chow, projective modification and modification projective.
  I opened upstream `ChowLemma.Data`, `nonempty_data`, the dense-restriction
  theorem and the proper-case closed-immersion instance. They provide the
  ingredients separately, not this existential declaration. I also opened
  upstream `ChowLemma/ProjectiveDomination.lean`: its existence theorem has
  no dense-open-isomorphism conclusion. Project `ChowFactorization.lean`
  likewise has no dense-open clause; `ChowModificationData.lean` assumes a
  nonempty source and concludes an immersion and complement ideal, not the
  present statement. No exact match. The chosen declaration name is absent
  from upstream names, upstream source and project source.

The module has no new definitions, helper nodes or dependency repairs to review.
There is no statement_change or citer audit to validate. Its only theorem ends
in `sorry`; no data is postponed. The declaration and module docstrings name the
source and blueprint. The proof docstring follows all three DAG proof steps:
Chow data, properness making the immersion closed, then H-projectivity plus
quasi-compactness. The imported proof modules cover the recorded dependencies.
The node's lean.statement is verbatim the file's signature.

Mismatches found: none. Changes: this second-reading report only; the correct
Lean module and node are unchanged. Required scompile.py compiled the delivered
module cleanly, with no errors or warnings (sandbox and library checks).
