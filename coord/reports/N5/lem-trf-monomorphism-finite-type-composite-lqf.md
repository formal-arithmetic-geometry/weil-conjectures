## Worker report

Stage 2, N5, 2026-10-22. The module
`Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite` states
`AlgebraicGeometry.Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp`.
Its sole proof is `sorry`; its docstring gives all four steps of the live reviewed split.
Only the item's `lean` field changes. No new definitions, dependency repairs, statement
corrections, or stage-1 splits are delivered. In particular, Q145's reviewed stage-1 split
is retained verbatim. No repair note exists for this item in the read clone.

Hypotheses and conclusions, in the node's order:

| Node text | Lean |
| --- | --- |
| Arbitrary schemes X, Y, Z and morphisms f, g | `{X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)` |
| f is a monomorphism, tested on every scheme T | `[Mono f]`; `Mono.right_cancellation` quantifies over every object T and a,b:T ⟶ X |
| g composed with f is locally of finite type | `[LocallyOfFiniteType (f ≫ g)]`; Lean composition is written in diagrammatic order |
| f is locally of finite type | `LocallyOfFiniteType f` |
| Its canonical diagonal is an isomorphism | `IsIso (pullback.diagonal f)` |
| The diagonal is an open immersion | `IsOpenImmersion (pullback.diagonal f)` |
| The diagonal is a closed immersion | `IsClosedImmersion (pullback.diagonal f)` |
| f is separated | `IsSeparated f` |
| f is unramified | `IsUnramified f` |
| f is quasi-finite at every point in sense (1) | `(∀ x : X, IsQuasiFiniteAtPoint f x)` |
| f is locally quasi-finite in sense (2) | `IsLocallyQuasiFinite f` |
| No quasi-compactness of X or separatedness of g | Neither occurs among the binders |

Both final clauses are retained because the node explicitly gives both; the recorded
`IsLocallyQuasiFinite` definition is definitionally the preceding pointwise assertion.
The recorded `IsQuasiFiniteAtPoint` uses affine opens U and V, x in U, U ≤ f⁻¹(V),
an `Algebra.FiniteType` witness for `f.appLE`, and `Algebra.IsQuasiFiniteAtPrime`
at `hU.primeIdealOf x`. Thus it includes the affine-neighbourhood finite-type and
isolated-fibre-point content rather than substituting bare Mathlib `LocallyQuasiFinite`.
`IsUnramified` is exactly the recorded conjunction of local finite type and open diagonal.
`pullback.diagonal` is the canonical lift of the two identities into `pullback f f`.

Read the statements and lean/mathlib_match records of every statement dependency,
and read these source declarations and their docstrings:

| Dependency | Module | Declaration used |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | `AlgebraicGeometry.Scheme`, its morphisms |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType | `AlgebraicGeometry.LocallyOfFiniteType` |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | `CategoryTheory.Limits.pullback` |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion | `AlgebraicGeometry.IsOpenImmersion` |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | `AlgebraicGeometry.IsClosedImmersion` |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | `AlgebraicGeometry.IsSeparated` (defined in its public Separated import) |
| def-weil-unramified-morphism | Sheaf.AlgebraicGeometry.UnramifiedMorphism | `AlgebraicGeometry.IsUnramified` |
| pqf-def-quasifinite | WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism | `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`, `IsLocallyQuasiFinite` |

Every statement-dependency module is imported publicly. The proof-only dependency
`lem-weil-pbc-unramified-quasi-finite-at-points` is imported privately from
`WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite`, declaration
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_unramified`.
The other proof-only dependency, clause (a) of
`lemma-nagata-finite-type-to-separated-target`, is
`AlgebraicGeometry.locallyOfFiniteType_of_comp` in the already public FiniteType import.
There are no omitted proof imports or import cycles.

Sources read locally: morphisms.tex `lemma-permanence-finite-type` (01T8),
`lemma-diagonal-unramified-morphism` (02GE), `lemma-unramified-quasi-finite` (02V5),
and schemes.tex `lemma-monomorphism` (01L3), `lemma-monomorphism-separated` (01L4).
Their hypotheses agree with the node and the theorem. No statement dispute was found.

Edge cases checked before writing:

- Empty X: no nonempty binder; the pointwise clause is vacuous and the diagonal
  is still an isomorphism. Empty targets introduce no excluded case.
- Identity f: under the composite local finite type hypothesis all clauses hold,
  and the monomorphism diagonal is the ordinary identity pullback identification.
- A closed point Spec k into Spec k[ε]/(ε²): the theorem does not incorrectly
  assert that f is open or étale; it asserts only that its diagonal is open.
- A non-quasi-compact open immersion, with g the identity: its composite is
  locally finite type and the conclusion asserts local, not global, quasi-finiteness.
- g need not be separated: no condition on it occurs beyond the composite.
- Dropping monicity would admit the affine line over a field, contradicting the
  isomorphic-diagonal conclusion; `[Mono f]` is substantive.
- `u` is explicit and arbitrary; no independent small test-scheme universe,
  cardinality, characteristic, finiteness, or nonemptiness restriction is imposed.

Searches performed with the prescribed msearch.py wrapper (all on 2026-10-22):

- leanfinder: "A monomorphism of schemes whose composite is locally of finite type
  has isomorphic diagonal and is unramified and locally quasi-finite". Eight hits,
  including `FormallyUnramified.isOpenImmersion_diagonal`, `.of_comp`, `IsPreimmersion`,
  and étale cancellation; no full conjunction with the recorded pointwise notion.
- loogle: `AlgebraicGeometry.LocallyQuasiFinite, CategoryTheory.Mono`: zero hits.
- grep in Mathlib AlgebraicGeometry:
  `locallyOfFiniteType_of_comp|isIso_diagonal_iff|isSeparated_of_mono|isLocallyQuasiFinite_of_mono`.
  Three hits: finite-type cancellation, monomorphisms separated, and a use of the
  isomorphic-diagonal criterion. These are components, not the complete statement.
- leansearch: "A monomorphism of schemes with locally finite type composite has
  isomorphic diagonal and is unramified and locally quasi-finite". Eight hits,
  including `pullback.isIso_diagonal_iff`, formally unramified components and
  composition of Mathlib local quasi-finiteness; no complete match.
- rg in both project roots: the exact node id gives no hits. Searches for
  `monomorphism.*locally.*finite|mono.*isLocallyQuasiFinite|isLocallyQuasiFinite.*mono|unramified_of_mono`
  find the affine étale relation consumer, whose additional relation and étaleness
  data and six conclusions differ from this general lemma. The broader search for
  monomorphisms and finite type likewise supplies no exact declaration.
- rg of Mathlib, WeilConjectures, and Sheaf for the chosen full declaration suffix
  `monomorphism_properties_of_locallyOfFiniteType_comp` gives no existing declaration.

Validation: scompile.py compiled this single module in both sandbox and library modes
against the live server library, with no errors or warnings (8.4 s and 5.7 s).

## Second reading by N5

This is a separate self-audit after writing and compiling, not an independent-agent
review: the dispatcher expressly forbids starting another agent, and the maintainer
performs the independent delivery review. Reopened the live node and the delivered
module. The two hypotheses are exactly `Mono f` and local finite type of `f ≫ g`;
the three scheme and two morphism binders have the node's domains and codomains.
The eight conjuncts match local finite type, isomorphic diagonal, open diagonal,
closed diagonal, separatedness, unramifiedness, pointwise quasi-finiteness, and local
quasi-finiteness respectively. In particular, the open-immersion assertion applies to
the diagonal, not to f. Checked the imported `IsUnramified` body and upstream
`IsQuasiFiniteAtPoint`/`IsLocallyQuasiFinite` bodies against the node's cited definitions.
The pointwise clause retains finite type of the affine section map; no Mathlib-only
stalkwise replacement is made. No mismatch or node correction was found. No changes
were needed in this second pass. The JSON signature is extracted verbatim from the
theorem keyword to before `:=`, and all other original node fields are retained.
