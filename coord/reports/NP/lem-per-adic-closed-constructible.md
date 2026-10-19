## Worker report

The module `Sheaf.Paper.AdicClosedConstructible` states
`lem-per-adic-closed-constructible`. Its five postponed theorems divide the
node's clauses into Hom closure, the normalized adjunction, the closed symmetric monoidal structure,
scalar naturality/evaluation/transposition, and identity/tower compatibility.
All five proofs are `sorry`; definitions contain actual constructions.

Hypotheses and clauses:

- Any field k is `(k : Type u) [Field k]`. No characteristic, finiteness,
  perfection, algebraic-closedness, or nonemptiness restriction is imposed.
- The prime invertible in k is `(l : ℕ) [Fact l.Prime]` and
  `[Fact (IsUnit (l : k))]`. `residueInvertible` maps this very unit through
  k -> Γ(T,O_T) -> κ(x), supplying the input required by the recorded operations explicitly, without
  adding a global instance. `tensor` abbreviates the published tensor declaration with this inverse
  passed explicitly.
- The separated finite-type k-scheme is `T : Scheme.{u}`, its `T.Over (Spec (.of k))`
  structure, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` of its
  structure morphism. The geometric assumptions are explicitly included in
  `hom_constructible`, even though the predicate itself does not mention k.
- E/Q_l is `(E : Type u) [Field E] [Algebra ℚ_[l] E]`
  `[FiniteDimensional ℚ_[l] E]`. The integer ring and uniformizer are exactly
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`
  used by the imported coefficient constructions, not extra chosen rings.
- The completed sheaf is `completedIntegralCoefficientSheafUnrestricted l E T`.
  The ambient category `DerivedCategory (integralTowerModules l E T)` is modules
  over this completed ring. The constant-to-completed map is publicly imported
  from `CompletedIntegralConstantMapOfUniverses`.
- I_T is exactly `sfIntegralConstructibleCategory l E T`: derived completeness,
  bounded constructible positive reductions, and one finite interval common to
  all reductions. No different integral constructibility predicate is introduced.
- `hom_constructible` states membership of the ambient
  `integralDerivedInternalHom` for every P,Q in I_T. `hom` is its actual
  full-subcategory lift, on both objects and arrows, using this theorem.
- `closed_symmetric_monoidal` asserts existence of a
  `CoefficientClosedStructure (hom l k T E)` with a `SymmetricCategory` structure.
  `S.tensor = tensor l k T E` (the published `constructibleIntegralTensor`) fixes the complete tensor
  bifunctor, including arrows. The unit's underlying object is precisely the
  degree-zero complex of `SheafOfModules.unit` of the completed coefficient ring.
- `CoefficientClosedStructure.adjunction` supplies the natural Hom bijections.
  The last clause of `closed_symmetric_monoidal` fixes every transpose to
  `transpose`. `transpose_existsUnique` normalizes every image to ordinary
  ringed-site currying after the actual completion unit. That unit is the
  published reduction adjunction unit, its tensor comparison, and the inverse
  Roos-normalized tensor realization, composed directly in the signature.
  `transpose` selects this uniquely characterized bijection; no map or object
  is chosen from a mere uncharacterized existence assertion. `evaluation`
  is the inverse transpose of the identity.
- A finite extension E -> L is an arbitrary `E →ₐ[ℚ_[l]] L`, with L also finite
  dimensional over Q_l. This includes every inclusion and its identity.
  `extend` abbreviates the existing `sfConstructibleIntegralScalarExtension`;
  its legacy dummy p is instantiated with 0 and the prime's nonzeroness. It
  imposes no characteristic-zero hypothesis on k. `homScalar` is precisely
  the existing evaluation-defined isomorphism `scalarHomCompleteInputs`.
- `scalar_laws` first states naturality in both P and Q. Its second clause is
  the equation identifying this same isomorphism with the transpose of extended
  completed evaluation precomposed with `scalarTensorCompleted.inv`. Its third
  clause states compatibility with every tensor-Hom adjunction bijection.
- `scalar_coherence` first says that the identity comparison becomes the identity
  arrow under `sfIntegralScalarUnit`. The second clause quantifies over every
  finite coefficient tower E -> L -> F and uses exactly `sfIntegralScalarComp`
  on the source Hom object and on its two inputs. In the contravariant input
  it uses the inverse composition comparison, as required by the square's types.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient extension
  constructions and `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: completed coefficient
  sheaf and `integralConstantToCompletionOfUniverses`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the actual ambient operations and
  `constructibleIntegralTensor`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: the recorded scalar construction,
  with its original equal-universe interface publicly retained.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: `scalarHomCompleteInputs`,
  `scalarTensorCompleted`, and the evaluation/ordinary-completion normalization.
- `Sheaf.Paper.CompletedPullbackTensorComparison`: `pullbackTensorCalculus`,
  its actual reduction/limit adjunction and tensor comparison, and
  `pullbackTensorIntegralTensorModel`, with its unique Roos normalization.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfIntegralScalarComp` and
  `sfIntegralScalarUnit`, uniquely normalized by ordinary balanced tensor and
  the quotient-completion maps.
- `def-weil-scheme-morphism-properties` is a convention node, so its named
  Mathlib definitions are used directly. All usable recorded project proof modules
  are imported non-publicly unless already imported publicly; the failing proof-only
  IntegralHomReduction import is documented below. The unstated
  finite-Tor-any-field proof dependency has no module to import.

`def-pur-completed-pullback-tensor-comparison` and
`lem-weil-scalar-extension-composition` are added to `stmt_deps`, as permitted for already
landed notions, because their canonical completion and scalar composition
maps occur in the statement. No existing statement is changed and no dependency
record is replaced. A transitive graph search confirmed neither added dependency
reaches this item.

Sources read: the local Bhatt--Scholze PDF, Definition 3.4.10 and Lemma 3.4.11
(completion and its adjunction), and Lemmas 6.7.12--6.7.13 (tensor and Hom closure).
The DAG proof's residue-field induction and finite-free evaluation calculation
are retained step by step in the theorem docstrings. The finite-type field
hypothesis supplies the quasi-excellence needed by Lemma 6.7.13.

Edge cases checked: T empty; zero P,Q,M; k of characteristic zero and of any
positive characteristic different from l; arbitrary finite and ramified
coefficient extensions; identity embeddings; towers with either embedding the
identity; all cohomological intervals including [0,0] for zero reductions.
No nonempty space, nonzero object, finite base field, or positivity condition on
cohomological degrees is imposed. Universes use a common u containing all field
and scheme models; the small pro-etale site retains object universe u+1 and
morphism universe u, and coefficient modules retain the required lift.

Searches run:

- msearch LeanFinder: `derived complete constructible adic sheaves closed symmetric
  monoidal internal Hom finite coefficient extension`: eight light-condensed and
  solid-module hits, no statement for this integral constructible category.
- msearch Loogle: `CategoryTheory.MonoidalClosed, CategoryTheory.SymmetricCategory`:
  six generic monoidal reflection/distributivity hits, no adic constructible result.
- msearch grep: `MonoidalClosed|Closed.*Constructible|Constructible.*Closed`:
  generic module, condensed, and topology results, no match for the item.
- msearch LeanSearch: `derived complete constructible sheaves internal Hom closed
  symmetric monoidal category`: generic `MonoidalClosed`, `Closed`, and `ihom`
  results only.
- rg of the upstream WeilConjectures tree, side Sheaf tree and
  `dag/lean_names_upstream.json` for the item id, `adicClosedConstructible` and
  `sfIntegral.*[Cc]losed`: no item declaration; one unrelated isomorphism-closure
  lemma. Additional searches for completed evaluation located the usable partial
  adjunction in `DerivedAutomorphismHomEvaluation`, whose underlying smaller completion interface is reused here.
- Searches of upstream Mathlib, upstream WeilConjectures and side declarations
  for `AdicClosed` found no existing declaration namespace to conflict with.

## Second reading by NP

This is the dispatcher's worker self-reading; no other agent was started, as
required by the task. I reopened the node and matched every clause to the
signatures above. I explicitly retained the base-field and geometric binders in
the Hom-closure and normalized-adjunction theorems, checked that the unit is the completed ring rather than
its discrete constant sheaf, and checked the direction of the inverse in each
contravariant scalar-tower map. Evaluation is fixed by the uniquely normalized completed
adjunction and the scalar tensor comparison; no arbitrary comparison is chosen.
The identity and arbitrary finite-tower cases are present. The monoidal theorem
requires equality of the tensor bifunctors and fixes transposition, rather than
merely asserting existence of unrelated monoidal/closed instances.

Compilation repair: the first wrapper call stopped in the broad partial-adjunction
module's unrelated `SemilinearSystemModels` import, at universe constraints in
HasSheafify. The delivery removes that broad import and uses only the smaller
published `CompletedPullbackTensorComparison` interface. The actual completion
unit appears directly as a composite in `transpose_existsUnique`; the node's own
adjunction clause now supplies its uniquely determined Hom bijection. No source
module or launcher tool was changed.

A second compile stopped in the proof-only `IntegralHomReduction` module,
with universe constraints beginning at lines 98/103 and cascading errors in its
unrestricted ringed-site tensor presentation. This import is omitted from the
statement delivery; its proof dependency and proof-plan citation remain unchanged.
No statement uses that module's declarations. The maintainer will need to restore
this proof-plan import after that separate source module compiles again.

Validation: the prescribed scompile wrapper passed both its sandbox check (14.9 s)
and library-module check (9.5 s), with exit 0 and no warnings. All five postponed
theorems have complete proof plans and this node's blueprint id in their docstrings.
The maximum Lean line width is 99, and the primary lean.statement is an exact
substring of the source signature. No new nodes or dependency-module repairs
were needed; the item's mathematical statement is unchanged.
