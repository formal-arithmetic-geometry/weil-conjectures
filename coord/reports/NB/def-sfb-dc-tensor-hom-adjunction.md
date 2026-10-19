## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves`
defines
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleTensorHomAdjunctionOfPreserves`.
Its data is exactly the restriction of the ambient relative tensor–Hom adjunction. There are
no new theorems, axioms, postponed proofs, helper nodes, dependency repairs or statement changes.
The source is the current main-20261015 blueprint item and its three-step DAG proof, read
together with the parent unit `sk-def-sfb-dc-restricted-functors/_section.md`.

Hypotheses and clauses, matched individually:

| Node/source clause | Lean rendering |
| --- | --- |
| The setting of both cited functor definitions fixes distinct primes ℓ,p and a field k of characteristic p. | Explicit `(ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`. Here p is `ringChar k`, exactly as in the recorded Hom interface and ambient framework. |
| X is separated and of finite type over k. | `(X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]`. Locally finite type plus quasi-compactness is finite type. |
| Λ is a commutative condensed ring. | `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]`. No finiteness-coefficient class is imposed. |
| The tensor preservation property of `def-sfb-dc-tensor` holds. | `hT` quantifies over every pair of bounded constructible objects and asserts bounded constructibility of their ambient `derivedTensor` value. |
| The Hom preservation property of `def-sfb-dc-hom` holds simultaneously. | `hH` quantifies over every such pair and asserts bounded constructibility of the ambient `derivedHom` value, contravariant in its first argument. |
| K belongs to D_cons(X,Λ). | `(K : BoundedConstructible (condensedRingObj Λ X.left))`, the recorded full subcategory of the ordinary unbounded derived category of internal module objects. |
| The left functor is the specified restricted K ⊗ᴸ -. | The left endpoint is `(boundedConstructible _).lift ((boundedConstructible _).ι ⋙ (derivedTensor Λ X.left).obj K.obj) (fun A ↦ hT K A)`. This is precisely the fixed-K specialization specified by the dependency's Mathlib match, with the same objects and ambient morphisms. |
| The right functor is the specified restricted RHom(K,-). | The right endpoint is `(boundedConstructibleHomOfPreserves Λ ℓ X hH).obj (op K)`, using the dependency's recorded declaration unchanged. |
| These form an adjunction on D_cons. | The return type is an `Adjunction` between these two endofunctors of that full subcategory. |
| It is the restriction of the ambient adjunction along the fully faithful inclusion. | Its body is `(derivedTensorHomAdjunction Λ K.obj).restrictFullyFaithful` with `ObjectProperty.fullyFaithfulι` twice. The comparison inputs are the inverses of `ObjectProperty.liftCompιIso` and the recorded `boundedConstructibleHomOfPreservesObjCompatibility`. They both have identity components. |

The ell-adic coefficient examples belong to the cited preservation nodes; this definition
takes their preservation conclusions as hypotheses, as the item's proof explicitly requires.
It does not assert preservation for a general coefficient ring. No unit-closure or monoidal
subcategory assumption is needed: only the two stated pairwise preservation properties.

Dependency declarations read and used:

- `def-sfb-dc-tensor`: Mathlib's `CategoryTheory.ObjectProperty.lift` and
  `CategoryTheory.ObjectProperty.liftCompιIso`, in
  `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`. Its `mathlib_match` explicitly
  describes this fixed-K lift. It has no separate specialized recorded declaration to import.
- `def-sfb-dc-hom`: `boundedConstructibleHomOfPreserves` and
  `boundedConstructibleHomOfPreservesObjCompatibility` in
  `Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves`. Both full signatures,
  docstrings and construction bodies were read.
- `sk-def-sfb-derived-tensor-hom`: `derivedTensor`, `derivedHom` and
  `derivedTensorHomAdjunction` in the `AlgebraicGeometry.ProEtale.CondensedRing` namespace,
  supplied by `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its tensor
  import. Read these in the precise side framework, and read
  `coord/pefw-upstream-framework.md`. This is layer B, tensor over Λ_X, with no change of
  coefficient category. The Hom dependency publicly imports this ambient module.
- `sk-def-sfb-bounded-constructible`: `AlgebraicGeometry.ProEtale.boundedConstructible` and
  `AlgebraicGeometry.ProEtale.BoundedConstructible`, publicly re-exported by the recorded
  module `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`, which is imported.
  Its retained general internal-module declarations, and their original full signatures and
  docstrings, were read; the added discrete-coefficient presentation is not used.
- `Mathlib.CategoryTheory.Adjunction.Restrict`: `Adjunction.restrictFullyFaithful`,
  including its explicit Hom-equivalence definition and its existing unit/counit formulas.
  This provides the exact construction specified in proof step 3.

Edge cases checked by reading the construction:

- Empty schemes and zero bounded constructible objects are not excluded. No nonempty,
  nonzero or positive-rank premise is present. Restriction works on any objects of the
  full subcategory, and the supplied preservation hypotheses cover every pair.
- Arbitrary commutative condensed coefficients are allowed conditionally. In particular,
  the familiar unbounded Tor/Ext example over ℤ/4 is not silently asserted to satisfy
  either preservation hypothesis; the live upstream source explicitly documents it.
- No tensor-unit membership is assumed: binary preservation is sufficient for restriction
  of this unary adjunction, even without a monoidal structure on the subcategory.
- The first argument of Hom is opposite; tensor has the fixed K on the left. Both
  compatibility isomorphisms are reversed to have exactly the orientation required by
  `restrictFullyFaithful`.
- Universe `u` is explicit, with schemes/field in `u`, condensed abelian values in `u+1`,
  matching the dependency interfaces. `autoImplicit false` is explicit.
- The body fixes the Hom equivalence, unit and counit via the ambient adjunction; it is
  not a choice from a proposition asserting mere existence of an adjunction.

Searches for an existing declaration:

- `msearch.py ... leanfinder "derived tensor internal Hom adjunction restricted to bounded
  constructible complexes"`: eight general condensed/derived/Gabriel–Popescu hits; none
  states the conditional restricted adjunction here.
- `msearch.py ... loogle "CategoryTheory.Adjunction.restrictFullyFaithful"`: six hits,
  comprising the general restriction construction and its Hom/unit/counit formulas.
- `msearch.py ... leansearch "restrict an adjunction to a full subcategory when its left
  and right adjoints preserve the subcategory"`: eight hits, including the same general
  restriction construction. Reused, not redefined.
- `msearch.py ... grep "restrictFullyFaithful|boundedConstructibleTensorHomAdjunction"
  CategoryTheory`: seventeen general restriction uses/declarations; no project-specific
  conditional adjunction.
- `rg` of `boundedConstructibleTensorHomAdjunction`, the proposed new declaration name,
  and the item id in the slopmaster2 `WeilConjectures` sources and `lean/Sheaf`: no exact
  conditional declaration. Searching `dag/lean_names_upstream.json` likewise found no
  collision for the new name. `grep -rn` of the exact item id in the source found none.
- Read `scompile.py --source
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`: the
  published upstream `boundedConstructibleTensorHomAdjunction` assumes
  `IsEllAdicFinitenessCoefficient ℓ Λ` and uses the monoidal full-subcategory functors.
  It does not supply the item's arbitrary-coefficient conditional interface. The older
  local side source has stale unrestricted preservation assertions; the published source
  and the newly recorded conditional Hom dependency are used instead.
- Direct `rg` in Mathlib confirms the new full name is absent. Mathlib's generic
  restriction construction is used as data for this specialized definition.

No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by NB

Author self-check, not an independent review: the dispatcher brief forbids starting other
agents and assigns the independent review to the maintainer. Reopened the completed module
and the item, both restricted-functor dependencies, the ambient adjunction, and the full
subcategory declarations. The table above accounts for every inherited setting hypothesis,
both simultaneous preservation assumptions, the fixed K, both adjunction endpoints, and the
canonical restriction clause. In particular, verified that no ell-adic coefficient class or
tensor-unit condition slipped in. The left lift is the exact Mathlib specialization in
`def-sfb-dc-tensor.mathlib_match`; the right endpoint uses the recorded conditional Hom
functor rather than an inline replacement. The construction's two identity comparisons
ensure the unit and counit are the ambient ones. No mismatch required a statement change.

Validation: `scompile.py NB def-sfb-dc-tensor-hom-adjunction <module.lean>` completed
cleanly, with no errors or warnings. It compiled the two required dependency overlays
and checked this file separately as sandbox and library modules, within the per-file
60-second limit (9.5 and 13.1 seconds respectively). The node delta was checked to contain
only `lean`, and every Lean line is within 100 characters. Delivery uses the prescribed
`deliver2.py --no-push` preflight and then `deliver2.py`.
