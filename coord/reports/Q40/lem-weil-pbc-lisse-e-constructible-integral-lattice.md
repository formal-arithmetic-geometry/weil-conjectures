## Worker report

Q40 states `AlgebraicGeometry.ProEtale.exists_constructible_integral_lattice` in
`lean/Sheaf/Paper/LisseEConstructibleIntegralLattice.lean`. The original node statement
is unchanged. Its full seven-step natural-language proof is in the theorem docstring;
the Lean proof is `sorry`, as required for stage 2.

The continuous-constructibility interface absent from the library is supplied by the
new definition node described below. Every definition has explicit data. The only
additional postponed theorem proves naturality of the actual sectionwise coefficient
pullback; the new node explicitly includes that restriction law and its docstring gives
the pointwise proof. There is no arbitrary comparison map, no choice of a nonunique
object from an existence theorem, and no locally-free hypothesis on the integral model.

Hypotheses and conclusions, clause by clause:

- Prime ℓ: `(l : ℕ) [Fact l.Prime]`.
- Finite E/ℚℓ: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- The canonical valuation topology is carried by
  `WithAbs (Padic.coefficientExtensionAbsoluteValue l E)`. This is the existing
  transported field, not an independent choice of topology. Its valuation ring is
  `latticeCoefficientIntegers l E`, the existing transport of
  `Padic.coefficientExtensionIntegers l E`. The uniformizer is the one already supplied
  by the coefficient-extension interface; the assertion uses no extra uniformizer
  parameter or property and is invariant under its choice.
- Scheme T: `(T : Scheme.{u})`.
- Noetherian, in the finite-affine-cover sense stated in the node:
  `[IsLocallyNoetherian T] [CompactSpace T]`. Locally noetherian affine neighborhoods
  and quasi-compactness give the required finite affine cover; conversely that cover
  implies both hypotheses. No separation assumption is imposed.
- Finite dimension: `(_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ d)` bounds the
  supremum of strict irreducible-closed chains by a natural number.
- ℓ invertible in every local ring:
  `(_hℓ : ∀ x : T, IsUnit (l : T.presheaf.stalk x))`.
- E_T and A_T: `latticeModuleRing T (...)`, using the existing
  `latticeCoefficientSheaf` of continuous functions with pointwise operations and
  precomposition. Its `ULift` is a size transport, not a change of coefficients.
  The adic-coefficient-datum dependency explains the name completed coefficients;
  no inverse-system or derived-completion object from that node is used in this
  statement, which already explicitly defines its coefficient sheaf by C(|V|,A).
- L: the explicit `SheafOfModules.{u+1}` binder over this continuous E-ring sheaf.
- Pro-etale locally free of finite rank: `[L.IsFiniteLocallyFree]`. This permits
  varying finite ranks, including rank zero.
- Existence of integral N: `∃ N : SheafOfModules.{u+1}
  (latticeModuleRing T (latticeCoefficientIntegers l E)), ...`.
- Finite stratification and finitely presented local models:
  `IsContinuousConstructible T (latticeCoefficientIntegers l E) N`. Unfolding gives
  a `Scheme.LocallyClosedStratification T`; for every stratum a `CoversTop` family
  in its actual small pro-etale site; for every cover member an ordinary module P
  with `Module.FinitePresentation`; and an isomorphism, on that member, from the
  canonical ringed pullback of N to `continuousCoefficientModule ... P`.
- A_T tensor_A P: `continuousCoefficientModule` first forms the existing constant
  module sheaf of P and then uses `SheafOfModules.changeOfRings` along the actual
  constant-section coefficient map. Thus it is the sheaf tensor, not a pointwise
  tensor lacking sheafification.
- E_T tensor_A_T N ≅ L: `Nonempty (SheafOfModules.changeOfRings
  (integralLatticeCoefficientMap T l E) N ≅ L)`.
  This map is the existing continuous map induced by inclusion A → E.
- There is no assertion that N is globally finite locally free. P and the cover
  are permitted to vary with the stratum and the covering member.

Dependency declarations used (public imports also include their transitive modules):

- `Sheaf.Paper.LatticeSheafLocallyConstant`:
  `AlgebraicGeometry.ProEtale.latticeCoefficientPresheaf`,
  `latticeCoefficientSheaf`, `latticeModuleRing`, `latticeCoefficientIntegers`,
  `integralLatticeCoefficientMap`. The live source was checked with
  `scompile.py --source Sheaf.Paper.LatticeSheafLocallyConstant`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionAbsoluteValue`, `Padic.coefficientExtensionIntegers`.
- `Sheaf.Paper.AdicLisseModule`:
  `AlgebraicGeometry.Scheme.adicLisseConstantRing`, `adicLisseConstantModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafDirectImage`, `proEtaleSheafInverseImage`,
  `proEtaleSheafAdjunction`, `proEtaleModuleInverseImage`. These retain the small
  site's object universe u+1 and morphism universe u.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.LocallyClosedStratification`, including actual stratum
  schemes, immersions and their image identities.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses` and its imported
  tensor module: `SheafOfModules.changeOfRings`, the actual sheafified scalar tensor.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the recorded alias for `SheafOfModules`; the latter is used directly.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  the quasi-compact scheme node's recorded `CompactSpace`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` supplies the recorded small-site
  context; the underived continuous module statement uses that same `Scheme.ProEt`
  and `Scheme.ProEt.topology`, already imported through the coefficient interface.
- The main module additionally imports the available recorded proof-dependency
  modules (non-public imports), including finite-etale lattice descent, the etale
  finite stratification, exact functors and derived adjunctions, Ext and extension
  classification, K-injectives and Hom complexes, closed immersions, and ringed
  open/closed pro-etale functors. Unstated proof-only dependencies are not needed
  to elaborate a stage-2 statement.

Edge cases checked mathematically before writing:

- Empty T is allowed. There is no `Nonempty T` or positive-rank assumption. A
  zero-stratum stratification of the empty scheme makes the local-model condition
  vacuous, as it should; an empty covering family covers only an empty site object.
- Zero L and zero P are allowed; finite local freeness includes rank zero and
  finite presentation includes the zero module. No faithfulness, injectivity or
  nonzero scalar-extension condition was added.
- Disconnected strata and varying ranks are allowed. Neither irreducibility nor
  connectedness nor reducedness is imposed on T or its stratum schemes.
- Dimension uses `topologicalKrullDim`, so the empty-space bottom dimension also
  satisfies a natural-number bound. No assumption of positive dimension was made.
- E and T share a universe after common enlargement. Coefficient sheaf sections
  and ordinary modules use u+1 while site morphisms stay in u. No equality of the
  site's object and morphism universes was imposed, nor is any covering index
  quantified in an independent potentially smaller universe.
- Ringed pullback is inverse image followed by scalar extension along the
  canonical coefficient map. It does not silently identify f⁻¹A_Y with A_X.
  Pullback coefficients are constructed from actual precomposition along the
  first projection of V ×_Y X.

Searches for an existing statement or definition:

On resumption, the lattice-theorem LeanFinder query, the
`SheafOfModules, Module.FinitePresentation` Loogle query, and the helper-name
Mathlib grep were repeated. They again returned 8 unrelated hits, zero hits,
and zero hits respectively; the saved search log records these executions.

- `msearch.py ... leanfinder` with “Every lisse sheaf over a finite extension of
  the p-adic numbers has a constructible integral lattice”: 8 results, including
  `instModuleFinite_of_discrete_submodule`, `LocallyConstant.freeOfProfinite`, and
  `ZLattice.module_finite`; none is this sheaf theorem.
- `msearch.py ... loogle "SheafOfModules, Module.FinitePresentation"`: 0 results.
- `msearch.py ... grep "lisse.*lattice|constructible.*integral"`: 0 results.
- `msearch.py ... leansearch` with “A sheaf over continuous coefficient rings is
  constructible if on a finite stratification it is locally tensor with a finitely
  presented constant module”: service unavailable with an internal server error.
  This is recorded as unavailable, not evidence of absence.
- `msearch.py ... loogle '"IsConstructible", "SheafOfModules"'`: 0 results.
- `msearch.py ... grep
  "IsContinuousConstructible|continuousCoefficientModule|continuousModulePullback"`:
  0 results in Mathlib.
- `tools/blueprint_refs.py search 'continuous constructible module'`: no result.
  DAG text searches found no exact general continuous-coefficient predicate.
- Upstream exact-item-id search: no result. The supplied 51-module framework in the shared checkout's
  `lean/WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean` defines local finite presentation
  of an internal module over a ring sheaf. This permits presentations with matrix
  entries in the coefficient sheaf, whereas the node asks for scalar extension
  of an ordinary finitely presented A-module on a local cover. It is a different
  general predicate and encoding, so is not copied or silently substituted.
- Searches in `lean/Sheaf` found the continuous coefficient sheaves in
  `LatticeSheafLocallyConstant.lean` and constant module sheafification in
  `AdicLisseModule.lean`; both are reused. `IntegralLatticePair` requires global
  finite local freeness, so using it here would strengthen the conclusion.
  The finite-discrete-coefficient and etale inverse-system nodes likewise do not
  supply the requested continuous constructibility definition.

The primary source was checked at https://arxiv.org/pdf/1309.1198:
Definition 6.8.10 supplies the finitely presented ordinary integral module models,
and Lemma 6.8.13 supplies the lattice assertion. The original node's additional
noetherian finite-dimensional and invertibility assumptions are retained exactly.
There is no statement correction or STATEMENT-DISPUTED finding.

Both delivered Lean modules compiled separately through `scompile.py`, in dependency
order, against the live side-library overlay, with no errors or unexpected warnings.
The local source/record checks `stage2_delivery.check_lean_text` also return no
failures for either module, and the new node citations equal its stmt_deps.
The earlier attempt encountered server `OSError: [Errno 28] No space left on device`
while creating compiler-overlay symlinks. On resumption, the existing two modules,
node records, saved search results and source interfaces were reviewed again.
The prescribed `deliver2.py --no-push` wrapper now prints OK: both modules compile
and preflight passes except for the independent second reading, which the wrapper
explicitly reserves for the next worker. No Lean statement, definition or
natural-language node statement required repair. Nothing was pushed. The second
reader supplies the independent reading and performs delivery.

## New nodes

`def-weil-pbc-continuous-constructible-module`, in
`lean/Sheaf/Paper/ContinuousConstructibleModule.lean`, defines the actual constant
coefficient map, ordinary-module scalar extension, canonical coefficient pullback,
ringed module pullback, and finite-stratification local-model predicate. Its source
is Bhatt--Scholze Definitions 6.8.1 and 6.8.10 and their use in Lemma 6.8.13. The
restriction-naturality statement is explicitly part of the node, is the only named
postponed theorem in that module, and has a complete pointwise proof docstring.
The three search kinds and repository/DAG searches are recorded above and in
`mathlib_searches`; no existing notion provides this precise ordinary-finitely-
presented-module local model for continuous coefficients. All existing coefficient,
constant-sheaf, inverse-image, tensor and stratification constructions are reused.
The item gains this node and the landed continuous-coefficient helper node in
`stmt_deps`. No existing dependency node is changed.


## Earlier second reading (a previous round; superseded)

Independent second reading, 2026-10-16. I opened the item node, both delivered
modules, the new definition node, the recorded statement-dependency nodes and
their declaration sources. The item has no `statement_change`. Its mathematical
statement and both Lean signatures are correct and remain unchanged.

Source check: Bhatt--Scholze, arXiv:1309.1198, Section 6.8, pp. 57--61,
Definitions 6.8.1, 6.8.3, 6.8.10, Lemmas 6.8.2 and 6.8.13, and Remark 6.8.15.
The section starts with arbitrary schemes, then restricts constructibility and
the lattice lemma to topologically noetherian schemes. The node explicitly asks
for noetherian, finite-dimensional, ell-invertible schemes and finite E; those
node hypotheses are retained. The paper does not impose separation, a common
rank, or global local freeness of the integral model. Definition 6.8.10 uses
ordinary finitely presented integral modules, rather than arbitrary finite
presentations over the sheaf of continuous functions. Remark 6.8.15 specifies
ringed pullback by inverse image followed by scalar extension. These agree with
the delivered local-model predicate and its canonical coefficient map.

Item inventory and item-by-item Lean match:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Exact; primes 2 and all odd primes are
   included, while 0 and 1 are correctly excluded.
2. Finite field extension E/Q_ell: `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Exact. This does not
   replace a finite-dimensional field extension by a finite-type algebra.
3. Valuation topology, valuation ring A, and the fixed uniformizer convention:
   `WithAbs (Padic.coefficientExtensionAbsoluteValue l E)` and
   `latticeCoefficientIntegers l E`. I read `CoefficientExtensionFinite` and its
   `CoefficientExtension` import: the absolute value is the spectral extension;
   the ring is determined by the absolute-value bound in the DVR theorem.
   `latticeCoefficientIntegers` is its comap along `WithAbs.equiv`. Exact; the
   uniformizer is part of the imported coefficient convention and is not a
   variable in the conclusion, so no uniformizer assumption is needed here.
4. Scheme T: `(T : Scheme.{u})`. Exact arbitrary scheme, including nonreduced
   schemes, with no affine, separated, connected, or nonempty hypothesis.
5. Noetherian in the specified finite-affine-cover sense:
   `[IsLocallyNoetherian T] [CompactSpace T]`. Exact. I read Mathlib's every-affine
   local Noetherian class and its affine-cover equivalences. Quasi-compactness
   extracts a finite subcover from such a cover; conversely a finite noetherian
   affine cover gives these two properties.
6. Finite dimension: `(_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ d)`. Exact.
   The imported definition is the supremum of lengths of chains in
   `IrreducibleCloseds T`, with bottom allowed for the empty space.
7. Ell invertible: `(_hℓ : ∀ x : T, IsUnit (l : T.presheaf.stalk x))`. Exact local
   ring condition, without a stronger global-section unit assumption.
8. Continuous rational and integral coefficient sheaves: `latticeModuleRing T`
   applied to the two coefficient rings above. I read the live
   `LatticeSheafLocallyConstant` source using `scompile.py --source`: sections
   are lifted continuous maps with pointwise operations and restrictions by
   precomposition. `latticeModuleRing` only forgets commutativity. Exact.
9. L an E_T-module sheaf: the explicit `SheafOfModules.{u + 1}` binder. Exact;
   the recorded `ringedSiteModules` declaration is precisely an abbreviation
   for this Mathlib category, rather than a different module encoding.
10. Pro-etale locally free of finite rank: `[L.IsFiniteLocallyFree]`. Exact. I
    read the upstream class in `Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree`:
    it asks for locally free local generators data with finite type on each
    covering member, and explicitly allows different ranks on different members.
11. An integral module sheaf N: the existential
    `∃ N : SheafOfModules.{u + 1} (latticeModuleRing T
    (latticeCoefficientIntegers l E)), ...`. Exact; no finiteness or freeness
    instance on all of N has been added.
12. A finite stratification and finitely presented local integral models:
    `IsContinuousConstructible T (latticeCoefficientIntegers l E) N`. Exact
    after unfolding: one `Scheme.LocallyClosedStratification`, every stratum,
    a `CoversTop` family, then a finitely presented ordinary coefficient module
    P for each member, and an isomorphism on the localized site. Both the cover
    and P can vary. I read the stratification declaration: its scheme immersions
    realize exactly the finite disjoint locally closed partition, with no extra
    reducedness or incidence restriction.
13. The local model A_T tensor_A P: `continuousCoefficientModule`, using the
    imported `adicLisseConstantModules` and `SheafOfModules.changeOfRings` along
    `continuousCoefficientConstantMap`. Exact sheafified tensor of the constant
    module sheaf; P is not replaced by a sheaf with an arbitrary presentation.
14. The rationalization isomorphism: `Nonempty
    (SheafOfModules.changeOfRings (integralLatticeCoefficientMap T l E) N ≅ L)`.
    Exact existential isomorphism along the actual inclusion A into E. Neither
    a mere isomorphism of underlying groups nor an arbitrary scalar map is used.
    The conjunction orders the two properties differently from the prose, but
    both are properties of the same existential N and neither chooses the other.

New-node and construction audit (H4, H5, H12):

`def-weil-pbc-continuous-constructible-module` introduces exactly the missing
continuous-coefficient local-model notion needed by clause 12. Its definition
uses arbitrary topological commutative A, then specializes to the source's O_E.
Its constant map is the actual constant-function ring homomorphism, extended by
the sheafification adjunction. The direct-image section map precomposes with
`pullback.fst V.unop.hom f`, the projection from V times_Y X to V; the inverse-image
coefficient map is its adjoint under the recorded pro-etale adjunction. Module
pullback then uses the recorded module inverse image and scalar extension.
I read that dependency's live source: its `AsSmall` transport retains all small
pro-etale objects and returns to object universe u+1 and morphism universe u.
There is no private replacement site or imposed equality of those universes.
The new naturality theorem states the actual restriction square and postpones
only its proof, with the pointwise pullback-projection proof in its docstring;
its assertion is explicitly present in the new node. Every definition contains
real data. No data is selected from a mere nonunique existence theorem.

The new node has the prescribed definition fields, empty proof lists, exact
cited stmt_deps, the item's chapter/unit and ancestor/via, search records and
none-state audits. All its Lean declarations are listed. There are no dependency
modules in this delivery. The completed-coefficient-datum node supplies context;
the item's explicit C(|V|,A) coefficient sheaf is not replaced by the constant
ring sheaf or by a tower object. No missing tower construction is needed to type
this underived statement.

Independent searches, using different wording from the first worker:

- `msearch.py ... leanfinder` query "A locally free rational pro-etale module
  admits an integral model locally presented by finite generators and relations
  on strata": eight etale-algebra presentation/descent results; no matching
  sheaf theorem or local-model definition.
- `msearch.py ... loogle '"IsLocallyConstant", "Module"'`: two rank-at-stalk
  results on ordinary modules; neither supplies the required sheaf notion.
- `msearch.py ... grep 'stratif.*(tensor|finite.*present)|integral.*structure|
  lattice.*lisse'`: five unrelated polynomial, rational-number and integral
  results in Mathlib.
- Independent `rg` across upstream WeilConjectures, shared lean/Sheaf and DAG
  nodes, with "constructible integral", "integral lattice", "continuous
  constructible", and stratification/tensor/finitely-presented wording. I opened
  `WeilGroup.IsLisse.exists_lattice`: it is a representation-theoretic lattice
  theorem over an algebraic closure with an open-curve restriction, not this
  arbitrary-scheme constructible integral-sheaf theorem. The existing pro-etale
  constructible-sheaf node concerns finite discrete coefficient rings and
  locally constant finite modules. The existing integral derived category
  concerns derived-complete objects. Neither is this underived predicate.
- I read the exact supplied framework file
  `lean/WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean` and
  `coord/pefw-upstream-framework.md`. Its internal-module constructibility asks
  for a locally finite presentation over the ring sheaf, allowing matrices of
  continuous functions. That does not specify scalar extension of an ordinary
  finitely presented A-module on a local cover. Its ring/module encoding and
  predicate therefore do not replace the new definition. Existing continuous
  coefficient, constant-module, pullback and tensor components are reused.

Edge cases: Empty T and a zero-stratum stratification are allowed; `Fin s.n`
requires no positive n. `CoversTop` is its actual covering-sieve condition, so
an empty covering family can occur only where it really covers. Zero modules,
rank zero, torsion finitely presented P, disconnected strata and varying ranks
are allowed. No finite-level n or positive-rank binder is introduced. A nonempty
scheme of characteristic ell is correctly excluded by the local-unit condition;
the empty scheme satisfies it vacuously. Arbitrary scheme size is covered by u;
E and T can be placed in a common larger universe, coefficient sections and
modules are in u+1, and the small-site Hom universe remains u. The cover index
is in the site's object universe, with no independent smaller test universe.
All variables/universes are bound and autoImplicit is disabled.

Mismatches and changes: I found no mathematical mismatch, hollow definition,
missing conclusion or additional hypothesis. I added five non-public imports
for already stated Mathlib proof dependencies, as required by stage 2 rule 7:
`CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`,
`Algebra.Homology.DerivedCategory.KInjective`,
`AlgebraicGeometry.Cover.QuasiCompact`, `Topology.NoetherianSpace`, and
`AlgebraicGeometry.Properties`. The apparent doubled TeX slashes in a tool
rendering were checked on the decoded JSON and are valid single slashes; no node
edit was made. Both node `lean.statement` strings are verbatim substrings of
their file signatures. The seven-step theorem proof and the helper naturality
proof are complete natural-language plans in source/blueprint docstrings; both
Lean theorem proofs remain `sorry`. No statement correction or citer audit is
required.

Verification: `scompile.py Q40 lem-weil-pbc-lisse-e-constructible-integral-lattice`
compiled both sibling modules separately, in dependency order, with no error or
unexpected warning. The main file compiled in 8.7 seconds and the helper in
15.6 seconds in the library confirmation pass, within the prescribed limit.


## Repair of return L, immutable head 537e575661b4

The returned point was `file-only compilation failed: FileNotFoundError(2,
'No such file or directory')`. It contained no missing filename or traceback.
I checked the delivered file inventory against both `lean.file` records: both
module files exist under the sandbox's `lean/Sheaf/Paper/`, and each belongs to
exactly its recorded node. The helper is supplied together with its consumer,
so compilation does not depend on finding an unpublished sibling in the live
library. The item signature still matches `lean.statement` verbatim.

I reran the prescribed `scompile.py Q40
lem-weil-pbc-lisse-e-constructible-integral-lattice` with the absolute paths of
both delivered modules. The current file-only compiler completed successfully:
helper preliminary check 11.4 s, helper sandbox check 9.7 s, helper library check
14.2 s, main sandbox check 8.1 s, and main library check 11.5 s. Every invocation
stayed within 60 seconds, with no errors or warnings. The sibling files were
compiled separately in dependency order. This directly rechecks the operation
that failed in L's independent immutable-head check; it does not establish the
cause of the earlier filesystem exception.

No Lean source change is justified by the returned exception, and no mathematical
statement, dependency interface or proof was changed. This repair adds the
missing current return-specific file-inventory and compilation evidence, then
reruns the full preflight/delivery dry run. No push is authorized in this worker
turn; the independent second reader retains delivery responsibility.

## Second reading by Q40

I independently read the item node, its source place (Bhatt--Scholze, Definition
6.8.1, Definition 6.8.10 and Lemma 6.8.13), the item module, the new
`def-weil-pbc-continuous-constructible-module` node and module, and the recorded
coefficient, site, scheme, sheaf-module, stratification, tensor and finite-presentation
dependencies. The source says that on a topologically noetherian scheme a lisse
finite-extension E-sheaf has a constructible O_E model whose scalar extension is
the original sheaf; the node adds its explicit finite-dimensional and local
ell-invertibility hypotheses and spells out the continuous coefficient sheaves.

The step-1 inventory and verdict are:

- Prime `l`: `(l : ℕ) [Fact l.Prime]`; exact, including all prime l and excluding
  0 and 1.
- Finite extension `E / Q_l`: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`; exact finite-dimensional field extension.
- Valuation topology and valuation ring: `WithAbs (Padic.coefficientExtensionAbsoluteValue
  l E)` and `latticeCoefficientIntegers l E`; these are the canonical imported
  coefficient conventions, with no arbitrary topology or extra uniformizer.
- Scheme `T`: `(T : Scheme.{u})`; no connectedness, separation, reducedness or
  nonempty assumption is added.
- Noetherian hypothesis: `[IsLocallyNoetherian T] [CompactSpace T]`; this is the
  recorded finite affine noetherian-cover formulation.
- Finite dimension: `_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ d`; exact finite
  bound on irreducible-closed chains.
- Invertibility of `l`: `_hℓ : ∀ x : T, IsUnit (l : T.presheaf.stalk x)`; exact
  local-ring condition, with no stronger global unit hypothesis.
- Continuous coefficient sheaves: `latticeModuleRing T (...)`; this is the
  existing continuous-function sheaf with pointwise operations and restrictions
  by precomposition.
- Rational module sheaf: `L : SheafOfModules.{u + 1} (latticeModuleRing T
  (WithAbs ...))`; exact E_T-module object.
- Lisse condition: `[L.IsFiniteLocallyFree]`; exact pro-etale finite local
  freeness, allowing rank zero and varying local ranks.
- Integral model: `∃ N : SheafOfModules.{u + 1}
  (latticeModuleRing T (latticeCoefficientIntegers l E)), ...`; exact A_T-module
  object, with no global finite-local-freeness assumption on N.
- Constructibility: `IsContinuousConstructible T (latticeCoefficientIntegers l E) N`;
  unfolding gives a finite locally closed stratification, a covering family on
  every stratum, an ordinary finitely presented A-module for every cover member,
  and the stated local isomorphism to `A_T ⊗_A P` via the canonical ringed pullback.
- Rationalization: `Nonempty (SheafOfModules.changeOfRings
  (integralLatticeCoefficientMap T l E) N ≅ L)`; exact sheaf tensor scalar
  extension along the canonical inclusion A into E.

The item module renders every clause and introduces no extra assumptions; the
two properties of the same existential N are conjoined in reversed prose order.
The helper module's definitions are real constructions: its
constant map is the constant-function map, its inverse-image coefficient map is
the adjoint of pullback precomposition, and its module pullback is sheaf scalar
extension. The only postponed helper proof is the explicitly named restriction
naturality theorem. The new node's fields meet section 5: its chapter, unit,
ancestor and via agree with the item; its cited identifiers equal stmt_deps;
its searches cover the three required kinds; proof lists are empty and audit
states are none. Its statement explicitly includes the named naturality law.
Every declaration is recorded, and each has its source and blueprint docstring.
There are no dependency modules or statement corrections in this delivery.
The source was checked at https://arxiv.org/html/1309.1198v2, section 6.8;
the earlier report's finite-affine-cover interpretation is independently
confirmed by Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top`.

Edge cases checked: empty T and empty strata are admitted; zero N, zero P and
rank-zero L are admitted; strata may be disconnected and have varying ranks;
no positive dimension or nonempty index is imposed; characteristic ell is
excluded exactly by the stalk-unit hypothesis; E and T may be put in a common
universe enlargement, while coefficient modules use the required `u + 1` lift.

Independent searches used different wording. LeanFinder for a locally free
pro-etale sheaf with a constructible integral model returned only unrelated
etale infrastructure. Loogle for `SheafOfModules IsFiniteLocallyFree
Module.FinitePresentation` returned no match (and reported the identifier as
unknown in that query). A repaired query, `"SheafOfModules", "FinitePresentation"`,
returned twelve local ring-sheaf presentation results, headed by
`SheafOfModules.IsFinitePresentation`; these permit arbitrary coefficient-sheaf
matrices and do not supply the ordinary-A-module local model. The exact
51-module framework's `IsConstructibleModuleObject` was opened as well and
has that same distinction. Grep over Mathlib, `WeilConjectures`, and `lean/Sheaf`
for constructible-integral, continuous-coefficient, and exact theorem names
found no existing declaration; the upstream `WeilGroup.IsLisse.exists_lattice`
and the derived constructible-integral predicates are different notions.

Mismatches: none. No Lean file or node statement required repair. The sandbox
node correctly adds `def-weil-pbc-continuous-constructible-module` and the
landed continuous-coefficient dependency to `stmt_deps`; the item statement and
the file signature remain verbatim aligned. Both sibling modules compile with
the prescribed `scompile.py` wrapper, with only the permitted `sorry` notices.


## Maintainer correction of the helper scope, 2026-10-16

This paragraph supersedes the earlier claims that the current dependency imposes no
constructibility condition on strata. The immutable helper's arbitrary-scheme scope
was too broad for its dependency: `Scheme.LocallyClosedStratification` extends
`Topology.Stratification`, whose current declaration includes
`isConstructible_stratum`. Both local source and `scompile.py --source` confirm this.
The main theorem is unaffected because its noetherian hypotheses make every locally
closed stratum constructible. The new helper node and `IsContinuousConstructible`
now explicitly assume a topologically noetherian scheme, exactly the domain in
Bhatt--Scholze Definition 6.8.10. All coefficient maps and scalar-extension
constructions retain their arbitrary-scheme scope. This is a source-based repair
of the new definition, not an additional hypothesis on the item. No existing
project dependency or target statement is changed.

Complete replacement modules, the new-node record, and the item Lean record
are supplied in fixes/.
The main theorem combines its equivalent locally-noetherian and compact hypotheses
into the existing `IsNoetherian T` class; its record matches that file.
The noetherian-space instance is inferred by `IsNoetherian.noetherianSpace`.
The class `IsNoetherian T` has exactly the original two parent hypotheses, so
this change adds no mathematical condition. The new predicate's
signature and its record agree verbatim. The merge tool refits the main signature
from the complete replacement module. Empty schemes, zero modules, varying
ranks, and nonreduced schemes are still included. All previous clause checks of
the main theorem remain valid. The helper's source-based scope correction is the
only finding and repair in this maintainer review.


Final verification of fixes: `scompile.py Q40
lem-weil-pbc-lisse-e-constructible-integral-lattice
lean/Sheaf/Paper/ContinuousConstructibleModule.lean
lean/Sheaf/Paper/LisseEConstructibleIntegralLattice.lean`, run from this review's
fixes/ directory, returned exit 0 with no errors or warnings. Local side-overlay
checks: helper preliminary 7.9 s, helper sandbox 7.2 s, helper library 7.0 s,
main sandbox 7.3 s, main library 5.9 s. The refreshed proof dependency
LisseLatticeFiniteEtaleDescent compiled in 7.2 s. Every invocation was per-file,
with the wrapper's 60-second limit, nice 19 and two threads. Both replacement
record signatures match their replacement modules exactly. No global build or
repository mutation was performed.
