## Worker report

The module `Sheaf.Paper.CoefficientHeartClosure` states the single theorem
`AlgebraicGeometry.ProEtale.coefficientHeart_closure`, with `sorry` as its proof.
It introduces no definition and changes no natural-language statement. Its docstring
records all eight proof steps of the node, including finite-E cokernels, finite-stage
Qbar_l descent, the evaluation proof for kernels, and globalization.

The statement follows the current main-20261015 blueprint file
`sec-six-functors-basics/sk-lem-coefficient-heart/sk-lem-coefficient-heart-closure.md`.
The resolved stage-1 repair note was read: its requirement to preserve the statement
is respected, and its revised eight-step proof is carried into the theorem docstring.

In the table below, `RΛ` denotes the literal term
`(sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ`.
This is only a report abbreviation: the Lean signature writes the term out every time.

Each hypothesis and clause is rendered as follows:

| Node | Lean |
| --- | --- |
| Fixed prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]`; no assumption about its invertibility on the schemes |
| Lambda is E, a finite extension of Q_l in the fixed algebraic closure, or Qbar_l | `hΛ`, the disjunction of an existential `IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)` with `FiniteDimensional ℚ_[ℓ] E` and equality to `Profinite.padicSubfieldCondensedRing ℓ E`, or equality to `Profinite.padicAlgClCondensedRing ℓ` |
| Commutative coefficient ring | `Λ` is a condensed `RingCat` sheaf and its underlying ring object has `[IsCommMonObj RΛ]`, the existing coefficient interface |
| S topologically Noetherian | `∀ (S : Scheme.{u}) [TopologicalSpace.NoetherianSpace S]` in the first conjunct; algebraic Noetherianity is not required here |
| Extension of lisse end terms is lisse | `ObjectProperty.IsClosedUnderExtensions (IsLisseCoefficientModule ... (X := S))`; this existing Mathlib class quantifies over every short complex with `ShortExact`, with the property required only for its first and third objects |
| Kernel of any morphism between lisse modules is lisse | `ObjectProperty.IsClosedUnderKernels (IsLisseCoefficientModule ... (X := S))`; the class quantifies over all kernel forks with the universal property, for maps whose source and target have the property |
| Cokernel of the same sort of morphism is lisse | `ObjectProperty.IsClosedUnderCokernels` for that same predicate, using all universal cokernel coforks |
| X Noetherian | `∀ (X : Scheme.{u}) [IsNoetherian X]` in the second conjunct, separately from the local topological assumption |
| Cons closed under kernels, cokernels, extensions in the ambient module category | Three corresponding Mathlib closure classes for `IsConstantModelConstructible RΛ X`; their ambient category is the actual `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj ... X)` |
| Cons is abelian | `Nonempty (Abelian (ConstantModelConstructible ... X))`, for the already defined full subcategory with its inherited morphisms and preadditive structure |
| The inclusion is exact | `PreservesFiniteLimits (ObjectProperty.ι ...)` and `PreservesFiniteColimits (ObjectProperty.ι ...)`; for this additive inclusion of abelian categories these are its left and right exactness |
| Constructible iff lisse on each stratum of a finite stratification | The final `∀ M, IsConstantModelConstructible ... M ↔ ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n, IsLisseCoefficientModule ... ((CondensedRing.upperStar ... (R.immersion a)).obj M)` |

The closure classes are not stronger assertions that all subsheaves or quotients of
lisse objects are lisse: they require both source and target of the morphism to be
lisse. Likewise the extension class only assumes lisseness of the two end terms.
For the global clause the same distinction applies to constructibility.

Dependency declarations used publicly:

- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and
  `AlgebraicGeometry.ProEtale.ConstantModelConstructible`. The former uses the finite
  constant scalar-model convention, with an affine-local condition on general schemes.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `AlgebraicGeometry.ProEtale.finiteConstantLocalModel_iff_exists_cover`, whose full
  signature and docstring were read. Its canonical scalar-extension functor and
  same-cover matrix characterization were also read. The field/local-free argument
  belongs to the proof; no extra field assumption is added to the statement.
- `Sheaf.Paper.CoefficientHeartCommonStratification`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`
  and the existing `Scheme.FiniteLocallyClosedStratification` imported there. The lisse predicate means
  free of some finite rank on each member of a pro-etale cover: upstream `Mod.IsFree`
  explicitly means isomorphic to `Mod.finiteFree R n` for some natural n.
  The definition node `def-sfb-lisse-coefficient-module` owns this predicate through
  its exact `existing: true` binding to this module. That definition node is cited in
  `stmt_deps`; the common-stratification theorem is used only by proof step 8 and
  remains only a proof dependency.
- `Mathlib.CategoryTheory.ObjectProperty.Extensions` and
  `Mathlib.CategoryTheory.ObjectProperty.Kernels`: their existing closure classes,
  with their complete definitions read before use.
- `sk-def-sfb-condensed-ring` (recorded module
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`, publicly imported):
  the underlying ring object is written explicitly as
  `RΛ`, using Mathlib's `CategoryTheory.sheafCompose` and the forgetful functor
  `forget₂ RingCat Ab`. This expands the existing helper definition exactly and
  avoids using a theorem-node-owned helper in the statement dependency interface.
- Existing coefficient ring definitions from
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. Qbar_l means
  finite-subextension-valued sections, as required by the source; it does not mean
  every valuation-continuous function into the algebraic closure.

The module also imports the recorded modules of all stated proof dependencies,
including the Mathlib epi/local-surjectivity and enough-injectives matches. Closed
upstream audit records are used for cartesian coefficients, module cokernels and
change of scalars, and `CategoryTheory.Mod.instAbelian` is imported from its owning
upstream module. The missing local checkout of
`Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization` was read with
`scompile.py --source`; the published module has the recorded canonical comparison.
No dependency interface is replaced and no new node is needed.

Edge cases checked before writing:

- Empty schemes and zero modules are admitted by every quantifier. Neither scheme
  has a `Nonempty` binder, and finite-free rank zero is admitted by `Mod.IsFree`.
- Covers have no fixed rank and no imposed uniform positive rank; on disconnected
  schemes ranks may vary between covering members.
- Short exactness includes injectivity and surjectivity at the ends, via
  `ShortComplex.ShortExact` in the extension closure class.
- The stratification has `n : ℕ` and `Fin n` strata: an empty stratification is
  allowed for an empty scheme. Scheme structures may be nonreduced; there is no
  reducedness or factorization assumption.
- The local assertion only requires Noetherian underlying topology, and the global
  assertion uses algebraic Noetherianity exactly as written in the node.
- No restriction on the characteristic, no base field, separatedness, finite type,
  or invertibility of ell was introduced.
- All universe variables and object variables are explicit. The scheme/site and
  coefficient sizes follow the recorded `Scheme.{u}` / `Ab.{u+1}` interfaces, without
  equating the site's object and morphism universes. There is no `let` in the signature.

Searches for an existing statement (all before writing):

- `msearch.py`, LeanFinder: "Lisse pro-etale finite extension Q_l coefficient sheaves
  kernels cokernels extensions form an abelian exact constructible subcategory".
  Eight hits, including `Scheme.Modules.instAbelian`, condensed-module abelianness
  and unrelated exactness results; none is this coefficient-specific theorem.
- `msearch.py`, Loogle: `CategoryTheory.ObjectProperty.IsClosedUnderKernels`.
  Twelve hits provide the reusable closure predicate and generic full-subcategory
  abelianness machinery; none supplies the lisse closure result.
- `msearch.py`, grep, Mathlib/CategoryTheory:
  `IsClosedUnderKernels|IsClosedUnderCokernels|IsClosedUnderExtensions`.
  Sixteen hits give precisely the generic predicates used in the signature.
- `msearch.py`, LeanSearch: "Lisse sheaves for condensed finite extensions of p-adic
  fields or bounded algebraic closure coefficients are closed under kernels
  cokernels extensions on topologically Noetherian schemes". Eight hits concern
  generic condensed limits and abelian categories, not the required closure theorem.
- `rg`, upstream WeilConjectures, side framework and `dag/lean_names_upstream.json`:
  `coefficientHeart_closure|CoefficientHeartClosure|IsLisseCoefficientModule|lisse.*(kernel|cokernel|extension)`.
  No exact theorem exists. The older adic modules have an extension lemma for their
  separate `AdicSheaf` encoding and only generic-open or stratified kernel/cokernel
  assertions; they do not state this two-coefficient whole-stratum theorem.
- `rg`, upstream WeilConjectures: `det-lem-coefficient-heart-closure`: no occurrence.
- `rg`, lean/Sheaf: `coefficientHeart|lisse.*(kernel|cokernel|extension)|IsLisseCoefficientModule`.
  Found the shared lisse predicate in the common-stratification module, the already
  recorded constructibility and finite-descent modules, and the larger coefficient
  heart theorem. The larger heart theorem has finite-type separated hypotheses over
  a field of characteristic different from ell, and omits the local topologically
  Noetherian-scheme closure assertion; it is not this node's statement.

No statement dispute, correction, hollow definition or missing dependency was found.

Validation: the prescribed `scompile.py Q17 det-lem-coefficient-heart-closure`
invocation compiled the delivered file cleanly (exit 0), both the sandbox probe and
the actual `Sheaf.Paper.CoefficientHeartClosure` module. No compiler warning or error
was emitted. Only the named theorem has a postponed proof. A local record comparison
confirmed that the source statement is unchanged, the only node deltas are `lean`
and the added landed definition nodes in `stmt_deps`, and `lean.statement` is the exact
multiline signature in the source file.


## Return repair

The return at immutable head `828f253fc4c7` identified delivery-errors H2/H12:
`det-lem-coefficient-heart-common-stratification` was added to `stmt_deps` although
its theorem conclusion is used only in the proof. The retained packet first passed
an automated dry run (`fd63ec9ed9`), which does not resolve this semantic ownership
issue. The repair replaces that added statement dependency with the existing
`def-sfb-lisse-coefficient-module` and also cites `sk-def-sfb-condensed-ring`.
Every occurrence of `coefficientHeartRingObj Λ` in the signature is expanded to its
literal defining `sheafCompose` expression. The original helper's full definition
and the lisse definition's full signature, body and docstring were read in
`Sheaf.Paper.CoefficientHeartCommonStratification`; its theorem is still a proof
dependency. No new module, definition, theorem, natural-language statement change
or dependency repair is introduced. The `lean.statement` record is refreshed
verbatim from the expanded signature.

## Second reading by Q17

Self-check of the repaired node and module (the dispatcher forbids starting another
agent): the only mathematical-text change is expansion of a definitional abbreviation.
The prime, the finite-subfield-or-algebraic-closure disjunction, and the commutative
ring-object binder retain their types. The first conjunct still quantifies over all
topologically Noetherian schemes and asserts extension, kernel and cokernel closure
for lisse modules. The second still quantifies over all Noetherian schemes and
asserts kernel, cokernel and extension closure for constructible modules, abelianness
of their full subcategory, finite-limit and finite-colimit preservation by its
inclusion, and the equivalence with lisseness on every stratum of some finite
stratification. Every module category and restriction functor uses the same expanded
coefficient term. Rank zero, the empty scheme and the empty stratification remain
allowed. The dependency-node metadata, rather than the physical module name, now
identifies the definition that supplies the lisse predicate. No mismatch remains.

Repair validation: the final module, including the public import of the condensed-ring
definition node's recorded module, compiled through the prescribed `scompile.py`
with exit 0 and no diagnostics (sandbox 2.6 s, library 2.8 s). The self-check confirmed
that only `lean` and the two added landed definition dependencies differ from the
current shared base, `lean.statement` is verbatim, all Lean lines fit 100 characters,
the abbreviation no longer occurs in the module, and the theorem's sole proof is
`sorry`. Common stratification remains in `proof_deps` and is absent from `stmt_deps`.
