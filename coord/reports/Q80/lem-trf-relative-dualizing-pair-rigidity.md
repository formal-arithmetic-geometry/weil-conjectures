## Worker report

This delivery states `lem-trf-relative-dualizing-pair-rigidity` in
`Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity`. Its two declarations are
`AlgebraicGeometry.relativeDualizingPair_rigidity` and
`AlgebraicGeometry.relativeDualizingPair_rigidity_on_open`. Both proofs are `sorry`.
It adds the missing supplied-pair predicate and canonical class/scalar maps in
`Sheaf.AlgebraicGeometry.RelativeDualizingPair`, owned by the new definition node
`def-trf-coherent-relative-dualizing-pair`. There is no existence assertion for a
relative dualizing pair and no change to the assigned node's statement.

The source was read in `literature/stacks-project/duality.tex`, Definition
`definition-relative-dualizing-complex` and Lemmas `lemma-relative-dualizing-RHom`
and `lemma-uniqueness-relative-dualizing` (Tags 0E2T, 0E2V, 0E2W), including the
source's explanation that W may be the whole product for a separated morphism.

Clause-by-clause correspondence:

- Schemes and the named morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Separated, flat, locally finitely presented: `[IsSeparated f] [Flat f]
  [LocallyOfFinitePresentation f]`. Only separatedness is required from the
  proper-morphism definition node: there is no properness or quasi-compactness
  hypothesis.
- Locally Noetherian base: `[IsLocallyNoetherian S]`. There is no global
  Noetherian or compactness hypothesis.
- The product Y is the actual categorical `pullback f f`, its first projection
  is `pullback.fst f f`, and its diagonal is `pullback.diagonal f`. Separatedness
  says precisely that this diagonal is a closed immersion.
- The supplied object K belongs to the recorded `schemeDerivedCategory X`.
  `relativeDualizingDiagonalModule f` is the ordinary module direct image of
  `SheafOfModules.unit (moduleRings X.toRingedSpace)` under that actual diagonal.
  `relativeDualizingDiagonalComplex f` places it in degree zero; `DerivedCategory.Q`
  puts it in D(O_Y). This is Δ_*O_X, with no arbitrary object or representative.
- The class binder `ξ : Q.obj (relativeDualizingDiagonalComplex f) ⟶
  (derivedPullback (pullback.fst f f)).obj K` is exactly the stated diagonal class.
- The predicate itself retains the separated/flat/locally-finitely-presented
  binders of its definition node. The first conjunct of
  `IsCoherentRelativeDualizingPair f K ξ` is the recorded
  `Scheme.IsPseudoCoherent X K`, without a perfectness or boundedness substitution.
- Its second conjunct is `∀ x : X, ∃ U : X.Opens, x ∈ U ∧
  Scheme.HasFiniteTorDimensionOver (U.ι ≫ f) ((derivedPullback U.ι).obj K)`.
  The existing Tor predicate forgets scalars to the inverse-image base structure
  sheaf and tests against every module over it. The bounds can depend on U.
  This is locally finite Tor amplitude over S, not finite Tor amplitude over X
  and not a uniform bound on all of X.
- The third conjunct is `IsIso (relativeDualizingClassMap f K ξ)`.
  This map is the canonical tensor-Hom transpose of `μ ≫ ξ`, where μ is
  the actual derived multiplication of Δ_*O_X. Thus it asserts invertibility
  of multiplication by the specified ξ, rather than existence of some
  unspecified isomorphism with the same endpoints.
- The first conclusion is `IsIso (relativeDualizingScalarMap X K)`.
  The scalar map is the canonical transpose of `(λ_ K).hom`; its source is
  the shared derived tensor unit O_X[0] and its target is RHom_X(K,K).
- A second pair is quantified by `(L : schemeDerivedCategory X)`, its class η,
  and `IsCoherentRelativeDualizingPair f L η`. The conclusion is
  `∃! α : K ≅ L, ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = η`.
  The order of composition translates `(Lp₁*α)ξ = η`. This asserts uniqueness
  of the isomorphism itself, not just its existence or its isomorphism class.
- `relativeDualizingPair_rigidity_on_open` repeats both assertions for every
  `U : X.Opens`, with the morphism `U.ι ≫ f` and pairs in D(O_U). The base
  remains S. There is no nonempty or quasi-compact condition on U. It applies
  to any supplied pair on the restriction, in particular the restricted pairs
  from the source's open-restriction observation. The proof docstring explains
  preservation of their defining conditions under open restriction.
- All derived-category size binders are explicit. The universal scheme and
  localized-open `HasDerivedCategory` instances are infrastructure for the
  recorded APIs, not finiteness conditions on schemes. `autoImplicit` is false.

Canonical multiplication and data integrity:

`IsRelativeDualizingDiagonalMultiplication` fixes the ordinary chain map by
its value on every pure tensor in the (0,0) summand, over every open of Y.
`existsUnique_relativeDualizingDiagonalMultiplication` is the one postponed
construction theorem in the definition module. Its statement is part of the
new node's definition and its docstring gives the sectionwise construction,
chain condition, and uniqueness argument. Its unique characterization fixes
the actual map, so taking its witness does not choose undetermined data from
mere existence. Every other helper definition has explicit data.
`relativeDualizingDiagonalMultiplication` uses the existing
`pullbackTensorModelMap` followed by Q of this uniquely determined chain map.
This supplies the non-flat derived-to-ordinary multiplication without pretending
that Δ_*O_X is K-flat. No data definition has a `sorry` body.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separated import:
  `AlgebraicGeometry.IsSeparated`, whose field is diagonal closed immersion.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`. The current source was read through
  `scompile.py --source` because this upstream file is absent in the older local
  source checkout. The dependency's shared module/sheaf and abelian structures
  are retained; `X.Modules` is not used to create another derived category.
- `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent`.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `AlgebraicGeometry.derivedPullback`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: publicly retains
  `CategoryTheory.derivedInternalHom` on the small scheme open site, which is the
  version used by the existing canonical tensor-Hom bijection. No general-site
  universe identification or new internal-Hom functor is introduced.
- `Sheaf.AlgebraicGeometry.FiniteTorDimensionOver`:
  `AlgebraicGeometry.Scheme.HasFiniteTorDimensionOver`.
- `Sheaf.AlgebraicGeometry.DerivedTensorStructure`:
  `AlgebraicGeometry.schemeDerivedTensorMonoidal`.
- `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom`:
  `AlgebraicGeometry.schemeDerivedTensorHomEquiv`, with its representative
  characterization and uniqueness theorem.
- `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison`:
  `AlgebraicGeometry.pullbackTensorTotal`, `pullbackTensorModelMap`.
- Mathlib's `SheafOfModules.pushforward`, `SheafOfModules.unit`, and
  `CochainComplex.singleFunctor` implement the diagonal algebra and its complex.
  `SheafOfModules.tensorObjIsoSheafification` gives the canonical image of a
  pure section tensor; the product is in the actual ring O_X(Δ⁻¹V).

The stated proof dependencies with existing module records are imported privately:
affine pseudo-coherent RHom, internal Hom on opens, affine QCoh derived equivalence,
RHom/global sections, and affine derived pullback/tensor comparisons. The remaining
proof dependencies lack Lean records in the supplied DAG snapshot; their future
uses are recorded in the theorem's seven-step proof docstring. They are not needed
to type the statement and are not restated here.

Edge cases checked before writing: X or U empty; zero complexes; repeated supplied
pair; arbitrary shifts (the diagonal condition is retained and does not accept
arbitrary shifts); disconnected and non-quasi-compact sources; arbitrary base
characteristic; nonregular diagonal/polynomial-presentation kernel. In particular,
there is no assumption that the diagonal algebra is flat or perfect. The
multiplication uses the lax localization comparison even when it is not invertible.
The zero complex only qualifies when its actual diagonal condition holds.
For the empty source all objects/maps involved are zero, and both uniqueness and
scalar invertibility have the expected meaning. No statement fault or dispute found.

Searches for existing declarations:

- `msearch.py leanfinder`: "Unique isomorphism preserving diagonal class between
  relative dualizing complexes for flat morphism of schemes" returned eight
  diagonal/base-change/flatness hits, no coherent-duality rigidity or pair definition.
- `msearch.py loogle`: `DerivedCategory, CategoryTheory.Iso` returned twelve
  ordinary derived-category comparison declarations, no supplied-pair theorem.
- `msearch.py leansearch`: "Relative dualizing pair on a flat morphism of schemes
  finite tor amplitude diagonal class" returned eight flatness declarations,
  not the pair predicate or diagonal class multiplication.
- `msearch.py grep`: `relativeDualizing|RelativeDualizing|homothety` in
  AlgebraicGeometry returned zero hits; the unrestricted homothety search found
  only Euclidean geometry uses.
- `rg` in the upstream project and `lean/Sheaf` for `relativeDualizing`,
  `RelativeDualizing`, `relative_dualizing`, `DualizingPair`, and `dualizingPair`
  found no coherent supplied-pair interface. The broad Tor search did find the
  reused Tor-dimension predicate, and the tensor/Hom searches found the reused
  canonical total tensor and tensor-Hom APIs.
- DAG phrase search and `tools/blueprint_refs.py search 'relative dualizing'`
  found inline consumers and distinct etale dualizing objects. There is no
  existing definition node for this coherent pair. The upstream ID search also
  found no existing declaration for the assigned theorem.

Validation: every delivered Lean module is checked separately with `scompile.py`,
in dependency order. The delivery dry run runs the server preflight and compilation.
The first compiler run exposed only helper elaboration errors (the total-tensor
instance, explicit pure-tensor universes, ordinary section-ring multiplication,
ExistsUnique witness extraction, and a product-scheme type annotation); these are
repaired using the existing tensor model and explicit types, with no statement change.

## New nodes

`def-trf-coherent-relative-dualizing-pair` defines the supplied-pair predicate of
Stacks Tag 0E2T in the separated case W = X ×_S X, together with its diagonal
algebra, uniquely characterized multiplication, canonical derived class map,
and the scalar map appearing in Tag 0E2V. The new node cites the existing
pseudo-coherence, finite relative Tor dimension, derived pullback, derived
tensor, tensor-Hom, module, complex, and fibre-product notions. The searches
above rule out an existing coherent-pair node or declaration; etale dualizing
objects and the smooth proper right-adjoint object have different data and
are not substitutes. This node is attached below the item's existing
`lem-trf-local-term-locality` ancestor and retains its unit and ancestry.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
