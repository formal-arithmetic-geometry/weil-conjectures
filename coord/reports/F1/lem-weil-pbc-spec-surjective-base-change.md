## Worker report

The module `Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange` states
`AlgebraicGeometry.Spec.map_surjective_baseChange`, with only `sorry` as proof.
No new notion, dependency module, or statement correction is needed.

Hypothesis and clause correspondence:
- Commutative rings R, S, R': `{R S R' : Type u}` and the three `CommRing` instances.
  They live in a common arbitrary universe, as Mathlib's scheme spectrum functor
  requires; any three rings can be considered in a common universe. No finiteness,
  nontriviality, field, flatness or integrality assumption is imposed.
- Ring map R → S: `[Algebra R S]` and `algebraMap R S`. Specifying an algebra
  structure on commutative rings specifies precisely a unital ring homomorphism.
- Its spectrum map is surjective: `h : Function.Surjective
  (Spec.map (CommRingCat.ofHom (algebraMap R S))).base`.
- Every base ring map R → R': the arbitrary instance `[Algebra R R']`.
- Base-changed ring R' ⊗_R S: `R' ⊗[R] S` is Mathlib's algebra tensor product.
- Base-change map r' ↦ r' ⊗ 1: `Algebra.TensorProduct.includeLeftRingHom`,
  explicitly typed `R' →+* R' ⊗[R] S`; its source definition and docstring were read.
- Surjectivity of Spec(R' ⊗_R S) → Spec R': `Function.Surjective` of the `.base`
  of `Spec.map` on precisely that ring map. `.base` is the underlying continuous
  map, so surjectivity here is surjectivity on points, not on rings or sections.

Dependency declarations used: def-weil-affine-spectrum records
`AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, in
`Mathlib.AlgebraicGeometry.Scheme`, imported directly. Their definitions and
full signatures/docstrings were read at lines 469–480. `Spec.topObj` in
`Mathlib.AlgebraicGeometry.Spec` identifies the underlying space with
`PrimeSpectrum`; `Spec.map_base` and `Spec.map_apply` in Scheme.lean confirm
that the map used is contraction of prime ideals. The canonical tensor map is
`Algebra.TensorProduct.includeLeftRingHom` in
`Mathlib.RingTheory.TensorProduct.Basic` (line 273).

Edge cases checked before writing: the zero ring R forces its unital algebras
S and R' to be zero, and all the spectra in question are empty. A zero ring R'
gives an empty target and a zero tensor product, so the conclusion holds.
When S is zero and R is nonzero, the surjectivity hypothesis fails. Identity
base change recovers the original surjection. Non-flat surjective-on-spectra
maps are included: no faithful-flatness hypothesis is used. Tensor order is
R' on the left, so the displayed map is exactly the node's map.

Searches made (2026-10-11):
- msearch.py leanfinder, query "surjective map on prime spectra remains
  surjective after tensor product base change": returned surjectivity on stalks,
  RingHom.surjective_isStableUnderBaseChange, finite-type base-change results,
  and faithfully flat spectrum results; none states this general claim.
- msearch.py loogle, query "PrimeSpectrum.comap, Algebra.TensorProduct.includeLeft":
  zero hits.
- msearch.py leansearch, query "surjective map on prime spectra is stable under
  tensor product base change": unavailable, Internal Server Error.
- msearch.py grep, query "comap_surjective|surjective_comap|surjective.*baseChange"
  in RingTheory: 25 hits, chiefly integral and faithfully-flat special cases;
  none states the claim for arbitrary spectrum-surjective ring maps.
- rg of the same spectrum/surjectivity names in WeilConjectures and lean/Sheaf:
  generic irreducibility, field-extension, integral and other special cases;
  no exact statement. grep of the item's id in WeilConjectures: no hits.
- rg "map_surjective_baseChange" in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collision.

Source checked: the local Stacks algebra.tex is not present on this machine;
opened https://stacks.math.columbia.edu/tag/00FI. Its final assertion says exactly
that surjectivity persists along any R → R'. The four-step proof in the module
follows the node's proof, naming the fibre criterion, residue-field construction,
tensor cancellation and the linear-retraction nonvanishing argument.
No STATEMENT-DISPUTED or node fault was found.

## Second reading by F1

Read independently against the sandbox node and module, the recorded dependency
node def-weil-affine-spectrum, and the actual Mathlib definitions. The local
Stacks .tex checkout is absent. I read the raw upstream algebra.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including section-conventions and lemma-surjective-spec-radical-ideal, and
checked https://stacks.math.columbia.edu/tag/00FI. The conventions explicitly
include commutative unital rings and the zero ring; the final assertion of 00FI
allows every ring map R → R'. No ambient Noetherian, field, flatness, injectivity,
or finiteness hypothesis is present. The node extracts the surjectivity clause
of that assertion, exactly as its proof does.

Objects, hypotheses, and conclusion, in the node's order:
1. Commutative rings R and S: `{R S R' : Type u}` with `[CommRing R]`
   and `[CommRing S]`. Verdict: exact, including zero rings.
2. A ring homomorphism R → S: `[Algebra R S]` with `algebraMap R S`.
   Verdict: exact. A unital map between commutative rings gives an Algebra
   structure by RingHom.toAlgebra, so this does not require an additional
   mathematical hypothesis or a special kind of ring map.
3. The induced spectrum map: `Spec.map (CommRingCat.ofHom (algebraMap R S))`.
   Verdict: exact. The dependency's recorded `AlgebraicGeometry.Spec` and
   `AlgebraicGeometry.Spec.map` in Mathlib.AlgebraicGeometry.Scheme are used
   directly. Their definitions at lines 470 and 479 construct the affine
   scheme and the contravariant morphism. `Spec_carrier`, `Spec.map_base`, and
   `Spec.map_apply` at lines 533–538 identify its points with prime ideals and
   its underlying map with contraction. This is the dependency's notion,
   not a private spectrum or an unrelated morphism.
4. Surjectivity of Spec S → Spec R: the binder `h : Function.Surjective
   (Spec.map (CommRingCat.ofHom (algebraMap R S))).base`.
   Verdict: exact surjectivity on points, not surjectivity of the ring map.
5. Every commutative ring R' and every map R → R': `[CommRing R']`
   and the arbitrary `[Algebra R R']`.
   Verdict: exact universal quantification. These binders preceding `h` merely
   commute universal choices with an implication whose hypothesis does not
   mention R'; no existential choice or restricted class of base maps occurs.
6. Base-changed ring R' ⊗_R S: `R' ⊗[R] S` with Mathlib's tensor-product
   commutative ring structure. Verdict: exact, in the node's tensor order.
7. The canonical map r' ↦ r' ⊗ 1: explicitly typed
   `(Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] S)`.
   Verdict: exact; Basic.lean:273 defines precisely this unital ring map.
8. Conclusion Spec(R' ⊗_R S) → Spec R' is surjective: `Function.Surjective`
   of the `.base` of `Spec.map` on the map in item 7.
   Verdict: exact, all points quantified; no missing or added conjunct.

Edge cases: if R is zero, its unital algebras S and R' are zero and all
spectra are empty. If R' is zero the target spectrum is empty and the tensor
ring is zero. If S is zero and R nonzero, `h` cannot hold because the target
spectrum is nonempty. Identity base change and nonflat base maps are included;
no extra instance excludes them. There is no index set or integer n, so the
empty-index and n = 0 checks are inapplicable. No characteristic is specified,
so all characteristics are allowed. The common universe `u` is arbitrary;
any finite collection of ring carriers in different universes lives in their
common maximum universe. This is not a test-object quantifier in an independent
smaller universe, and creates no vacuous hypothesis. All variables and the
universe are visibly bound.

Independent searches (2026-10-11):
- msearch leanfinder: "A surjection of affine scheme points remains surjective
  after extension of scalars". Eight hits: affine-space projection,
  pointsPi, target image ring map, SurjectiveOnStalks.iff_of_isAffine,
  Spec.map_surjective, and underlying-map surjectivity declarations.
  Spec.map_surjective concerns the function from ring maps to scheme morphisms,
  not the surjectivity of a particular map on points. No exact match.
- msearch loogle: "PrimeSpectrum.comap, Function.Surjective". Twelve hits,
  including integral and faithfully flat surjectivity, IsLocalHom, and
  embeddings induced by surjective ring maps. None states arbitrary
  spectrum-surjective base change.
- msearch leansearch: "For any homomorphism A to B inducing a surjection on
  prime ideals, extending scalars preserves surjection on prime spectra".
  Service unavailable (Internal Server Error); no verdict claimed for it.
- Independent rg on Mathlib RingTheory and AlgebraicGeometry, all upstream
  WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json:
  `surjective.*[bB]ase[Cc]hange|[bB]ase[Cc]hange.*surjective|comap_surjective|
  surjective_comap|map_surjective_baseChange`.
  Opened the close upstream declarations in GenericIrreducibility.lean:
  comap_surjective_map_tensor_of_ker assumes a surjective algebra map and a
  particular nilpotent kernel condition; comap_surjective_map_tensor_of_field
  is a field-extension special case. Neither states this node.
  Opened RingHom.surjective_isStableUnderBaseChange: its predicate is
  surjectivity on ring elements, not prime spectra. Opened the Surjective
  base-change instance in PullbackCarrier.lean: it concerns scheme pullback
  projections and needs the affine tensor/pullback identification to obtain
  this statement. Thus it is a proof ingredient, not an existing declaration
  of this exact ring-tensor statement. No exact match or name collision found.
  Searching the item's id upstream gives no hit; the project's
  LocalCompleteIntersectionFieldChange only cites it in its proof docstring.

H5/H6/H8/H9: no definitions or local instances occur, hence no hollow or
private notion; the sole theorem has exactly `by sorry`. Both docstrings name
00FI and the blueprint id. Its four proof paragraphs match all four node
steps: fibre criterion, compatible residue-field inclusion, two tensor
cancellations with symmetry, and the basis/linear-retraction nonvanishing
argument. Each non-elementary dependency is named. Imports serve the spectrum
and tensor map used in the signature. Namespace and topic are appropriate,
lines meet the 100-character bound, and no hidden `let` or auto-implicit binder
occurs. There are no new nodes, dependency modules, or statement corrections
to review, and consequently no correction-citer verdicts are needed.

Mismatches found: none. Kept the Lean module and node unchanged; appended this
second reading only. The node's lean.statement is verbatim the file's signature
through the result type, before `:=`. Server single-file compilation with the
required scompile.py command succeeded in 1.6 seconds (exit 0), with no warnings.
