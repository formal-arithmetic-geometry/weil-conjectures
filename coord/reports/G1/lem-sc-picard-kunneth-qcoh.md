## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.PicardKunnethQcoh`, declaration
`AlgebraicGeometry.Scheme.Modules.picard_kunneth_qcoh`. Its proof is `sorry`.
The added operations module supplies the canonical map that the original statement
needs; it does not assume an arbitrary cup pairing or an arbitrary cohomology theory.
No statement correction and no dependency replacement is made.

Hypotheses and clauses, matched individually:

- The field is `(k : Type u) [Field k]`.
- The schemes are `(X Y : Scheme.{u})`; `f` and `g` are their structure morphisms to
  `Spec (CommRingCat.of k)`. Explicit morphisms are used because this statement forms
  their fibre product and its induced morphisms.
- `F : X.Modules`, `G : Y.Modules` are modules over the respective structure sheaves.
  `[F.IsQuasicoherent]` and `[G.IsQuasicoherent]` are precisely quasi-coherence,
  not coherence or finite generation.
- Quasi-compactness is `[CompactSpace X] [CompactSpace Y]`, topological compactness
  without any Hausdorff condition.
- Affine diagonals are `[IsAffineHom (pullback.diagonal f)]` and the same for `g`.
  Over the affine base Spec(k), this is equivalent to the absolute affine-diagonal
  condition: intersections of affine opens are affine. No separatedness is assumed.
- `∀ n : ℕ` includes every integer degree at least zero.
- The product is `pullback f g` and its projections are `pullback.fst` and `pullback.snd`.
- `externalCupCoefficients f g F G` is literally the tensor product of the two objects
  of `tensorPullback` along these projections; the tensor is over the product's
  structure sheaf.
- `scalarCohomology` restricts scalars on the recorded `RingedSpace.moduleCohomology`;
  it is not the abelian-sheaf `Modules.H` encoding.
- The direct sum is indexed by `{pq : ℕ × ℕ // pq.1 + pq.2 = n}`; each summand is the
  tensor over `k` of the two indicated cohomology modules.
- `∃ e : ... ≃ₗ[k] ...` says that the map is an isomorphism. Its direction is from
  the direct sum to product cohomology, the actual direction of the source's cup map.
  The displayed isomorphism in the node is an unoriented identification; reversing
  that display does not change the assertion.
- The generator equation for `DirectSum.lof` pins every value of `e` to `externalCup`.
  Pure tensors generate each tensor product, and summand inclusions generate the
  direct sum, so this specifies the canonical linear map uniquely.
- `externalCup` pulls both classes back by the canonical projection maps and applies
  `scalarCohomologyCup`; it is not an unspecified linear equivalence.
- The second conjunct quantifies over arbitrary morphisms `u`, `v` over k and their
  induced product morphism `w`. Its two projection equations uniquely specify w.
  It asserts equality after the canonical external-tensor coefficient identification
  `externalCupPullbackIso`. The left side is pullback of the external cup; the right
  side is the external cup of the pulled-back classes. This is functoriality on pure
  generators and therefore of the whole canonical direct-sum map. The source schemes
  X', Y' need not be quasi-compact or have affine diagonal for this identity.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, lines 169–180 (full class docstring and signature).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, lines 36–48, and
  `Scheme.Hom`, lines 72 onward (schemes and morphisms).
- `Sheaf.AlgebraicGeometry.Coherent`: its module docstring identifies quasi-coherence
  with Mathlib `SheafOfModules.IsQuasicoherent`; the recorded `RingedSpace.IsCoherent`
  is deliberately not imposed, since the item only asks quasi-coherence.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`,
  `snd`, `lift` (lines 95–140) and `map` (lines 270–278), with the scheme pullbacks instance.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`, its full
  tensor-formula object and map definitions, lines 22–121.
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`: `exists_tensorPullbackAdjunction`,
  including its unit formula; the normalized choice is used for cohomology pullback.
- `Sheaf.Topology.RingedSpaceModuleCohomology`: `globalSectionsFunctor`,
  `moduleCohomology`, `globalSectionsComplex`, their full docstrings and signatures.
- `Sheaf.AlgebraicGeometry.ModulePullbackTensor`: `module_pullback_tensor`, including
  the tensor-section normalization, for the canonical external coefficient comparison.

Edge cases checked: empty schemes are allowed (no `Nonempty` or connectedness hypothesis);
zero modules are allowed; degree zero gives the ordinary tensor of pulled-back sections;
all characteristics are allowed (no characteristic hypothesis); arbitrary non-finite
cohomology vector spaces are allowed; every bidegree includes zero. No finite-dimensional
or properness assumption occurs. The common universe u can contain the field, schemes,
and their module values; the tensor and direct sum remain in that universe. The auxiliary
Ext computations use u+1 for k-sheaves but transport back to the original u-small derived
cohomology objects; no independent small test universe is introduced.

Searches performed:

- msearch leansearch, `Kunneth isomorphism quasi coherent module cohomology schemes over
  a field`: unavailable, HTTP Internal Server Error (not a negative search result).
- msearch leanfinder, same query: ordinary sheaf cohomology, group cohomology, and sheaf
  category instances; no quasi-coherent Kunneth isomorphism.
- msearch loogle, `AlgebraicGeometry.Scheme, "kunneth"`: zero hits.
- msearch grep, `kunneth|cupProduct`, Mathlib/AlgebraicGeometry: zero hits.
- rg of WeilConjectures and lean/Sheaf for Kunneth/cup/cohomologyPullback: the source
  has etale six-functor Kunneth statements, which have different coefficients and
  hypotheses; the landed Picard degree-one slice lemma cites this item but does not
  state it. The structure-sheaf-only pullback module uses abelian-sheaf Ext and cannot
  supply general module cohomology and cup product.
- Plain grep for this node id in WeilConjectures: no hit.
- `dag/lean_names_upstream.json` contains the six-functor Kunneth name, not this theorem.

The local literature checkout contains only lists, so the source was read directly at
https://stacks.math.columbia.edu/tag/0BED (statement and full proof, including its map
construction). The theorem docstring carries the eight proof steps of the DAG node.

## New nodes

`def-sc-field-linear-module-cohomology-operations` defines the field-linear enhancement
of the recorded O-module cohomology and its canonical pullback, cup and external cup
operations, needed before the item can name its map. The new module is
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`.
The underlying cohomology remains `RingedSpace.moduleCohomology`; the enhancement is
restriction of scalars, not a second cohomology theory. Scalar sheaves have exactly the
original sections with scalars restricted along k → O_X(U). Pullback is constructed by
exact inverse image and the tensor-pullback unit. Cup is constructed by exact tensor
functors and Yoneda composition in k-sheaves, followed by the canonical coefficient map.
Composition comparisons use uniqueness of left adjoints with the normalized adjunctions.
The external coefficient isomorphism uses the existing tensor-pullback tensor theorem.
Every postponed proof needed by these definitions is a named theorem with `sorry` and
its own source/proof docstring; no definition's data is `sorry`.

Source: Tag 0BED, maps before equation-kunneth-on-cech, with the cohomology/cup construction
of Tags 01DZ and 01F7. Existing node searches used `blueprint_refs.py search 'cup product'`,
`search 'cohomology pullback'`, and `search 'field-linear'`, and rg on dag/nodes. The
blueprint cup nodes are etale/derived or supported versions, not these O-module operations;
there is no matching field-linear operation package. Its blueprint ancestor is
`thm-sc-theorem-of-cube`, at the invocation of Kunneth on the special fibre.

msearch leansearch for `field linear cohomology pullback cup product module sheaves ringed
space` was unavailable (Internal Server Error). Leanfinder for the same query found
ordinary module pullback and pullback-free-module lemmas, not the cohomology operations.
msearch grep for `scalarCohomology|scalarSheaf|scalarExtMap|moduleExtEquiv` found no
Mathlib match; the same rg in WeilConjectures and lean/Sheaf found none. Actual queries
and results are in searches.jsonl. The node records these searches with the service
failure distinguished from no match. No dependency modules were needed.

## Earlier second reading (a previous round; superseded)

I read the node statement, Tag 0BED (Varieties, `lemma-kunneth`), both delivery modules,
and every declaration named by the new operations package. The item renders the node as
follows, clause by clause:

- `k : Type w` with `[Field k]` is the base field.
- `X Y : Scheme.{w}` with explicit `f : X ⟶ Spec (CommRingCat.of k)` and
  `g : Y ⟶ Spec (CommRingCat.of k)` are the two schemes over the field.
- `[CompactSpace X] [CompactSpace Y]` gives quasi-compactness, and affine diagonal
  instances are stated for both structure morphisms.
- `F : X.Modules`, `G : Y.Modules` with `IsQuasicoherent` instances are precisely the
  two quasi-coherent modules.
- For each `n : ℕ`, the subtype `pq.1 + pq.2 = n` indexes the direct sum of the two
  scalar-restricted module cohomologies. The existential linear equivalence has direction
  from that direct sum to product cohomology, and the `DirectSum.lof` equation identifies
  each pure tensor with `externalCup`, including the required degree cast.
- The final conjunct quantifies morphisms `u`, `v` over `k` via `hu`, `hv`, an induced
  product morphism `w`, and its two projection equations. Its equality is exactly the
  pullback naturality equation after `externalCupPullbackIso`, for all degrees and pure
  classes.

The Lean hypotheses add no finiteness, separatedness, connectedness, characteristic,
nonzero, or finite-dimensional assumptions. The explicit structure maps are permitted by
the project convention for fibre products. The universal quantifier over `n : ℕ` covers
all nonnegative degrees in the source. The empty scheme, zero module, degree zero, and
all characteristics remain admissible; the direct-sum subtype and pure-generator clause
also behave correctly in these cases. All scheme, index, and coefficient universes are
the single universe `w`, so no independent vacuous universe is introduced.

I searched Mathlib and the project with LeanFinder, Loogle, grep/rg, and the upstream-name
index for Kunneth, cup-product, and field-linear module-cohomology declarations. The
searches found no existing theorem or operation package; the unavailable LeanSearch query
is recorded as unavailable rather than a negative result. The new definition node and its
module were therefore required and were read against Tag 0BED and Tags 01DZ/01F7.

No mismatch was found between the node and `picard_kunneth_qcoh`; no statement correction,
dependency replacement, or edge-case restriction was needed. The operations module uses
the recorded `RingedSpace.moduleCohomology`, scalar restriction, tensor-pullback, and
named postponed proofs; no definition contains `sorry` as data. Both modules compile
together successfully with `scompile.py` (exit code 0).

Repair H10: the scalar cohomology carrier now has an explicit
`Module.compHom` instance (`scalarCohomologyModule`) and is wrapped with
`ModuleCat.of`, avoiding repeated kernel reduction through
`ModuleCat.restrictScalars` in the Ext transport and cup/pullback definitions.
With `SHEAF_FILE_TIMEOUT` unset, `FieldLinearModuleCohomologyOperations.lean`
compiles cleanly in 30 seconds (the default landing limit is 60 seconds).


## Second reading by G1

I independently opened the item node, both delivered modules, all eight definition
nodes used by the item/new node, and the source signatures below. I also fetched
`varieties.tex` and `cohomology.tex` from stacks/stacks-project into the scratchpad
and read `lemma-kunneth`, its preceding section and complete proof, the module
cohomology definition, and `section-functoriality`. The source imposes precisely a
field, quasi-coherence, quasi-compactness and affine diagonals; it imposes no
properness, separatedness, finite type, or characteristic assumption.

Object/hypothesis/conclusion checklist (each verdict is PASS):

- Base field: `k : Type w` and `[Field k]`. Mathlib `Field` is the ordinary
  nontrivial commutative division ring, matching `def-weil-field`.
- Schemes over k: `X Y : Scheme.{w}`, `f : X ⟶ Spec (CommRingCat.of k)` and `g`
  introduce the two schemes and structure maps. Mathlib `Scheme`/`Scheme.Hom`
  are the locally affine locally ringed spaces/morphisms of `def-pc-scheme`.
  Explicit structure maps are appropriate because this statement forms a fibre product.
- Module objects: `F : X.Modules`, `G : Y.Modules`; these are exactly Zariski
  `SheafOfModules` over the two structure sheaves, not etale sheaves.
- Quasi-coherence: `[F.IsQuasicoherent] [G.IsQuasicoherent]`. I read Mathlib's
  `IsQuasicoherent` (local presentations) and `Coherent.lean`'s identification
  with the affine-local module definition of `pqf-def-coherent`; no coherence or
  finite-presentation hypothesis is substituted.
- Quasi-compactness: `[CompactSpace X] [CompactSpace Y]`. Lean compactness here
  has no Hausdorff requirement, exactly quasi-compactness of schemes.
- Affine diagonals: `[IsAffineHom (Limits.pullback.diagonal f)]` and likewise g.
  Over affine Spec(k), this is the absolute affine-diagonal condition: it is
  equivalent to all intersections of affine opens being affine. It includes
  nonseparated schemes, so it does not strengthen the source to separatedness.
- Product and projections: `Limits.pullback f g`, `pullback.fst`, `pullback.snd`.
  I read the recorded pullback/universal-property signatures and the scheme
  pullbacks instance, rather than replacing the product by an unrelated scheme.
- Coefficients: `externalCupCoefficients f g F G` is the tensor of
  `(tensorPullback (pullback.fst f g)).obj F` and the analogous G object.
  I read `TensorPullback.lean`'s object/formula/functor definitions and the
  recorded tensor monoidal construction (sheafification of sectionwise tensor).
- Cohomology: `scalarCohomology` retains the carrier of the recorded
  `RingedSpace.moduleCohomology`, and restricts its Γ(X,O_X)-module action along
  `scalarMap f ⊤`. I read `globalSectionsFunctor`, `moduleCohomology`, and
  `globalSectionsComplex` in `RingedSpaceModuleCohomology.lean`. The resulting
  k-vector spaces are the source's O-module cohomologies.
- Degrees and sum: `∀ n : ℕ` and `{pq : ℕ × ℕ // pq.1 + pq.2 = n}` give every
  nonnegative degree and every p+q=n, with tensor over k, then `⨁`.
- Isomorphism: `∃ e : ... ≃ₗ[k] ...` has the source cup map's direction from
  the sum to product cohomology. The node's displayed unoriented identification
  is equivalent to this assertion.
- Canonical map: the equation on every `DirectSum.lof` pure tensor fixes e to
  `externalCup`, with the equality-of-degrees cast supplied by `i.property`.
  Pure tensors and summand inclusions generate the source, so no arbitrary
  vector-space equivalence can satisfy this clause instead of the cup map.
- Pullback functoriality: the second conjunct quantifies X',Y', f',g', u,v,
  `hu : u ≫ f = f'`, `hv : v ≫ g = g'`, and w with both projection equations.
  These characterize the induced product map uniquely. The displayed equality
  is pullback of the cup class, followed by `externalCupPullbackIso`, equal to
  cup of the two pulled-back classes. It holds on all bidegrees/classes and
  thus on all generators of the direct-sum map. No extra geometric assumptions
  are placed on X',Y'.

New node `def-sc-field-linear-module-cohomology-operations`: PASS after repairs.
Its self-contained statement introduces scalar restriction and canonical maps,
not a free choice of cohomology or cup pairing. I checked the `moduleExtEquiv`
choice is fixed by the formula for *every* injective resolution and cocycle;
`scalarUnitLinear`, `scalarPullbackCoefficient` and `scalarTensorCoefficient`
are fixed by their section formulas. Hence the Ext transport has canonical,
not arbitrary, data. The k-sheaf inverse image is exact; k-sheaf tensor is exact
because k is a field; the cup uses tensor transport and Yoneda composition,
then the sectionwise coefficient map s⊗t ↦ s⊗_{O_X}t. These are the operations
in 0BED and the functoriality construction of 01F7, with 01DZ's cohomology.
I read `exists_tensorPullbackAdjunction`'s normalized sectionwise unit and
`module_pullback_tensor`'s naturality/pure-section formula, which fix the
composition and external coefficient comparisons. No dependency module is
needed: the recorded notions are usable and used.

The new node has the required definition/split fields, source, exact cited
statement dependencies, empty proof fields, null mathlib_match/proof_origin,
worker/item/date/group creation record, matching chapter/unit, none audits,
and its own Lean record. Its ancestor is `thm-sc-theorem-of-cube`. I checked
its `blueprint.from.via` against the latest base, with the item prepended,
as §5 requires. The sandbox item copy's via was stale; the dry run refreshed
the base and confirmed that the original longer path was the current one. I added the
two performance-helper names to `lean.declarations`. The main signature and
the new node's primary `scalarCohomologyCup` signature remain unchanged.

Edge cases: PASS. Empty X or Y and zero F or G are admitted; there is no
nonempty/nonzero assumption. At n=0 the sole summand is (0,0) and the map is
the usual product of pulled-back sections. For each n≥0 the sum index is
nonempty; arbitrary empty affine covers in the proof are not excluded by a
statement binder. All characteristics and arbitrarily large vector spaces
are covered. The common arbitrary universe w holds schemes, their rings,
and module values; the Ext computation in w+1 is transported back to the
w-small derived-cohomology carrier, adding no smallness hypothesis or
independent smaller test universe. All binders are explicit with autoImplicit false.

Independent searches, with different phrases from the first worker:

- LeanFinder: `cohomology of quasi coherent sheaves on product of schemes
  tensor over field`: ordinary sheaf H/presheaf cohomology, module pullback,
  and monoidal sheaf instances; no matching theorem.
- Loogle: `"Kunneth"`: zero hits.
- LeanSearch: `Kunneth formula for quasi coherent Zariski module sheaves over
  a field`: service unavailable (Internal Server Error), not a negative result.
- LeanFinder: `Zariski sheaf vector space cohomology cup pairing restriction
  scalars`: module Tilde restrictions, change-of-rings adjunctions, ordinary
  sheaf H and group cohomology; no matching operation package.
- rg on Mathlib, WeilConjectures and lean/Sheaf for Kunneth/cup product and
  scalarCohomology/scalarSheaf/scalarExtCup/moduleExtEquiv: no duplicate of the
  delivered operations; etale six-functor Kunneth has different coefficients
  and hypotheses. I opened `HomologicalComplex.tensor_kunneth`: it is the
  algebraic complex theorem, not this geometric statement. The landed
  `PicardH1ProductInjective` merely uses this item for structure sheaves.
- `blueprint_refs.py search 'cup product'`, rg of DAG nodes, and upstream-name
  searches: etale/supported cup definitions and the Cech compatibility lemma
  do not supply the field-linear O-module operation package.

Mismatches repaired: two linearity theorem statements used `letI`, forbidden
by the statement conventions; I replaced those with explicit `SMul.smul`
instances for `Module.compHom`, preserving exactly the scalar actions. The
performance helpers `scalarCohomologyModule` and `scalarCohomology` lacked
source/blueprint docstrings; I supplied them and clarified the carrier's
own docstring. The new node's via was confirmed against the refreshed base and its helper
declaration list was repaired as described above. No mathematical statement correction was needed; nothing
in the item theorem was rewritten. Every postponed proof is a named theorem
with a source and natural-language proof; definitions have real data and
use named proof obligations, without embedded sorry data.

The compile also exposed the carrier helper’s unused structure-map binder;
I renamed it `_f`, retaining the explicit positional argument and silencing
the warning. The final dry-run server compile is clean. Both node primary
signatures match the files verbatim under the delivery signature reader.
