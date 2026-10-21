## Worker report

The module `Sheaf.Paper.FiniteFreeConstructibleScalarTransport` states
`AlgebraicGeometry.Scheme.finiteFreeConstructibleScalarTransport`. Its first
conclusion is preservation of the published three-clause integral constructible
predicate. Its second conclusion transports the supplied local models, with their
supplied stratification, covering sieves, representatives, bounds and isomorphisms.
All new theorem proofs are `sorry`; definitions have actual data. The coefficient-map
constructions now live in `Sheaf.Paper.FiniteFreeCoefficientTransport`, owned by
`def-weil-pbc-actual-finite-coefficient-transport`, rather than this theorem node.

Hypothesis and clause correspondence:

- The prime is `l : ℕ` with `[Fact l.Prime]`. The finite extensions are
  `E F : Type (u + 1)` with field, `Algebra (Padic l)` and
  `FiniteDimensional (Padic l)` instances. The inclusion is
  `i : E →ₐ[Padic l] F`; its injectivity follows from the field structure.
- The actual rings A and B are `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionIntegers l F`. Their recorded uniformizers and
  ideals are used by `pbcPadicCoefficientDatum`; no alternate rings or
  uniformizers are introduced. These rings inhabit the coefficient universe
  `u+1`, while the scheme has universe `u` and its site has object universe
  `u+1` and morphism universe `u`.
- `T : Scheme.{u}`, `[IsNoetherian T]`, `_hdim : ∃ n : ℕ,
  topologicalKrullDim T ≤ n`, and `_hl : IsUnit (l : Γ(T, ⊤))` render exactly
  the geometric hypotheses.
- The completed coefficient sheaves are
  `pbcAdicCompletion T (pbcPadicCoefficientDatum l E/F)`, the actual inverse
  limits of the positive finite quotient sheaves. The auxiliary completed map
  is uniquely fixed by all finite projections and the canonical quotient maps.
  The quotient-kernel theorem is merely the ideal-power condition needed to
  construct these maps from the already published integer inclusion.
- `K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E)` and `hK :
  PbcIsBoundedConstructibleComplete ... K` express membership in the full
  integral subcategory. This is the *published predicate itself*: intrinsic
  completeness, uniformly bounded constructible reductions with common local
  models, and compatible etale-origin witnesses. None is replaced by the older
  intrinsic constructibility predicate lacking the full witness condition.
- `finiteFreeCompletedScalar` is `pbcDerivedExtend` along the completed map,
  hence the published universal derived change of rings. The first conjunct
  asserts the identical three-clause predicate over B on its image.
- The second conjunct quantifies over `s : FiniteLocallyClosedStratification T`,
  the dependency's actual finite partition and scheme immersions; `V k` is a
  covering sieve of the terminal object of the small pro-etale site of each
  stratum. The explicit covering hypothesis keeps precisely the chosen covers.
- `P k U f hf` is the supplied algebra cochain complex on a chosen covering
  member. The integers `a k U f hf`, `b k U f hf`, the `IsStrictlyGE/LE`
  hypotheses, and `Module.Projective` together with `Module.Finite` give
  exactly bounded finite-projective terms, allowing bounds and models to
  depend on the covering member.
- The family `e k U f hf` is the supplied isomorphism from the restriction of K
  to the completed realization of that P. The restriction is expressed on the
  small pro-etale site of `U.left`, canonically equivalent to the slice site
  of the stratum at U. The morphism is literally `U.hom ≫ s.immersion k`.
  The published completed structural map gives the normalized completed-ring
  presentation of this restriction; the stratum-completion restriction lemma
  in the node's proof identifies it with the raw inverse-image presentation.
  Thus there is no change of covering member or of the given model.
- `finiteFreeCoefficientComplex` is literally the termwise existing
  `ModuleCat.extendScalars` functor, with differential `1 tensor d_P`. The
  output repeats the *same* a and b and asserts projectivity and finite
  generation of *every* term over B.
- The last clause is `IsIso (finiteFreeLocalModelMap ... (e k U f hf))`.
  That map is explicitly: the published K-flat-normalized scalar/restriction
  comparison, scalar extension of `e.hom`, the canonical K-flat counit,
  ordinary balancing and the inverse target-realization factorization.
  Its target is exactly the completed B-realization of `B tensor_A P`.
  `IsIso` makes this particular morphism an isomorphism, so this clause does
  not merely assert an unrelated `Nonempty` local model.
- `finiteFreeConstantBalance_existsUnique` fixes the ordinary balancing on
  every local generator by
  `((r tensor p) tensor s) ↦ c(r)s tensor (1 tensor p)`.
  `finiteFreeConstantComplexBalance` applies that same map degree by degree.
  Its uniqueness permits the definition to select it; the selected data is
  determined, rather than chosen from an undetermined existence statement.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported actual coefficient
  integer ring, uniformizer and quotient constructions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.Paper.AdicCoefficientDatum`: completed finite coefficient sheaves,
  `AdicCoefficients.coefficientMap` and the normalized tower constructions.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcPadicCoefficientDatum` and the
  actual-ring specialization of `PbcIsBoundedConstructibleComplete` and its
  full subcategory, through `Sheaf.Paper.BoundedConstructibleComplete`.
- `Sheaf.Paper.IntegralStratifiedPerfectModels`: `integralConstantModule`,
  `integralConstantModule_exact`, `integralConstantDerived`, and the recorded
  local model definitions. Their constant sheafification generators and tensor
  sections are the published `completedConstantGenerator` and
  `adicDatumTensorSection`, not a second realization construction.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`; its bounded finite-projective
  representative conditions are written out for the *supplied* representative P.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`;
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `extendScalars` and
  `extendRestrictScalarsAdj`, including its inherited additive structure.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`; the existing PBC
  specialization provides `pbcDerivedExtend` and `pbcComplexCounit`.
- `def-weil-pbc-integer-quotient-inclusions` records the existing
  `WeilConjectures.integralScalarIntegerInclusion` and
  `WeilConjectures.integralScalarQuotientMap` in
  `Sheaf.Paper.IntegralScalarExtensionWellDefined`; it owns the restriction of the
  given field embedding to the actual valuation rings and the quotient lifts.
- `def-weil-pbc-normalized-scalar-restriction` records the existing
  `pbcActualScalarDerivedPullIso` and its ordinary-adjunction and K-flat
  characterizations in `Sheaf.Paper.PbcActualScalarPullback`. Its source is
  Stacks 03EL and 0D6D; the recorded general tensor-pullback theorem is a distinct
  assertion and is no longer cited as a statement dependency.
- `def-weil-pbc-actual-finite-coefficient-transport` owns
  `finiteFreeCoefficientQuotientMap`, `finiteFreeCompletedCoefficientMap`,
  `finiteFreeCompletedScalar`, their named well-definedness/uniqueness/naturality
  theorems, and `finiteFreeScalarRestriction` in the new coefficient module.

Edge cases checked: E=F and the identity embedding are included, with the same
quotient-normalized map and tensor multiplication; ramified extensions preserve
same-index quotient maps because the image of the source maximal ideal is
contained in the target maximal ideal; the zero complex permits all zero terms
and any valid bounds; an empty scheme permits zero strata and the model clause
is vacuous; empty covering members are allowed; there is no restriction requiring
nonzero ranks or nonempty strata. Every degree is quantified, including degrees
outside the chosen interval. No equality of site object/Hom universes is imposed.

Searches: `msearch.py` leanfinder, query "Derived scalar extension of completed
coefficient sheaves preserves integral stratified perfect constructible complexes",
returned condensed/period-ring and ordinary module declarations, with no match.
LeanSearch, query "extension of scalars preserves constructible complexes of
completed coefficient sheaves", returned ordinary `ModuleCat.extendScalars` and
adjunction infrastructure, reused here; no full constructible-category match.
Loogle `ModuleCat.extendScalars, Module.Projective` returned zero matches.
`msearch.py grep 'constructible.*(complex|complete)|pro.?etale'
AlgebraicGeometry/Sites` returned the pro-etale site and elementary coefficient
sheaves, not this theorem. Direct `rg` of `lean/Sheaf` and `lean/WeilConjectures`
found no declaration carrying this node id. Searches for integral scalar
transport found `IntegralScalarExtensionConstructibleIntrinsic`, whose predicate
and completed coefficient presentation do not assert the retained compatible
etale-origin witnesses or the specified local model map; it is not an existing
match. Existing tensor, coefficient and realization helpers were inspected and
reused throughout. Search outputs are recorded by msearch.py in searches.jsonl.

No mathematical statement correction or disputed statement is required. The return
identified missing definition-level ownership, repaired by the three new definition
nodes described below. The transport theorem and its canonical local-model map are
unchanged; the two added theorem stmt_deps from the returned packet are dropped.

Proof imports: `IntegralStratifiedPerfectCharacterization` publicly reexports the
model definitions in the current server source. The published artifact still
contains the moved model declarations itself, so simultaneously importing it and
the model module produced "environment already contains ...
IsIntegralStratifiedFinitelyPresented". Importing only the characterization module
retains the proof dependency and its reexported definitions and avoids loading both
representations of the same declarations. The current source was checked with
`scompile.py --source`; no declaration was copied or renamed. The three unstated
proof dependencies (strict-perfect pullback model, stratum completion unit
restriction, normalized K-flat scalar comparison) have no recorded modules yet.
The already stated strict-perfect coefficient package, derived slice restriction
and sheaf tensor modules are imported for the rest of the node's proof plan.

The imported auxiliary operations framework has high-priority instances in
`max coefficient site` universes with an unconstrained coefficient size. As in
`PbcScalarExtension`, their four overlapping instances are disabled in this module;
the fixed-size PBC structures are unchanged. This resolves universe inference
without imposing any mathematical universe equality or additional assumption.

Validation of retained packet: before repairs, the requested initial
`deliver2.py --no-push` reported OK at dry-run commit 0760567f784. This established
that the retained packet compiles but does not discharge the independent return's
ownership objection. The repaired packet is compiled and checked separately below.
No global build or direct repository Git command was run.

## New nodes

`def-weil-pbc-integer-quotient-inclusions` gives the existing integer and quotient
inclusions a definition-level record. It is `existing: true` on
`WeilConjectures.integralScalarIntegerInclusion`, and additionally records its
quotient map, ideal-power kernel and reduction compatibility. It introduces no
second construction or module. Source: Bhatt--Scholze 6.8.14(1), as used in the
scalar-extension coefficient construction. The supplied field embedding is used
literally; no different coefficient field or valuation ring is chosen.

`def-weil-pbc-normalized-scalar-restriction` gives the existing canonical
scalar/restriction comparison a definition-level record, `existing: true` on
`pbcActualScalarDerivedPullIso` in `Sheaf.Paper.PbcActualScalarPullback`. Its statement
specifies the coefficient square, identity-on-sections right comparison, ordinary
adjunction conjugate, and the exact flat-term K-flat counit equation used to select
the unique derived comparison. Sources: Stacks 03EL and 0D6D, read in
`sites-modules.tex` and `sites-cohomology.tex`. No arbitrary isomorphism is supplied.
The new record includes the named uniqueness theorem on which the definition
selects its uniquely characterized data. The ringed-topoi tensor-pullback theorem's
record names a different declaration and does not own this interface.

`def-weil-pbc-actual-finite-coefficient-transport` owns the actual-ring finite quotient
map, projection-normalized completed map, its naturality, its derived extension,
and its normalized restriction specialization. Seven unchanged declarations moved
from the returned theorem module into `Sheaf.Paper.FiniteFreeCoefficientTransport`;
the source and blueprint docstrings now name their owning definition node. The new
module's primary declaration is `finiteFreeCompletedCoefficientMap`. The node
states every named helper property: quotient ideal-power well-definedness, unique
finite projections, structure-map naturality, and the specialized normalized
comparison. The original main theorem imports it publicly and uses exactly those
same constants.

H4 check: `def-weil-pbc-finite-completed-coefficient-map` and its complete module
`Sheaf.Paper.PbcFiniteCompletedCoefficientMap` were read. Its domain consists of
finite intermediate fields of a chosen algebraic closure, transported to `Shrink`
models and then `ULift` valuation rings. The present item supplies arbitrary finite
coefficient fields in universe `u+1` and requires their actual valuation rings and
recorded uniformizers. Its existing map cannot be applied at those types. The new
node is the actual-ring specialization, reusing the existing integer inclusion,
finite-coefficient functor, completed sheaves and derived change of rings. It does
not construct another copy of any of those notions.

Searches for all three definition records: `msearch.py leansearch` and `leanfinder`
with query "Canonical completed coefficient sheaf maps for finite p-adic field
embeddings with normalized derived scalar restriction comparison" returned eight
unrelated completion/restriction declarations and eight p-adic/period-ring
constructions respectively. `msearch.py grep` with query
`completed.*coefficient|scalar.*(pull|restriction)|IntegerInclusion` in
`AlgebraicGeometry/Sites` returned zero hits. Direct `rg` of `lean/WeilConjectures`,
`lean/Sheaf` and `dag/nodes` found the exact integer-inclusion and normalized
comparison helpers reused by the two existing records and the transported-field
completed map just discussed. `blueprint_refs.py search` returned zero blueprint
matches. The node records contain these exact search queries and outcomes; the
msearch output is retained in `searches.jsonl`.

## Repair of return L at d04022db8bbf

H2 / theorem-stmt_dep: removed `lem-weil-integral-scalar-extension-well-defined`
and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` from this item's stmt_deps.
Replaced them with definition records owning the actual integer/quotient maps,
completed coefficient map with naturality, and normalized scalar/restriction
comparison. No theorem was added as a dependency merely to expose a plain def.
Every delivered module is owned by exactly one definition/theorem node. The two
already published interfaces are reused as existing definitions, not copied.
The saved theorem signature, all hypotheses, full three-clause predicates, same
amplitude, finite-projective terms and specified `IsIso` local-model map remain
identical to the mathematically accepted returned packet.

## Second reading by Q134

Author's second pass, with the node and final module open; the dispatcher explicitly
forbids starting another agent, and the independent delivery review belongs to the
maintainer. Checked the full three-clause predicate against the first conjunct,
the exact covering hypotheses and dependent families against the second conjunct,
and the source's canonical-isomorphism requirement against the actual composite
map and its pure-tensor normalization. Corrected the initial draft's per-member
quantification to include the entire supplied covering/model family. Verified that
the actual valuation rings and all site universes are retained, finite-projective
terms and bounds refer to the termwise B tensor_A P itself, and the exact supplied
e is used. Definitions select only uniquely determined maps or isomorphisms;
all new theorem proofs remain sorry. No extra hypothesis or missing clause found.


Repair self-check by the author (the dispatcher forbids starting another agent):
read all three new definition statements against the actual recorded signatures
and bodies. The integer map is the given codRestrict, the quotient lift kills
exactly the prescribed ideal, the completed map is selected only by a unique
projection formula, and the right/ordinary/derived comparisons retain their
identity-section and counit normalizations. The moved seven declarations are
identical apart from blueprint ownership docstrings. Re-read the main theorem:
its signature and local model composite have not changed, and it now imports the
owning coefficient module. No added hypothesis, omitted clause or excluded edge
case was found. The independent maintainer review remains required.


Final repair validation (2026-10-21): `scompile.py` compiled both delivered modules
in dependency order, with sandbox and library checks clean (new coefficient module
5.7 s; main library module 9.7 s). The theorem signature is byte-for-byte equal
to the retained `lean.statement`; the only item fields changed against current
main are `lean` and `stmt_deps`. Each new definition node's bracketed references
matches its stmt_deps exactly. The prescribed repaired-packet dry run reported
`OK (dry run): commit 936338698e9 passes the preflight and compiles; nothing pushed`.
The nearby completed-pullback tensor and A1 coefficient-transport definition nodes
were also inspected: they concern same-coefficient tensor/pullback or comparison
of presentations, rather than this two-coefficient scalar/restriction square.
