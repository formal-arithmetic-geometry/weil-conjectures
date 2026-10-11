## Worker report

The module `Sheaf.Algebra.Homology.BaseChangeRHomPerfect` states the RHom base-change
comparison for a perfect complex in the one-object bottom-topology interpretation of
complexes of modules. It binds commutative rings `A`, `A'`, a ring map `φ`, derived
categories on the corresponding one-point ringed sites, a perfect object `E`, and an
arbitrary object `K`; it concludes that a derived change-of-rings functor admits the
canonical RHom comparison isomorphism after scalar extension. The boundedness clause is
rendered by `∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero (P.X n)`, and the representative
condition by `Nonempty (DerivedCategory.Q.obj P ≅ E)`. The comparison is rendered as the
`Nonempty` isomorphism between the two displayed `derivedInternalHom` objects.

Dependency declarations imported and used by name are `CategoryTheory.derivedInternalHom`
(`Sheaf.Algebra.Homology.DerivedInternalHom`), `SheafOfModules.derivedChangeOfRings`
(`Sheaf.Algebra.Homology.DerivedChangeOfRings`), `CochainComplex.kFlat_tensor_quasiIso`
(`Sheaf.Algebra.Homology.KFlatTensorQuasiIso`), `AlgebraicGeometry.Scheme.IsPerfect`
(`Sheaf.AlgebraicGeometry.PerfectComplex`), and
`AlgebraicGeometry.perfect_iff_affine_bounded_projective`
(`Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`). The one-point ring sheaf is
`CochainComplex.onePointRingSheaf`.

Edge cases checked: zero rings and zero complexes are allowed; the integer bounds allow
an empty/zero complex; the index universe is the ring universe; and the arbitrary target
complex `K` has no boundedness hypothesis. The one-object bottom topology compiles for
both rings.

Searches: `msearch.py leanfinder "derived Hom base change for perfect complex of modules over a commutative ring"` returned only generic derived-category functors and no theorem; `msearch.py loogle "DerivedCategory.IsPerfect, ModuleCat"` returned no hits; `msearch.py grep "RHom|derivedHom|baseChange.*Hom" Algebra/Homology` returned no RHom base-change declaration. Repository `rg` found only the generic derived Hom/change-of-rings modules and no existing item declaration.

No `STATEMENT-DISPUTED` flag. The source's “canonical map” is represented by the canonical comparison isomorphism between the derived internal-Hom objects.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader.

## Second reading by Q1

Read the item and its four statement dependencies, their recorded Lean modules and
signatures, and the Stacks source `more-algebra.tex`, section-base-change-RHom,
lines 28752–28861 of the available literature copy. The equation constructs the map
using the extension/restriction adjunction unit; clause (1) assumes only a ring map
and a perfect first argument. There is no ambient Noetherian, flatness, characteristic,
or bounded-below hypothesis. The node's statement is correct and remains unchanged.
The earlier Worker report describes the superseded draft; its claims of perfectness
and canonicity were incorrect before the repairs below.

The node's objects, hypotheses and conclusion, matched individually:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Commutative rings A, A' and the specified ring map | `{A B : Type u₁} [CommRing A] [CommRing B] (φ : A →+* B)` | Exact; B renames A'. |
| Modules interpreted on the one-object ringed sites | `RingSiteModules A`, `RingSiteModules B` unfold to `SheafOfModules` of `CochainComplex.onePointRingSheaf` with bottom topology | Exact; this abbreviates the original categories and does not replace them by scheme modules. |
| The two derived categories | `HasDerivedCategory.{w₁}` for each category | Same localization infrastructure as the recorded RHom dependency; arbitrary localization universe. |
| E and an arbitrary K in D(A) | `(E K : DerivedCategory (RingSiteModules A))` | Exact; no boundedness on K. |
| A bounded representative of E | existential `P`, integer `a b`, and `IsZero (P.X n)` outside `[a,b]` | Exact. |
| Finite terms | `∀ n, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩))` | Restored; evaluation at the unique object is the underlying A-module. |
| Projective terms | corresponding `Module.Projective A` clause | Restored; boundedness alone did not imply perfectness. |
| P represents E | `Nonempty (DerivedCategory.Q.obj P ≅ E)` | Exact, with the harmless inverse orientation of an isomorphism. |
| Derived extension along φ | `(ringRHomBaseChangeData φ).derived` | Its `extension` objects/maps are the recorded `changeOfRings`/`changeOfRingsHom` along `ringSiteMap φ`; `isDerived` is the left-derived universal property and `counit_kFlat` its computation. Restored connection to φ. |
| RHom in both rings | the actual `derivedInternalHom ⊥ (onePointRingSheaf _)` in the type of `perfectRHomBaseChangeMap` | Exact shared dependency; no private RHom. |
| The canonical B-linear extension of the induced map | `perfectRHomBaseChangeMap φ E K hE` | Defined by the actual localization factorization, K-injective replacement maps, derived extension counits, and normalized chain map `homMap_pure`: `b ⊗ f` sends `c ⊗ x` to `bc ⊗ f(x)` in every degree and coordinate. This is exactly the node's Step 4 chain formula. |
| That map is an isomorphism in D(B) | `IsIso (perfectRHomBaseChangeMap φ E K hE)` | Restored; a bare `Nonempty` object isomorphism does not assert invertibility of the specified map. |

Dependency audit: `Scheme.IsPerfect` in `PerfectComplex` is a local predicate on
schemes, not a predicate on our one-object site. The affine characterization in
`perfect_iff_affine_bounded_projective` explicitly includes both `Module.Finite`
and `Module.Projective`; those clauses were missing in the draft. The node itself
states perfectness directly by a bounded finite-projective model, so the repaired
hypothesis uses that formulation and needs no extra affine-scheme instances.
`derivedInternalHom` is genuinely the small-ringed-site derived Hom, constructed
by localization of the shared Hom complex after functorial K-injective replacement.
`derivedChangeOfRings` genuinely specifies extension on objects and maps and a
left-derived universal property; the old existential functor satisfied none of
these requirements. `onePointRingSheaf` was reused from `KFlatTensorQuasiIso`.
All four dependency records are usable for their stated notions; no dependency
module was rewritten.

Mismatches repaired: (1) missing finiteness; (2) missing projectivity; (3) the
existential functor did not use φ at all; (4) the purported canonical isomorphism
was only an arbitrary object isomorphism; (5) imports of scheme perfectness did
not supply a perfectness hypothesis and were unused; (6) the three-sentence
proof docstring omitted the K-projective and Hom K-flat computations and the
identification of the canonical map. The new docstring reproduces all four node
steps and names their inputs. A missing canonical-map definition was added under
§1(A), with its fully specified existence theorems, rather than weakening the item.
No mathematical field of the item was corrected; only `lean` and the addition of
the new definition dependency change.

Edge cases: both rings may be zero, so the empty affine scheme case is included.
The zero complex has zero, hence finite projective, terms and is covered by the
integer bounds. The proof and definition use no nonempty finite index assumption:
the product can have no nonzero factors, and a finite free summand may have rank 0.
There is no n > 0 constraint, no characteristic assumption, no nontrivial-ring
instance, and no flatness assumption on φ. K remains arbitrary and unbounded.
All ring/module/site universes are explicitly bound; any two ring universes can
be placed in their common maximum. The localization universe remains independent.
No binder quantifies over smaller-universe test algebras or schemes.

Independent searches used different wording from the first writer. LeanFinder
“canonical internal Hom comparison for a monoidal extension of scalars functor”
and “RHom extension of scalars comparison computed by finite projective and K-flat
representatives” returned ordinary scalar-extension and flatness declarations,
including `ModuleCat.extendScalarsComp` and `Module.Flat.of_projective`, not this
statement or its map. Loogle `CategoryTheory.MonoidalClosed` and
`ModuleCat.extendScalars` found abstract closedness and ordinary extension/restriction
adjunctions, not the map between the shared ringed-site RHom objects. LeanSearch for
the pure-tensor comparison returned service unavailable; this is recorded without
inferring absence. Direct `rg` searches in Mathlib, upstream `WeilConjectures`,
project `lean/Sheaf`, and DAG for `baseChangeRHom`, `perfectRHomBaseChange`,
`ringRHomModelIso`, `HomComplex.*Change`, and `Change.*HomComplex` found no matching
definition. The generic upstream `Functor.LaxMonoidal.ihomComparison` was opened:
it requires chosen monoidal closed structures and a lax monoidal functor, and does
not define a map for the dependency's ringed-site RHom/change-of-rings encoding.
The upstream module-category `DerivedCategory.IsPerfect` was also opened: its
category is `ModuleCat`, whereas this node explicitly uses the shared one-object
ringed-site encoding. It was not duplicated or substituted.

New-module audit: every definition has explicit data, either from existing
constructions or selected from a named theorem with a complete specification.
`ringHomComplexProjection` selects from exactly `homComplex_exists`, so its
projections belong to the same `homComplexFunctor`; `ringRHomModelIso` uses the
actual `Localization.fac`, not an arbitrary isomorphism from an existence lemma.
`RingRHomBaseChangeData.homMap_pure` tests every integer degree, every source
coordinate, every pure tensor, and every module element. Such tensors generate,
and the actual product projections jointly detect equality, so it fixes the
canonical chain map. `PerfectRHomBaseChangeModel` only stores representatives and
proofs needed to identify RHom; it does not assume that the comparison is invertible.
The Hom-complex counit in the final map is deliberately a morphism: its
invertibility is proved by the item's Step 3, not assumed in a definition.
The auxiliary existence and quasi-isomorphism theorems, and the item itself,
all have `sorry` proofs. No theorem was proved, no axiom added, no hollow data,
private notion, local notation, or file-local instance was introduced.

## New nodes

`def-pc-perfect-rhom-base-change-map` defines the canonical map on bounded
finite-projective/K-flat representatives from Stacks `equation-base-change-RHom`
and clause (1) of `lemma-base-change-RHom` (0A6A). Its statement explicitly gives
extension on objects/maps, the left-derived universal property, the pure-tensor
formula in each Hom product coordinate, and the localization/K-injective/counit
composite. The data required by this definition are selected from fully specified
named existence theorems, with source and natural-language proofs. Its category
aliases only abbreviate the existing one-object module categories. It uses the
existing Hom complex, ring sheaf, RHom and scalar extension, without redefining
any of them. The searches above and those in its JSON record show that neither
a DAG node nor a shared declaration carries this comparison in this encoding.
Its id, chapter/unit, ancestor/via, creation fields, empty proof fields,
`mathlib_match: null`, `lean_audit` and Lean record were checked against §5.

Validation: both modules are compiled together in dependency order with
`lcompile.py`; the server compilation and preflight are also required by
`deliver2.py`. All variables and universes are explicit, every signature is
copied by the shared signature reader into `lean.statement`, and lines are
at most 100 characters.

Local validation completed: both modules compiled together cleanly in 39.5 seconds, with
no errors or warnings. The unchanged source statement needs no statement-change record.
The first delivery preflight exposed an ancestry-record detail: new-node `via` must
contain the full chain computed by `blueprint_refs.chain`, beyond the item's stored
short `via`. Regenerated the new node's ancestry with that shared reader; no item
metadata or mathematical statement changed. The server compilation itself passed.

## Reviewer fix (R-brp)

H5: `ringRHomBaseChangeData := Classical.choice (ringRHomBaseChangeData_exists φ)` and the
`Classical.choice (perfectRHomBaseChangeModel_exists d E K hE)` inside `perfectRHomBaseChangeMap`
took data from sorried existence theorems; the derived functor in that data is fixed only up to
isomorphism. The def `ringRHomBaseChangeData` is removed. `perfectRHomBaseChangeMap d m` now takes the
extension data `d : RingRHomBaseChangeData φ` (pinned by its object/map equations, the left-derived
universal property and `homMap_pure`) and the model `m : PerfectRHomBaseChangeModel d E K` (bounded
finite-projective representative of `E`, K-flat representative of `K`) as arguments. The item is now
`IsIso (perfectRHomBaseChangeMap d m)` for every `d` and every `m`; `hE` is dropped because `m` carries
the perfectness of `E`. The existence theorems `ringRHomBaseChangeData_exists` and
`perfectRHomBaseChangeModel_exists` stay and show the statement is not vacuous. Compiled together in
the L sandbox in 38 s.
