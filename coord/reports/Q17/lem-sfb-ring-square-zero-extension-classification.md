## Worker report

The module `Sheaf.RingTheory.SquareZeroExtensionClassification` states
`Algebra.SquareZero.exists_unique_extension_classification`. Its only postponed proof
is this theorem. All definitions have real data. The natural-language statement is
unchanged. One new definition node supplies the missing ring-extension interface.

Clause-by-clause correspondence:

- Rings and base map: `a : Arrow CommRingCat.{u}`; a map over a fixed base is
  `a : R ⟶ A`, `b : R ⟶ B`, `f : A ⟶ B`, `hf : a ≫ f = b`.
  There are no flatness, finite generation, Noetherian, nonzero or characteristic binders.
- The full complex is the recorded `Algebra.CotangentResolution.cotangentComplex C a`.
  `C : Coherence` and `D : Naive.Comparison C` specify the existing normalized models;
  these are construction data, not additional mathematical assumptions. Their existence
  theorems are imported, not used to choose an unspecified cotangent object.
- `E1 C a M` is exactly Hom in `DerivedCategory (ModuleCat a.right)` from that full
  complex to `((DerivedCategory.singleFunctor ... 0).obj M)⟦(1 : ℤ)⟧`.
  The derived-category size instance is the same family used by the dependency.
- The exact additive sequence is `Extension.injection`, `injective`, `surjective`,
  and `exact`. `base`, `projection`, and `triangle` encode the R-algebra map.
  `square_zero` and `action` impose precisely the square-zero kernel and specified
  A-action. No algebra structure on M as a unital ring is requested.
- `IsIsomorphic` fixes both ends and the base. `Classification` asserts surjectivity
  of `cl a M` and `cl E = cl F ↔ IsIsomorphic E F`. This is the bijection on
  isomorphism classes, expressed without selecting representatives or an artificial
  universe-small quotient. No extension carrier outside the common ambient universe
  is excluded: choose u large enough for all rings and modules in the datum.
- Canonicity, rather than an arbitrary bijection: `HasPresentationFormula` requires
  a polynomial/localized polynomial presentation, an actual algebra lift `t`, and
  the conormal map `h` characterized on every kernel element. The chain map `q`
  goes to M in degree -1 and its component is h. The equality for `cl` is the
  normalized full comparison followed by Q(q) and the canonical identification
  M[-1] = M[0][1]. Thus the positive projection fixes the 0GPU sign.
  The theorem asserts unique existence of this class family.
- `IsSplit` uses Mathlib's existing `TrivSqZeroExt` carrier and inclusions. Its
  additive equivalence explicitly preserves the multiplication `(ab, an+bm)`, base,
  kernel and projection. This avoids assuming a second opposite-module action on
  an arbitrary module merely to synthesize the trivial-extension ring instance.
  Classification asserts existence of a split extension and that every such
  extension has class zero.
- `IsPushout` specifies the coefficient pushout by its universal property in
  extensions with fixed quotient and new kernel. The theorem asserts its existence
  and its class is `coefficientMap C u ...`, the actual shifted postcomposition.
  The universal property does not choose or assume a pushout object.
- `IsFiberProduct` bijects its elements with all pairs of elements with equal
  quotient and has the two prescribed kernel projections. `IsBaerSum` is this
  fibre product followed by pushout along `LinearMap.fst + LinearMap.snd`.
  Classification asserts existence and the additive class identity for every sum.
- General f,u clause: `u : M ⟶ (ModuleCat.restrictScalars f.hom).obj N` is exactly
  A-linearity for the induced action. `Nonempty (Hom E F f u.hom.toAddMonoidHom)`
  is existence of an R-algebra map inducing f,u. Its iff equates the explicit
  coefficient image with `pullbackClass C (baseSquare a b f hf) (cl ... F)`.
- `pullbackClass` is precisely `cotangentMap C q` followed by restriction on
  derived morphisms, then Mathlib's canonical `commShiftIso` and
  `mapDerivedCategorySingleFunctor` comparisons. It is not derived tensor base change.
- `ClassMapsFunctorial` includes coefficient identity/composition, base identity/
  composition, and commutation of coefficient maps with base maps. `HEq` in the
  base identity/composition equations compares the iterated restriction module
  with the canonically identical module restricted along the composite; it adds
  no arbitrary transport or equality hypothesis.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `cotangentComplex`, `cotangentMap`,
  and its standard terms/maps and tensor normalization. Imported publicly.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `Q`, `singleFunctor`, and `singleFunctors` (full signatures
  and docstrings read). Imported publicly.
- `Sheaf.RingTheory.NaiveCotangentComparison`: `Naive.Presentation`,
  `IsLocalizedPolynomial`, `conormal`, `kernelClass`, `complex`, `conormalIso`,
  `Comparison.comparison`, including its normalization/naturality fields.
  These plain definitions and structures are owned by the landed existing:true
  node `def-trf-naive-cotangent-comparison-data`, which is cited in stmt_deps.
  The parameter `D : Naive.Comparison C` uses these data directly; there is no
  choice from `exists_comparison`. The existence theorem node
  `lem-trf-lci-naive-cotangent-model` remains in proof_deps only.
- `Mathlib.Algebra.TrivSqZeroExt.Basic`: `TrivSqZeroExt`, `inl`, `inr` and the
  displayed multiplication law. Its existing definition node is added to stmt_deps.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (publicly available from
  cotangent coherence): `mapDerivedCategory`, `mapDerivedCategorySingleFunctor`,
  `commShiftIso`; `ModuleCat.ChangeOfRingsExact` supplies exact restriction.
- All stated proof-dependency modules are imported: polynomial rings and Kahler
  differentials through public NaiveCotangentComparison imports; two-term boundary;
  standard t-structure/orthogonality; triangle Hom exactness; projective modules,
  ModuleCat projectivity, projective Ext vanishing and Ext. The coherence existence
  theorem lives in the already imported coherence module. No omitted cycle imports.

Edge cases checked mathematically: M=0 forces E≅A, matching the zero Hom group;
A=0 forces its unital module M=0 and E=0; R=A gives only split extensions;
u=0 yields the split coefficient pushout; f=id and u=id give isomorphism exactly
on equal classes; addition with the split extension is neutral. The nonsplit
Z/p² extension of F_p by F_p over Z is allowed, so no hidden algebra section or
additive splitting was imposed. Arbitrary infinite polynomial generators and
arbitrary modules are allowed. In the presentation formula lower cohomology of
L is retained; no amplitude or lci assumption is added.

Searches actually run with msearch.py (records in searches.jsonl):

- LeanFinder: “Square zero extensions of commutative algebras are classified by
  Ext one of the cotangent complex naturally with Baer sum”: eight hits, principally
  `Algebra.Extension.H1Cotangent`, which is naive cotangent homology, not classification.
- Loogle: `TrivSqZeroExt, Algebra.Extension, DerivedCategory`: zero hits.
- LeanSearch: “square zero algebra extension with fixed kernel module isomorphism
  classes”: eight hits on trivial extensions and `Algebra.Extension.infinitesimal`.
- Mathlib grep: `SquareZeroExtension|square.zero extension|Baer`, RingTheory:
  eleven unrelated Baer-injectivity hits. `SquareZeroExtension|square.zero
  extensions|Baer sum`, all Mathlib: zero hits.
- Project rg for square-zero extensions and extension class names found the
  ringed-space/sheaf interface `TopCat.SquareZeroSheaf.Extension`, not a ring
  extension with ordinary-module kernel. `rg` for the item id in WeilConjectures
  returned no declaration. Read Mathlib `Algebra.Extension`: it is a general
  surjective algebra presentation with unspecified kernel, not this interface.
- DAG search found the unstated conormal-class and kernel-pushout lemmas, but no
  definition node giving this interface. `tools/blueprint_refs.py search
  'square.zero|extensions-of-algebras'` returned zero blueprint matches;
  `ancestor` returned None, preserved in the new node's blueprint provenance.

Sources read: defos.tex labels lemma-extensions-of-algebras,
remark-extensions-of-algebras, lemma-extensions-of-algebras-functorial,
remark-extensions-of-algebras-functorial (0GPT--0GPW), plus the recorded full
cotangent comparison and its 08RB documentation. No statement fault or dispute found.
Both delivered files compile cleanly with scompile.py, with autoImplicit false.

## New nodes

`def-sfb-square-zero-algebra-extension` defines the specified kernel/quotient
extension, its maps and isomorphisms, split predicate, coefficient pushout,
fibre product and Baer-sum diagram. Its own module is
`Sheaf.RingTheory.SquareZeroAlgebraExtension`. The source is Stacks 0GPT/0GPV/0GPW,
with the paired conormal/Baer description of 0GPU. The searches above show why
neither the general Mathlib algebra presentation nor the existing sheaf extension
is this notion. It cites the existing trivial-extension definition and constructs
no replacement trivial ring. All its definitions are data or predicates, with no
postponed proof or hollow choice. Its blueprint ancestor is null because the
prescribed ancestor tool returns None for this item; the inherited place and
complete via chain are retained.

## Repair of returned delivery 834edc6ff51

H2: replaced `lem-trf-lci-naive-cotangent-model` in the item's stmt_deps with
`def-trf-naive-cotangent-comparison-data`. The latter's existing:true record owns
the exact `Naive` definitions and `Comparison` structure used in the statement.
The theorem remains in proof_deps. The dependency paragraph above now distinguishes
these roles. Both Lean modules, all signatures and the mathematical statement are
unchanged from the returned delivery. Current main still has only the original
two statement dependencies and no Lean record; the prescribed delivery wrapper
will apply this repaired packet to current main.

## Repair attempt for returned delivery eedc037676b

The return requires reusing `Algebra.SquareZero.Extension`, `Hom`, and `IsSplit`
from `Sheaf.RingTheory.MarkedSquareZeroExtension`. That module is absent from
the read clone and from the current live server's Lean source tree. A read-only
search of the live DAG has no binding for the named module or declarations; the
only matches are in this item's return entry.

The prescribed source command
`scompile.py --source Sheaf.RingTheory.MarkedSquareZeroExtension` exits 1 with
`Module source unavailable: Sheaf.RingTheory.MarkedSquareZeroExtension`.
An isolated import probe through scompile.py also fails, including its server
confirmation, because `Sheaf/RingTheory/MarkedSquareZeroExtension.olean` does
not exist. Thus neither the required source signatures nor the import are
available through the authorized live-source/compiler tools.

The current-source-index collision refusal refers to an unavailable module.
No declaration was renamed or recreated to evade the refusal, and no unchanged
packet was pushed. The earlier H2 dependency repair remains intact. Reuse can
be completed once the module named by the collision index is available, or the
stale collision entry is corrected by maintenance.

## Recheck of unavailable collision dependency

On the next dispatched repair retry, `scompile.py --source
Sheaf.RingTheory.MarkedSquareZeroExtension` again exits 1: module source
unavailable. A fresh import probe again fails with the missing
`MarkedSquareZeroExtension.olean`, confirmed against current server sources.
The existing two-module packet compiles and passes the prescribed dry run
(commit 5d7bcdaa735, not pushed), but this does not supply the unavailable
declarations demanded by the immutable-head return. No unchanged re-push or
renaming was performed. The earlier H2 repair is retained.

## Resolution of stale duplicate-name return

Fresh read-only inspection of the live maintainer's
`local/stage2/parallel/source-index.pickle` on 2026-10-24 at 14:19 UTC shows
no indexed owner for any of `Algebra.SquareZero.Extension`,
`Algebra.SquareZero.Hom`, or `Algebra.SquareZero.IsSplit`. Its source-stamp
map likewise has no entry for `MarkedSquareZeroExtension`. The named source
file remains absent, and the prescribed source reader still reports the module
unavailable. Thus the stale collision entry that caused the return is now
cleared in the live maintainer index; there is no existing interface to import.

The return's requested reuse cannot be performed because there is no such
module, source binding, or indexed declaration. Retaining the original
definitions introduces no currently indexed duplicate and preserves the exact
interface already mathematically accepted in the independent review of
834edc6ff51 and eedc037676b. No declaration was renamed to conceal a collision,
no replacement for an available interface was introduced, and no tool/cache
was modified by this worker. The previous two blocker observations are
historical; the latest index evidence resolves their stale-refusal cause.
The H2 definition-node dependency repair remains applied. The prescribed
wrapper reapplies this packet to current main and checks it before delivery.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
