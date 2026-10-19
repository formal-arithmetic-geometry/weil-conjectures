## Worker report

Item: `det-ambient-ind-derived-triangulated`; group NE; 2026-10-18 UTC.
Module: `Sheaf.Paper.AmbientIndDerivedTriangulated`.

The shared base already records Q61's theorem
`AlgebraicGeometry.ProEtale.indConstructibleDerived_isTriangulated`.
The current source was confirmed with `scompile.py --source`. Its signature is
retained verbatim. The delivery adds
`AlgebraicGeometry.ProEtale.indConstructibleDerived_isClosedUnderIsomorphisms`,
covering the node's explicit isomorphism-closure clause for both coefficients.
Mathlib's `ObjectProperty.IsTriangulated` deliberately omits this clause
(Subcategory.lean, implementation notes), so that class alone was an incomplete
rendering of the whole node. Both statements have `sorry` proofs. Both are
clauses of this same DAG statement, and are listed in `lean.declarations`.
No natural-language node statement or dependency record changes.

The module also imports the now-recorded kernel/cokernel theorem, alongside
the extension theorem and the Mathlib proof dependencies. These are ordinary,
non-public proof imports. No new notion or auxiliary DAG node is necessary.

### Hypotheses, objects, and clauses

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]` in each declaration.
- Finite extension inside the fixed algebraic closure:
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. This uses the existing topology
  and scalar-field structure on the finite intermediate field.
- Ground field and positive characteristic: `(k : Type u) [Field k] (p : ℕ)
  [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)`.
- Scheme over that field: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- Separated: `[IsSeparated (X ↘ Spec (.of k))]`.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` together with
  `[QuasiCompact (X ↘ Spec (.of k))]`, the project's standard finite-type form.
- Coefficients E and Qbar: the two conjuncts use `padicSubfieldRingObj X ℓ E`
  and `padicAlgClRingObj X ℓ`, respectively. Their definitional bodies are
  `condensedRingObj (Profinite.continuousMapRingObj E) X` and
  `condensedRingObj (Profinite.padicAlgClRingObj ℓ) X`. These are the recorded
  pulled-back condensed rings, with their canonical monoid structures.
- The module category is exactly `CategoryTheory.Mod
  (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})` at the corresponding ring.
  No arbitrary action structure or alternative coefficient category is used.
- The ambient category is `DerivedCategory` of this abelian category,
  the ordinary unbounded derived category. No completeness or boundedness
  condition is imposed.
- Cons is the recorded `IsConstantModelConstructible` at the same condensed
  coefficient ring. This is the affine-local finite constant-model definition,
  not the different upstream finite-local-presentation predicate.
- IndCons is `ObjectProperty.ind.{u + 1}` of that predicate. Reading Ind.lean
  shows it quantifies over a `Type (u+1)` small filtered category, a
  `ColimitPresentation` at the specified ambient module, and constructible
  diagram objects. Thus it includes exactly isomorphic ambient colimits,
  with no abstract ind-category substituted.
- Dic is the inline object predicate `∀ n : ℤ, ObjectProperty.ind ...
  ((DerivedCategory.homologyFunctor _ n).obj K)`.
- Zero and all positive and negative shifts are the `ContainsZero` and
  `IsStableUnderShift ℤ` fields of `ObjectProperty.IsTriangulated`.
  ContainsZero is up to isomorphism, as in the recorded subcategory definition;
  the second declaration's isomorphism closure supplies the chosen zero too.
- Isomorphism closure is explicitly the conclusion
  `ObjectProperty.IsClosedUnderIsomorphisms` of the added declaration,
  separately for the two identical inline predicates.
- Two-out-of-three for any ambient distinguished triangle is exactly
  `IsTriangulated` together with that isomorphism closure: its middle-vertex
  field and Mathlib's derived first/third-vertex instances give all three
  cases. The `ext_of_isTriangulatedClosed₁`, `₂`, `₃` lemmas remove the
  intermediate isoClosure using the explicit closure assertion.
- Full triangulated subcategory has the recorded meaning
  `ObjectProperty.IsTriangulated`; `P.FullSubcategory` retains all ambient
  morphisms. Mathlib supplies its inherited triangulated structure and exact
  inclusion. No stronger admissibility or thickness condition is asserted.

### Dependency declarations read and used

- `sk-def-sfb-dc-setting`: read
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the
  surrounding standing field/scheme assumptions. This item uses the explicit
  standing binders; compactification is irrelevant because no morphism or
  shriek functor occurs. The module is already in the coefficient import closure.
- `def-sfb-subfield-coefficient-ring`, `def-sfb-qlbar-coefficient-ring`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`,
  `AlgebraicGeometry.ProEtale.padicSubfieldRingObj`, `padicAlgClRingObj`.
  Read their full enclosing context and definitional bodies in the published
  51-module framework under the shared read-only lean/WeilConjectures tree.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, and action-compatible morphisms.
- `pur713-def-module-category`, `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`; also read `DerivedCategory.Plus` and `.Bounded` in
  TStructure.lean to confirm these bounds are not part of this ambient category.
- `sk-def-sfb-constructible`:
  `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`, including
  `HasFiniteConstantLocalModel` and `IsFiniteConstantStratified`.
- `def-weil-triangulated-subcategory`:
  `Mathlib.CategoryTheory.Triangulated.Subcategory`,
  `CategoryTheory.ObjectProperty.IsTriangulated`; read its complete fields,
  iso-closure convention, and the three triangle-closure APIs.
- Proof imports: `Sheaf.Paper.IndHeartKernelsCokernels`,
  `AlgebraicGeometry.ProEtale.indHeart_kernelsCokernels` and its assertion
  predicate; `Sheaf.Paper.IndConstructibleExtensions`,
  `indConstructible_of_shortExact` and its `_padicAlgCl` variant.
- Other proof interfaces read: `CategoryTheory.Functor.shiftIso` in
  `Mathlib.CategoryTheory.Shift.ShiftSequence`;
  `DerivedCategory.HomologySequence.exact₁`, `.exact₂`, `.exact₃` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`;
  `CategoryTheory.Abelian` and the monicity of `Abelian.factorThruCoimage`
  in `Mathlib.CategoryTheory.Abelian.Basic`; `CategoryTheory.Pretriangulated`
  and the triangulated subcategory rotation interfaces.

### Sources and proof plan

Read the main-20261015 blueprint unit `_section.md`, the item's statement and
proof files, all eight statement-dependency nodes, and the recorded proof
interfaces. The first declaration's docstring retains all seven DAG proof
steps: zero and isomorphisms; shifts; long exact cohomology; the ambient short
exact sequence via coimages; kernel/cokernel and extension closure; both
signed rotations; and the inherited full triangulated structure. The new
clause's docstring expands the isomorphism part of step 1. It needs no
independent mathematical lemma or data construction.

### Edge cases

Checked the zero complex and the empty scheme: the zero finite scalar module
and empty/vacuous strata are permitted, so the predicate contains zero.
All integer degrees and all integer shifts, including zero and minus one,
are present, with no lower or upper bounds on a complex. The degree-one field
extension E = Q_ell is a permitted finite intermediate field. The Qbar clause
uses its canonical condensed finite-subextension ring, not arbitrary
continuous functions into an algebraic closure. The finite E binder only
bundles the two coefficient cases; it does not restrict Qbar, since the
bottom finite intermediate field always exists. Filtered diagrams are
nonempty by `IsFiltered`; the empty indexing category is correctly excluded
while the zero object is represented by a constant one-object diagram.
The pro-etale site retains its object/morphism size convention and Ab.{u+1};
no new universe equality or independent smaller test universe is imposed.

No STATEMENT-DISPUTED flag: the source agrees with the two stated clauses.
The existing statement's missing explicit isomorphism clause is an interface
omission repaired in Lean, not a correction of the natural-language node.

### Searches

- `msearch.py leanfinder`: "The full subcategory of the derived category with
  ind constructible cohomology is closed under isomorphisms and is triangulated".
  Eight hits: standard derived triangulated structures, t-structure, IsGE/IsLE,
  and bounded representatives; no theorem for this coefficient predicate.
- `msearch.py loogle`: "CategoryTheory.ObjectProperty.IsTriangulated,
  CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms". Twelve generic
  subcategory/localization/product hits; no specialized theorem. Source
  inspection confirms that the two classes express different clauses.
- `msearch.py grep`: "indConstructibleDerived|IsTriangulated.*ind|ind.*IsTriangulated"
  in CategoryTheory. Four induced-t-structure textual hits, no match.
- `rg` in the named upstream WeilConjectures tree: no occurrence of the
  node id or `indConstructibleDerived`. Searching shared `lean/Sheaf` finds
  only this item's existing module and original theorem. No second definition
  is introduced; its signature is retained and the missing clause is added
  to the same module. The added name has no existing declaration.
- Read `Mathlib.CategoryTheory.ObjectProperty.Ind` directly: existing `ind`
  already provides filtered ambient presentations and isomorphism invariance.
  Thus no new IndCons definition is needed.

### Validation

All compilation uses the prescribed `scompile.py` wrapper with one module,
two threads, nice 19 and the default 60-second per-file limit. The delivery
will be dry-run and pushed with `deliver2.py`; no direct Git command, live
source edit, or global build is used. The direct compiler run passed both the sandbox and library checks with
exit code 0 and no warnings. The library check reported 12.6 seconds; the
sandbox result included slot waiting. The dry-run result is recorded below.

`deliver2.py NE det-ambient-ind-derived-triangulated --no-push` passed:
"OK (dry run): commit 2fc86164d4 passes the preflight and compiles; nothing pushed".
The packet consists only of this module, its node record, and this report.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
