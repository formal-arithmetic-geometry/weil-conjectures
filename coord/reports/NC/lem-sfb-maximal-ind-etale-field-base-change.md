## Worker report

The module `Sheaf.RingTheory.MaximalIndEtaleFieldBaseChange` states
`Algebra.finiteEtaleSubalgebraUnion_field_baseChange`, with one `sorry` theorem and
no new definitions. The node is unchanged outside `lean`.

Source read: `literature/stacks-project/more-algebra.tex`, Tags 0CKR–0CKU,
particularly `lemma-class-weakly-etale-over-field` (finite subalgebras),
`lemma-max-weakly-etale-subalgebra`, and
`lemma-change-fields-max-weakly-etale-subalgebra` (lines 30980 onward).
The theorem docstring gives all nine proof steps from the accepted DAG split,
including finite tensor supports and descent from an algebraic closure. The
source's occurrence of Q tensor_A L in its proof is interpreted as Q tensor_k L,
as already explained by the accepted split; no statement correction is needed.

Hypothesis and clause correspondence:

- Base field k: `(k : Type u) [Field k]`.
- Arbitrary commutative unital k-algebra A: `(A : Type v) [CommRing A]
  [Algebra k A]`. There is no `Nontrivial A` assumption.
- Arbitrary field extension L/k: `(L : Type w) [Field L] [Algebra k L]`.
  The universes u, v, w are independent and explicitly declared.
- B_k(A), the union of finite étale unital subalgebras, is the existing
  `Algebra.finiteEtaleSubalgebraUnion k A`. Its actual definition is
  `sSup (finiteEtaleSubalgebras k A)`; the recorded dependency theorem says its
  underlying set is exactly the requested set-theoretic union. The defining
  finite-stage condition is `Module.Finite k D ∧ Algebra.Etale k D`, the same
  affine condition as `IsFinite (Spec.map ...) ∧ Etale (Spec.map ...)`.
- The induced inclusion after tensoring is the specific Mathlib map
  `Algebra.TensorProduct.map (finiteEtaleSubalgebraUnion k A).val
  (AlgHom.id k L)`. Its value on `b ⊗ l` is `b.val ⊗ l`; no arbitrary map or
  abstract isomorphism replaces this inclusion.
- Identification of the source with a subalgebra is `Function.Injective` of
  this map. Identification with the specified target is equality of its
  `Set.range` with the carrier of `finiteEtaleSubalgebraUnion L (A ⊗[k] L)`.
  Together these say precisely that this canonical map is an isomorphism onto
  that included subalgebra. Although `map` is bundled over k, its tensor formula
  automatically commutes with right-factor L-scalars, hence this is the
  asserted L-algebra identification.
- The L-algebra structure of the ambient tensor is passed explicitly as
  `TensorProduct.rightAlgebra` in the fully applied target definition, rather
  than relying on a file-local instance or changing tensor order. This is the
  structure `l ↦ 1 ⊗ l` specified by the node.
- The last sentence imposing no finite-generation, reducedness or dimension
  restriction is respected: none occurs in the binders.

Recorded statement dependency declarations read and reused:

- `Field`, `Mathlib.Algebra.Field.Defs`, the commutative division-ring class.
- `Algebra`, `Mathlib.Algebra.Algebra.Defs`, the unital central scalar map;
  with the two Field instances it is exactly a field extension.
- `AlgebraicGeometry.Spec` and `Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`.
- `AlgebraicGeometry.IsFinite`, `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `AlgebraicGeometry.Etale`, `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Algebra.finiteEtaleSubalgebras`, `Algebra.finiteEtaleSubalgebraUnion`, and
  `Algebra.finiteEtaleSubalgebra_directed_union`,
  `Sheaf.RingTheory.FiniteEtaleSubalgebraUnion`. Its module publicly imports the
  recorded Mathlib scheme-property modules; the delivered module publicly
  imports it. No dependency interface needs repair.
- The tensor map and the explicitly passed right-factor algebra structure are
  Mathlib's `Algebra.TensorProduct.map` (TensorProduct.Maps) and
  `Algebra.TensorProduct.rightAlgebra` (TensorProduct.Basic).

The imports also include all recorded proof-dependency modules, as plain imports:
IndEtaleUniverseTransport, IndEtaleStability, WeaklyEtaleField, Flat.Basic,
Basis.VectorSpace, Separable, SeparableClosure, GroupScheme.Defs,
FiniteSeparableClosure, SeparableTensorAlgebraicClosure, Geometrically.Integral,
WeilConjectures.Mathlib.AlgebraicGeometry.Scheme, FiniteType,
ReducedNoetherianTotalRingFractions, and IsAlgClosed.AlgebraicClosure.
`lem-sfb-ind-etale-core-ring-operations` currently has no recorded module; its
five clauses are referenced in the proof docstring and its import can be added
when it is stated. It is only a proof prerequisite, not an object missing from
this statement.

Edge cases checked mathematically before writing:

- A = 0: its only subalgebra is zero, which is finite étale (the empty product).
  Both tensor products are zero, the map between singleton carriers is
  injective, and both sides of the image equality are the singleton carrier.
- L = k: the usual right-unit tensor identification recovers B_k(A) inside A.
- A = k: the source core is k and the extended core is L.
- A = k[e]/(e²): the nilpotent contributes no new finite étale elements; the
  cores are k and L. Thus reducedness is not accidentally assumed.
- Finite products, including the empty product, are allowed. Purely inseparable
  extensions L/k and positive characteristic are not excluded by the binders.
- Infinite-dimensional A and transcendental or infinite L/k remain quantified;
  there is no finite type or algebraicity assumption and no universe equality.

Searches actually run with `batch2/msearch.py NC
lem-sfb-maximal-ind-etale-field-base-change`:

- leansearch: `The maximal ind etale subalgebra commutes with extension of the
  base field`. Eight hits: Etale.baseChange, RingHom.Etale.isStableUnderBaseChange,
  the scheme base-change instance, and ordinary étale classification/definitions.
  None constructs or compares the maximal union.
- leanfinder: `The maximal ind etale subalgebra of an algebra over a field
  commutes with arbitrary field extension`. Eight hits: Etale.comp,
  Etale.baseChange, Etale.exists_subalgebra_fg, RingHom.etale_algebraMap,
  formally étale/separable criteria, and étale finite-product classification.
  These are not this maximal-subalgebra statement.
- loogle: `"Etale", "TensorProduct"`. Five hits: formally étale and standard
  étale tensor instances, étale faithfully flat descent, finite splitting after
  étale extension, and the weakly étale tensor instance. No union comparison.
- grep of Mathlib RingTheory:
  `([Mm]ax.*[Ee]tale|[Ee]tale.*[Ss]ubalgebra|[Ss]ubalgebra.*[Ee]tale)`.
  Three hits: an unrelated maximal-spectrum line in Etale.Field and the
  finite-type coefficient descent theorem in Smooth.NoetherianDescent.
- rg of `lean/WeilConjectures` and `lean/Sheaf`:
  `finiteEtaleSubalgebra|[Mm]ax.*[Ii]nd.*[Ee]tale|[Mm]ax.*[Ww]eak`.
  The only union implementation is the dependency FiniteEtaleSubalgebraUnion;
  other matches are weakly étale local-ring or universe infrastructure. The
  EtaleComponents docstring cites this item but does not state its algebraic
  base-change comparison.
- grep of the exact item id in `lean/WeilConjectures`: no hits.

Validation: the prescribed scompile.py compiled this file separately as a
sandbox module and at its library module path, both cleanly (1.6 seconds each).
No additional helper, new node, dependency module or statement correction is
necessary. No STATEMENT-DISPUTED issue was found.

## Second reading by NC

The dispatcher expressly forbids starting another agent, so this is a separate
rereading by the same worker; the maintainer's independent delivery review is
still required. I reopened the node and final signature and checked each binder
and both conclusion clauses. The node's k, A, L and two scalar maps correspond
to the explicit types and five class binders, and A = 0 is admitted. The source
of `TensorProduct.map` is exactly B_k(A) tensor_k L because its left homomorphism
is the recorded subalgebra inclusion and its right homomorphism is the identity
of L. Its target is A tensor_k L. Injectivity plus the carrier equality is the
specified identification inside that same target, rather than an unrelated
algebra equivalence. I checked rightAlgebra's definition in TensorProduct.Basic:
its scalar map is includeRight and its scalar action multiplies by 1 tensor l,
so the target union is over L. The source map's tensor formula respects that
same action. The node places no other hypotheses on A or L and none are added.
The dependency's supremum-versus-union distinction is already settled by its
recorded theorem. No mismatch or change was found on rereading.
