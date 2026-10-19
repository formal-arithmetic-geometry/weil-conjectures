## Worker report

The module states Stacks Project, Varieties, Tag 04KT
(`literature/stacks-project/varieties.tex`, lemma-finite-extension-geometrically-reduced,
lines 637–670), with a sorry proof. The source and node agree; no correction or new notion
is needed.

Hypothesis and clause correspondence:
- A field k: `(k : Type u) [Field k]`.
- The specified structure morphism Z → Spec k: `(Z : Scheme.{u})
  (f : Z ⟶ Spec (CommRingCat.of k))`.
- Locally of finite type: `[LocallyOfFiniteType f]`; no quasi-compactness hypothesis.
- Finitely many irreducible components: `[Finite (irreducibleComponents Z)]`.
- Existence of a field extension: `∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')`.
  Its inclusion is `algebraMap k k'`, injective because its source is a field.
- Finite: `Module.Finite k k'`.
- Purely inseparable: `IsPurelyInseparable k k'`.
- Base change: `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))`.
- Reduction: that scheme's `.nilradical.subscheme`, whose canonical immersion is
  `.nilradical.subschemeι`.
- Geometrically reduced over k': `GeometricallyReduced` applied to the composite of that
  immersion with `pullback.snd`. This is exactly reducedness after every field extension of
  k': Mathlib's `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` identifies it
  with those field base changes. The structure morphism is the canonical one, not an
  arbitrary map.

Dependency declarations read and used (Mathlib paths are under the pinned upstream checkout):
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: `IsPurelyInseparable`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.nilradical`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.IdealSheafData.subscheme`
  and `Scheme.IdealSheafData.subschemeι`.
- The geometric-reducedness clause of `def-pc-geometrically-irreducible` is explicitly
  recorded in its mathlib_match as `AlgebraicGeometry.GeometricallyReduced` in
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced`; this is the clause used here.

Recorded statement dependencies need no replacement. Available recorded proof modules are
imported without public visibility, including the affine-tensor comparison, presheaf module
stalks, localization, MakeSeparable, SeparableExtension and SeparablyGeneratedTensorReduced.
Other proof nodes without Lean records are described by id in the seven-step docstring.

Edge cases checked: Z may be empty (choose k'=k), nonreduced, disconnected, or not
quasi-compact. No reducedness or nonemptiness assumption was added. Characteristic zero is
included (pure inseparability then means the identity extension up to isomorphism); positive
characteristic allows the required finite inseparable extensions. All carriers share u, as
in Mathlib's scheme and geometric-property interface; any finite extension admits a model
in the universe of k, so the existential universe imposes no restriction. All variables and
the universe are explicitly bound; no local notation, auxiliary definition, or hidden let
occurs in the signature.

Searches for an existing statement:
- msearch LeanFinder: "A locally finite type scheme with finitely many irreducible components
  admits a finite purely inseparable extension making its reduced base change geometrically
  reduced". Eight hits, mainly algebraic geometric-reducedness criteria and normalization;
  none constructs the extension in this scheme statement.
- msearch Loogle: `"GeometricallyReduced"`. Twelve hits: the class, its base-change instances,
  and reducedness criteria. No extension-existence statement.
- msearch LeanSearch: "Finite purely inseparable extension makes the reduction of a locally
  finite type scheme geometrically reduced". Service unavailable: Internal Server Error.
- msearch Mathlib grep: `insepar.*[Rr]educ|[Rr]educ.*insepar|exists.*[Gg]eometrically`.
  Eight hits in purely inseparable field theory and an unrelated separation file; no match.
- rg in upstream WeilConjectures: `exists.*[Gg]eometric|finite.*[Ii]nsepar|04KT` and
  `lem-pur-finite-inseparable-geometric-reduction`. No matching theorem or blueprint id;
  related slicing/smooth-locus and geometric-Frobenius results have different conclusions.
- rg in project lean/Sheaf: `finite.*purely|purely.*finite|geometric.*reduc`. Related
  generic-radicial model and spreading statements require different data and conclusions;
  none is this field-extension theorem.

No STATEMENT-DISPUTED issue found. Server compile and delivery dry-run results are recorded
below when completed. Independent second reading is left to the designated second worker.

Validation: scompile.py compiled the module cleanly in 1.4 seconds, nice 19, two threads,
60 seconds per file. deliver2.py --no-push printed OK: the commit compiles and passes
preflight except for the second reading reserved for the second worker; nothing was pushed.

## Second reading by NJ

Independently read the item node, its statement dependencies and their recorded declarations,
then Stacks Varieties, Tag 04KT (`lemma-finite-extension-geometrically-reduced`, lines
637–670). The source introduces its own field and scheme morphism and assumes precisely local
finite type and finiteness of the irreducible-component set. The preceding generic-point
criterion does not impose another standing hypothesis. No statement correction is needed.

Object, hypothesis and conclusion checklist, in quantifier order:
- Base field k: `(k : Type u) [Field k]`. Exact; fields are nontrivial commutative fields.
- Scheme Z and its specified structure map to Spec k: `(Z : Scheme.{u})
  (f : Z ⟶ Spec (CommRingCat.of k))`. Exact; the node names this morphism, so the explicit-map
  convention applies. Read Mathlib `Spec` and its contravariant `Spec.map` in Scheme.lean.
- Locally of finite type: `[LocallyOfFiniteType f]`. Exact; the class in
  Morphisms/FiniteType.lean tests the finite-type ring map on affine open pairs. This is the
  recorded dependency's local cover condition, without quasi-compactness.
- Finitely many irreducible components: `[Finite (irreducibleComponents Z)]`. Exact;
  `irreducibleComponents` in Topology/Irreducible.lean is the set of maximal nonempty
  irreducible subsets. The Set-to-sort coercion makes this finiteness of the component set,
  rather than finiteness of each component or of the scheme's point set.
- A field extension k'/k, chosen after k, Z, f and the hypotheses:
  `∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), ...`. Exact. Read `Algebra` in
  Algebra/Algebra/Defs.lean: its unital ring homomorphism is `algebraMap k k'`, automatically
  injective for fields. No separate inclusion datum is needed.
- Finite extension: `Module.Finite k k'`. Exact; its `fg_top` says the vector space is
  finitely generated, equivalently finite dimensional. No bounded degree is imposed.
- Purely inseparable extension: `IsPurelyInseparable k k'`. Exact; read the class and
  `isPurelyInseparable_iff_pow_mem` (Stacks 09HE) in PurelyInseparable/Basic.lean. The same
  extension and algebra structure are used for finiteness and all subsequent clauses.
- Base change of Z along this extension: with
  `g = Spec.map (CommRingCat.ofHom (algebraMap k k'))`, the term is `pullback f g`.
  Exact; read `pullback` and `pullback.snd` in Shapes/Pullback/HasPullback.lean. The latter
  targets Spec k', not Z or Spec k.
- Reduction of that base change: `(pullback f g).nilradical.subscheme`, with its canonical
  inclusion `(pullback f g).nilradical.subschemeι`. Exact; read `Scheme.nilradical` as
  radical of the zero ideal sheaf in IdealSheaf/Basic.lean and `subscheme`, `subschemeι`
  in IdealSheaf/Subscheme.lean. This uses the dependency's construction, with no new object.
- Geometric reducedness over k': `GeometricallyReduced
  ((pullback f g).nilradical.subschemeι ≫ pullback.snd f g)`. Exact. Read the class in
  Geometrically/Reduced.lean and `geometrically` plus
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` in Geometrically/Basic.lean.
  These quantify over all field extensions of k' and require their pullbacks to be
  `IsReduced`. Read `IsReduced` in Properties.lean: it is reducedness of all rings of
  sections, equivalent to the reduced-stalk condition. The structure map is specifically
  the canonical composite. No conclusion about unreduced Z or its unreduced base change
  has been substituted.

Dependency audit: all nine statement dependencies are usable as recorded, including the
geometrically reduced clause of `def-pc-geometrically-irreducible` (not its irreducibility
clause). No new definition node or dependency module is delivered, so H12/H13 introduce no
additional obligations. Also read the available proof interfaces MakeSeparable,
SeparableExtension, SeparablyGeneratedTensorReduced, PresheafModuleStalkFunctor and the
finite affine tensor comparison, checking the square's scalar towers, field-generation
hypothesis, and tensor reducedness. They are proof imports, not extra hypotheses on this
statement. The declaration docstring follows all seven node proof steps: reduce, choose
generic points, identify their base-changed stalks, form the finite tower, make the next
field separable, preserve previous fields and compose extensions, then apply the generic
criterion. Unstated proof nodes are identified by their DAG ids. No data definition,
private notion, local notation, hidden let, or auxiliary proved theorem is introduced.

Edge cases: empty Z has zero components and admits k'=k; no nonempty binder excludes it.
Nonreduced Z is allowed and is reduced only after the displayed base change. Disconnected
and non-quasi-compact schemes with finitely many components are covered. There is no
numerical n parameter; the proof's n=0 case is the empty list. Characteristic zero and all
positive characteristics are included; in characteristic zero pure inseparability forces
the structural field map to be an isomorphism. The zero ring is correctly excluded only
as a base field, not as an affine chart of the empty scheme. All binders and universe u
are explicit. The field and scheme share Mathlib's universe; any pair can be placed in a
common universe, and a finite extension has a model in the base field's universe. The
geometric predicate tests fields in that universe, as the recorded dependency does;
reducedness over a larger extension is detected by finitely many coefficients in a small
finitely generated subextension, so this does not omit a geometric-reducedness case.

Independent duplicate searches used other wording than the worker's initial search:
- msearch LeanFinder: “A scheme locally of finite type over a field with finite irreducible
  components becomes geometrically reduced after taking its reduction over some finite
  radicial field extension”. Eight hits, including algebraic geometric-reducedness criteria,
  scheme reducedness/integrality, and normalization; no theorem constructing this extension.
- msearch Loogle: `"GeometricallyReduced"`. Twelve hits: the class, base-change instances,
  and reducedness consequences with existing geometric-reducedness hypotheses. None is
  this existential finite-extension statement.
- msearch grep: `radicial.*reduc|reduc.*radicial|exists.*purelyInseparable`. One hit,
  `IsPurelyInseparable.exists_pow_mem_range_tensorProduct`, which is a tensor power lemma.
- Direct rg over upstream WeilConjectures, project lean/Sheaf and Mathlib's algebraic
  geometry: `04KT|exists_finite_purelyInseparable_geometricallyReduced_reduction|
  finite.*radicial|inseparable.*geometrically|geometrically.*inseparable`. The upstream
  slicing/smooth-locus result assumes geometric reducedness; project radicial-model and
  shrinking statements concern spreading over a base. None is the item statement.

Verdict: no mismatch found; no Lean or node edits. The node's `lean.statement` was checked
verbatim against the theorem signature. The only theorem has a sorry proof; source and
blueprint docstrings and the 100-character width convention pass. Server scompile.py
compiled the delivered module cleanly in 1.3 seconds, nice 19, two threads, 60-second limit.
