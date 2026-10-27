## Worker report

The module `Sheaf.AlgebraicGeometry.MarkedRadicialCompactification` states
`AlgebraicGeometry.exists_marked_radicial_compactification`, with `sorry` as its entire proof.
There are no new definitions, dependency repairs, or statement changes. The module docstring
names ILO Expose X 2.3 Step 1, printed p.150, and Stacks Tags 04KT and 01S4. The theorem docstring
carries all eight proof steps of the reviewed node, including the finite-dimensional residue-field
argument. I read ILO printed p.150 directly with pdftotext (PDF page 156), and the full statement
and relevant proof of `lemma-finite-extension-geometrically-reduced` in varieties.tex.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`; the scheme is `X : Scheme.{u}` with `[Nonempty X]`.
  Its k-structure is the explicit morphism `f : X ⟶ Spec (.of k)`.
- Separatedness is `[IsSeparated f]`; finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`.
  These are precisely the recorded dependency conventions, with no extra base hypothesis.
- The marking is `Z : Set X`, with `hZ : IsClosed Z` and `hZnd : interior Z = ∅`.
  For a closed subset, empty interior is exactly nowhere density.
- `∃ Xbar fbar j` supplies the compactification and its structure map. `IsProper fbar` and
  `LocallyOfFiniteType fbar ∧ QuasiCompact fbar` render proper and finite type explicitly.
  `IsOpenImmersion j ∧ DenseRange j ∧ j ≫ fbar = f` renders the dense open immersion over k.
- `∃ C : Set Xbar, IsClosed C ∧ interior C = ∅ ∧ j ⁻¹' C = Z` gives the closed nowhere dense
  extended marking and its restriction. The separate conjunct `C = closure (j '' Z)` records
  the specified choice as the closure, rather than merely some extended marking.
- `∃ (e : Type u) (_ : Field e) (_ : Algebra k e)` gives the extension; `Module.Finite k e`
  and `IsPurelyInseparable k e` are the finite and purely inseparable requirements.
  `ringChar k = 0 → Function.Surjective (algebraMap k e)` says the extension is trivial in
  characteristic zero. A field hom is injective, so surjectivity identifies e with k as a
  k-algebra; literal equality between different carrier types is not imposed.
- The concluding lambda is applied to exactly
  `T = (pullback fbar (Spec.map (CommRingCat.ofHom (algebraMap k e)))).nilradical.subscheme`,
  to its canonical e-structure `b = nilradical.subschemeι ≫ pullback.snd ...`, and to its
  canonical map `t = nilradical.subschemeι ≫ pullback.fst ...`. The lambda only avoids
  repeating these expressions in every clause; beta reduction gives the statement entirely
  in terms of Mathlib's canonical constructions. There is no chosen map or unspecified model.
  The required k-linearity is the pullback condition composed with the reduction inclusion.
- `Nonempty T ∧ IsProper b ∧ LocallyOfFiniteType b ∧ QuasiCompact b ∧ GeometricallyReduced b`
  gives all five assertions about the reduced constant model over e.
- `IsFinite t ∧ IsHomeomorph t.base ∧ UniversallyInjective t` gives finite, homeomorphic on
  underlying spaces, and radicial. The last equivalence is the recorded Stacks 01S4 match.
- `Set.BijOn t {η | ∃ D ∈ irreducibleComponents T, IsGenericPoint η D}
  {η | ∃ D ∈ irreducibleComponents Xbar, IsGenericPoint η D}` says that the actual map t
  bijects component generic points. This includes both preservation and surjectivity.
- For every component D and its generic point η, `(t.residueFieldMap η).hom.Finite` and
  `(t.residueFieldMap η).hom.IsPurelyInseparable` give the finite purely inseparable extension
  of the actual residue fields, along the map induced by t.
- `IsClosed (t ⁻¹' C) ∧ interior (t ⁻¹' C) = ∅` gives the inverse marking assertion.
- `IsNoetherian Xbar ∧ IsNoetherian T` uses Mathlib's class extending `IsLocallyNoetherian`
  and `CompactSpace`; the two `(irreducibleComponents ...).Finite` clauses give finite
  numbers of components for both schemes.

Dependency interfaces read and used (full signatures and docstrings, not just names):

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`, respectively in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `def-weil-proper-morphism`: `IsProper`, `IsSeparated`, and `UniversallyClosed`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its public imports. IsProper includes
  locally finite type, while universally closed implies quasi-compact.
- `def-weil-open-immersion`: `IsOpenImmersion`, `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-pc-field-tower`: import `Sheaf.FieldTheory.FieldTower`; its docstring explicitly
  assigns finite and purely inseparable extensions to Mathlib's `Module.Finite` and
  `IsPurelyInseparable`. Its recorded main declaration `FieldExtension.degree` is not needed
  to assert finiteness. `Mathlib.FieldTheory.PurelyInseparable.Basic` supplies the latter class.
- `def-pc-fibre-product`: `pullback`, `pullback.fst`, and `pullback.snd` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-pbc-scheme-reduction`: `Scheme.nilradical`, `IdealSheafData.subscheme`, and
  `IdealSheafData.subschemeι`, in `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` and `.Subscheme`.
- `def-pc-geometrically-irreducible`: import its recorded module
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`, using the recorded companion class
  `GeometricallyReduced` (defined in `.Geometrically.Reduced`) on b.
- `def-weil-finite-integral-morphism`: `IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-weil-radicial-morphism`: the mathlib_match `UniversallyInjective` and its equivalence
  `tfae_universallyInjective` in `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`.
- `def-weil-irreducible-components`: `irreducibleComponents`, `Mathlib.Topology.Irreducible`.
- `def-sc-generic-point`: `IsGenericPoint`, `Mathlib.Topology.Sober`.
- `def-weil-residue-field`: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField`.
- `pqf-def-locnoeth`: `IsLocallyNoetherian`, used through `IsNoetherian` in
  `Mathlib.AlgebraicGeometry.Noetherian`.

All recorded proof dependency modules are present as plain imports when they are not already
public statement imports: Nagata's `WeilConjectures.Compactification.Dense`,
`Sheaf.Compactification.BoundaryRefinement`,
`Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction`,
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`,
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`, and
`WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`, together with the
Mathlib permanence/localization modules. Mathlib leaves are available from these and the
public dependency imports. No dependency waits or import cycles were introduced.

Edge cases checked before writing:

- Z empty: its image and closure are empty; both inverse markings are empty.
- X already proper: the identity compactification is allowed.
- Nonreduced X, including Spec of dual numbers: the initial compactification need not be
  reduced. T is the actual reduction after base change. Its map to Xbar remains finite
  because reduction of a Noetherian scheme is a closed immersion.
- Dimension zero and several components: the generic-point sets and finite-component clauses
  remain literal; no integrality or connectedness assumption was added.
- Characteristic zero: pure inseparability is trivial; the explicit surjectivity clause
  renders e=k up to the required algebra identification. No positive-characteristic hypothesis.
- Imperfect fields: a nontrivial finite purely inseparable extension is allowed; geometric
  reducedness is asserted after that extension, not prematurely over k.
- Empty X is excluded exactly as in the node. No conclusion or intermediate encoding requires
  additional nonemptiness of an index set. All schemes and fields share the common ambient
  universe u; any particular field/scheme pair can be raised to this ambient universe.

Searches made with the prescribed msearch.py wrapper on 2026-10-24:

- LeanFinder: "A separated finite type scheme over a field has a dense proper compactification
  with a nowhere dense closed marking and geometrically reduced reduction after finite purely
  inseparable extension". Eight results, including finite_appTop_of_universallyClosed and
  compactSpace_of_universallyClosed; none states this construction with all clauses.
- Loogle: "AlgebraicGeometry.IsProper, AlgebraicGeometry.GeometricallyReduced". Zero hits.
- Mathlib grep: "compactification|marked.*radicial|geometricallyReduced_reduction" in
  AlgebraicGeometry. Zero hits.
- LeanSearch: "A separated finite type scheme over a field admits a dense proper compactification
  whose reduced base change along some finite purely inseparable field extension is geometrically
  reduced". Eight hits about IsProper and IsSeparated; no complete match.
- rg of both live `lean/WeilConjectures` and `lean/Sheaf`:
  `marked.radicial|MarkedRadicial|markedRadicial|geometricallyReduced_reduction|exists.*compactification`.
  Found dense compactification and geometric reduction separately, and the stronger downstream
  ProperPairRadicialPreparation statement. None is this statement. The latter is not a dependency
  and is not imported. `grep -rn 'lem-sfb-marked-radicial-compactification' lean/WeilConjectures`
  found no existing declaration carrying this node.
- Additional rg for definitions of reduced base change/reduced constant extensions found no
  reusable generic construction. No helper is introduced: the existing pullback and nilradical
  constructions are applied directly.

Validation: scompile.py compiled the single module in both sandbox and library modes without
errors or non-sorry warnings. The dry run and delivery below recheck the final header and record.

## Second reading by Q108

I reopened the item node and the complete Lean statement for a separate clause-by-clause rereading.
The dispatcher explicitly forbids starting another agent; this is a same-worker rereading, and
maintainer independent review remains part of delivery. Every clause is mapped above. In particular
I checked that `pullback.snd` supplies the e-structure while `pullback.fst` supplies the map to
Xbar; both are composed with the actual nilradical inclusion. The finite residue-field extensions
use that map rather than an arbitrary algebra structure. I checked preservation as well as
surjectivity in `Set.BijOn`, closure equality for C, both finite-type clauses, both Noetherian
clauses, and both finite-component clauses. All existentials precede the clauses that use their
instances. The lambda is an ordinary beta-reducible expression with no let/have binder and no
hidden hypotheses. No mathematical mismatch was found and no statement was changed. The only
header adjustment after the first successful compile was explicitly listing the finite-type,
finite-morphism, and pullback dependency imports already available transitively.
