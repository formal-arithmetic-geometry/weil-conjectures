## Worker report

The delivery adds `Sheaf.AlgebraicGeometry.QcqsZeroDimensionalAffine`, with the single
statement `AlgebraicGeometry.isAffine_of_qcqs_of_t1`. Its proof is exactly `sorry`.
Only the item's `lean` field changes. The accepted NR stage-1 split is preserved.
The previous worker's stale-assignment diagnosis concerned splitting again: the
live item is split and reviewed, but has no Lean record, so this stage-2 task remains.

I read Stacks `literature/stacks-project/properties.tex`, Tag 0CKV,
`lemma-dimension-zero`, its statement and full proof. Its final assertion gives
precisely the node's affine conclusion for a quasi-compact quasi-separated scheme
whose points are closed. Nothing here changes the unit, node statement or proof route.
No statement correction, missing notion, dependency repair or statement dispute arises.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme is `(X : Scheme.{u})`, with `universe u` explicitly bound.
- Quasi-compactness is `[CompactSpace X]`; Mathlib compactness imposes no Hausdorff
  condition. This is the recorded declaration of def-weil-pbc-quasi-compact-scheme.
- Quasi-separatedness is `[QuasiSeparated (terminal.from X)]`, exactly the recorded
  def-weil-quasi-separated-morphism applied to the terminal structural morphism.
  `quasiSeparatedSpace_iff_quasiSeparated X` also identifies its spatial form.
- Every point being closed is `[T1Space X]`. I read the definition in Mathlib,
  `Topology/Separation/Basic.lean:347`: its sole field is
  `t1 : ∀ x, IsClosed ({x} : Set X)`. No discreteness or finiteness is asserted.
- The parenthetical dimension-at-most-zero is an equivalent description of this
  hypothesis for a scheme; the node's primary all-points-closed form is used, without
  adding a second hypothesis. The recorded `topologicalKrullDim` module is imported.
- Affineness is `IsAffine X`. I read `AffineScheme.lean:59-69`: this class says the
  canonical `X.toSpecΓ` is an isomorphism, and `Scheme.isoSpec X` supplies exactly
  `X ≅ Spec Γ(X, ⊤)`. Thus the node's commutative ring and spectrum isomorphism are
  present with the canonical ring of global sections; they are not extra assumptions.
- The empty scheme is allowed: there is no `Nonempty X` or nontrivial-ring hypothesis.
- There is no Noetherian, finite-type, reducedness, separatedness, Hausdorffness,
  finite-space or discrete-topology assumption. `u` is arbitrary.

Dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`,
  including its full local-affine field and docstring.
- def-weil-pbc-quasi-compact-scheme: `Mathlib.Topology.Defs.Filter`, `CompactSpace`,
  its docstring and `isCompact_univ` field, imported through QuasiSeparated.
- def-weil-quasi-separated-morphism: `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated`, with its quasi-compact diagonal field.
- def-kun-topological-krull-dimension: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, defined as `Order.krullDim (IrreducibleCloseds T)`.

All stated proof dependencies are imported, directly or through the public statement
imports. I read their records and the declarations used in the plan:
`isCompact_iff_finite_and_eq_biUnion_affineOpens` (Mathlib QuasiCompact),
`Ideal.exists_le_maximal` (Mathlib Ideal.Maximal), `Spec` (Mathlib Scheme),
`Spec.profinite_of_isMaximal` (Sheaf ZeroDimensionalSpectrumProfinite),
`Scheme.compactSpace_of_isAffine` (Mathlib AffineScheme),
`quasiSeparatedSpace_of_isAffine` (Mathlib QuasiSeparated),
`compactSpace_inter_of_quasiSeparated` (Sheaf QuasiCompactOpenIntersection),
`IsClosedImmersion` and `IsClosedImmersion.iff_isPreimmersion` (Mathlib ClosedImmersion),
and `isAffine_of_finite_closed_cover` (WeilConjectures IsAffineOfFiniteClosedCover).
The declaration docstring reproduces all six accepted proof steps with their node ids.

Edge cases checked before writing: Spec of the zero ring has no points, satisfies
all hypotheses and is affine. Spec of the dual numbers over a field retains
nilpotents and satisfies the statement, so no reducedness is imposed. Spec of the
infinite product of copies of F₂ has an infinite profinite space; it is covered by
the statement without any finite or discrete topology assumption. An infinite
disjoint union of points illustrates the need for quasi-compactness; gluing two
profinite spectra along a non-quasi-compact open illustrates the need for
quasi-separatedness. Neither hypothesis follows for arbitrary schemes.

Actual searches made in this session:

- msearch.py LeanFinder: `A quasi compact quasi separated scheme whose points are all
  closed is affine`. Eight hits included `IsAffine`, quasi-affine predicates and
  quasi-separatedness criteria, but none states this affineness theorem.
- msearch.py Loogle: `AlgebraicGeometry.IsAffine, T1Space`. Zero hits.
- msearch.py grep in AlgebraicGeometry:
  `IsAffine.*T1Space|T1Space.*IsAffine|isAffine.*[Zz]ero|[Zz]ero.*isAffine`.
  Fifteen hits concern zero loci or maps becoming zero, not this assertion.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id, T1/affineness,
  zero-dimensional/affineness, `topologicalKrullDim`, and the chosen declaration name.
  No exact existing assertion or name collision. Read the existing finite-discrete
  affine theorem: it requires finite/discrete topology and is not a match. The
  zero-dimensional spectrum result starts with an affine spectrum, so it is not
  the desired theorem for an arbitrary scheme.
- Read `dag/lean_names_upstream.json` search results and the node's prior searches;
  no exact match. The requested CompactObject example is now withdrawn; I also
  read its recorded upstream replacement and its full node record.

Validation: scompile.py compiled both its sandbox and library checks with no errors
or warnings (2.8 s and 3.2 s respectively). Every theorem proof remains `sorry`.

## Second reading by NB

This is this worker's separate final reading, not a claim of an independent agent
review. The dispatcher explicitly forbids starting other agents; the maintainer's
independent delivery review supplies that check.

With the live node and complete delivered module open, I checked each binder and
conclusion again. `Scheme.{u}` covers the given object without restricting its size;
`CompactSpace X` is exactly quasi-compactness; the terminal-map `QuasiSeparated`
class is precisely the node's scheme notion; `T1Space` has exactly the closed-singleton
field, with no stronger topology condition. `IsAffine X` yields the spectrum of the
commutative global-section ring, including the zero ring. The dimension clause is
parenthetical equivalence, not a separate conclusion or extra assumption. The absence
of `Nonempty`, Noetherian and finite-type binders preserves the three express scope
clauses. No mismatch was found, so nothing changed in this final reading. There are
no new nodes or dependency modules. The independent reviewer should check these
same identifications and the six-step source docstring.
