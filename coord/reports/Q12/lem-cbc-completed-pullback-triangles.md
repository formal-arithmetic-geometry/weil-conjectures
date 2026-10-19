## Worker report

The module `Sheaf.Paper.CompletedPullbackTriangles` states the node as the theorem
`AlgebraicGeometry.Scheme.completedPullback_preserves_shifts_distinguished`.  It
uses the published strict-tower completed pullback
`pbcActualCompletedPull g d` and the published intrinsic-completeness predicate
`PbcIsIntrinsicallyComplete`.

The Lean statement renders the source clauses as follows.  `A : Type (u + 1)`
with `[CommRing A]`, `X Y : Scheme.{u}`, `g : X ⟶ Y`, and
`d : AdicCoefficientDatum A` are the fixed coefficient datum and arbitrary
scheme morphism.  The existential `h : (pbcActualCompletedPull g d).CommShift ℤ`
is the family of natural shift isomorphisms for every integer shift; the
`CommShift` structure includes the unit, composition, and naturality identities.
For every `T : Triangle (PbcCompletedDerived Y d)`, the hypothesis
`T ∈ distTriang _` is the ambient distinguished-triangle hypothesis.  The
three successive hypotheses on `T.obj₁`, `T.obj₂`, and `T.obj₃` are precisely
that all three vertices are intrinsically derived complete.  The conclusion
`(pbcActualCompletedPull g d).mapTriangle.obj T ∈ distTriang _` says that the
image triangle, whose final map uses the shift comparison supplied by `h`, is
distinguished in the target ambient derived category.  There are no
constructibility, Noetherianity, or scheme-finiteness binders.

The dependency declarations used are:

- `Sheaf.Paper.AdicCoefficientDatum`,
  `AlgebraicGeometry.Scheme.completedReductionTower` (the canonical strict
  reduction-tower derived functor and its coefficient datum).
- `Sheaf.Paper.PbcActualStrictPullback`,
  `AlgebraicGeometry.Scheme.pbcActualStrictCompletedPull` and
  `AlgebraicGeometry.Scheme.pbcActualCompletedPull` (the specified strict-tower
  composite and its completed pullback interface).
- `Sheaf.Paper.IntrinsicCompletionCompleted`,
  `AlgebraicGeometry.Scheme.IsCompletedIntrinsicallyDerivedComplete` (the
  explicit derived-completeness unit notion; the ambient published predicate
  used in the theorem is imported through the completed-pullback module).
- The Mathlib declaration recorded for `def-weil-triangulated-category` is
  `CategoryTheory.Pretriangulated` in
  `Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean`; the statement uses
  Mathlib's `CategoryTheory.Pretriangulated.Triangle`, `distTriang`, and
  `Functor.CommShift` interfaces.

Edge cases checked against the statement and its definitions: the identity
morphism gives the completion functor with its existing normalized shift;
zero and split distinguished triangles map to zero and split triangles; positive,
zero, and negative integer shifts are covered by `CommShift`; the empty scheme
is allowed by the recorded intrinsic-completeness predicate; and both
`I = 0` and `I = A` remain admitted by the adic datum (the latter gives the
zero completed coefficient situation).  No hypothesis about constructibility
or Noetherianity was introduced.

Searches made:

- `msearch.py ... leanfinder "completed pullback preserves shifts and distinguished triangles"`:
  generic Mathlib hits (`Functor.IsTriangulated.map_distinguished`,
  `Functor.CommShift`/pullback-shift interfaces), but no specified completed
  pullback theorem.
- `msearch.py ... loogle "Functor.IsTriangulated, Functor.CommShift, mapTriangle"`:
  no Loogle hits (the query names are not recognized there).
- `msearch.py ... grep "completedPullback.*Triangulated" Mathlib/CategoryTheory`:
  zero hits.
- `rg` over `WeilConjectures/` and the existing `lean/Sheaf` tree for
  `completedPullback_preserves_shifts_distinguished`, completed-pullback
  triangulated assertions, and the item id found no duplicate declaration.
  The existing strict-pullback and inverse-limit modules provide the
  construction, but no statement of this triangle-preservation result.

The theorem proof is intentionally `sorry`; this delivery supplies only the
stage-2 statement and its source/docstring, as required.

## Second reading by Q12

Independent maintainer second reading of immutable delivery
`d2d4bed24b5fb9af92298949f56240c0b300ea05`, performed on 2026-10-17.
The worker section above is retained; this section replaces its placeholder.

Clause-by-clause reading:

- The arbitrary scheme morphism is `g : X ⟶ Y`, with no geometric finiteness
  assumptions. `A : Type (u + 1)`, `[CommRing A]`, and
  `d : AdicCoefficientDatum A` supply precisely the Noetherian adic hypotheses.
  I opened the inherited `CompleteCoefficientDatum` fields: ideal, Noetherianity,
  finite generation, additive torsion of A/I, and perfect positive quotients;
  `quotientFinite` supplies their finiteness. No completeness of A is assumed.
- `PbcCompletedDerived Y d` is the ambient derived category of modules over
  the actual inverse-limit ring sheaf on the small pro-etale site. It is not
  the subcategory of complete objects or a constant-coefficient derived category.
- I read `pbcActualStrictCompletedPull`, the coefficient map and tower pullback
  in `CompletedTowerPullback`, and the derived-limit interface. The former is
  exactly reduction followed by derived tower pullback followed by derived limit.
  `pbcActualCompletedPull` is the ordinary-pullback/completion-reflector
  presentation. The imported recorded dependency theorem
  `pbcActualCompletedPullback_tower` gives the unique natural unit-compatible
  isomorphism between their restrictions to intrinsically complete inputs.
  This is an acceptable canonical presentation of the same functor, not an
  arbitrary substitute. The expanded docstring makes this transport explicit.
- `PbcIsIntrinsicallyComplete` existentially packages generators of the ideal
  and a complex representative, transporting through the normalized ring
  comparison and testing `IsCompletedIntrinsicallyDerivedComplete`. That last
  predicate is invertibility of the explicit Koszul completion unit. No
  constructibility conditions accompany it.
- `∃ h : (pbcActualCompletedPull g d).CommShift ℤ` provides natural integer
  shift isomorphisms with zero and addition coherence. Its ambient formulation
  uses the canonical extension already supplied by this dependency interface;
  restricting it gives the claimed comparisons on complete objects.
- `T : Triangle (PbcCompletedDerived Y d)` and `T ∈ distTriang _` express an
  ambient distinguished triangle. All three vertex completeness hypotheses
  appear separately. The local instance argument `(shift := h)` ties the
  conclusion to exactly the same shift structure. Mathlib's `mapTriangle`
  has final arrow `F.map T.mor₃ ≫ (F.commShiftIso 1).hom.app T.obj₁`.
  Thus both the final-arrow clause and target distinguishedness are present.

Sources read: Stacks proetale.tex, lemma-pushforward-Noetherian-case (099N),
clauses (2),(5); derived.tex, proposition-derived-functor (05SE);
sites-cohomology.tex, lemma-derived-limit-is-ok (0941); and the blueprint
`thm-cbc-finite-extension.md`. The latter explains the compact-support use;
the node explicitly assembles the strict-tower exactness assertion from the
more general derived-functor results. No scheme Noetherianity is required.
I read all four statement dependency nodes and their exact interfaces, and
also the resolving-class, diagram-replacement and Rlim proof dependency statements.
The proof-dependency list equals the union of the step uses.

Edge cases: all integer shifts, including 0 and negative shifts; zero/split
triangles; identity morphisms; empty schemes; the zero ring; the unit ideal;
and the zero ideal, subject to the coefficient datum's finiteness conditions.
The empty generator tuple is allowed. Tower index 0 denotes positive exponent 1,
not the missing quotient A/I^0. Scheme universe u and coefficient universe u+1
are the published size convention, retaining site object/Hom universes u+1/u.
No equality between those site universes or further typeclass hypothesis is added.

Independent searches with `rg` across the group's `lean/Sheaf` and
`lean/WeilConjectures`, the older upstream `WeilConjectures`, and Mathlib's
category-theory tree used completed pullback, shift, distinguished and
IsTriangulated combinations. There is no existing theorem for this specified
completed-ring functor. Principal/integral completion, etale operations, scalar
extension and generic triangulated functor results have different scope.
The 51-module pro-etale framework documentation was read in the group clone;
no condensed or etale replacement is used here.

Findings and corrections: H11, the delivered second-reading section contained
only a disclaimer. It is replaced by this actual independent reading. H8/H9,
the proof plan was compressed and did not spell out the presentation transport
or import the three proof tools directly; the replacement Lean file expands
the four steps and supplies their imports. The theorem signature and node
statement are unchanged. No new notion, helper, dependency-record repair or
source-based statement correction is needed.

Compiler evidence: the immutable module was checked with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q12
lem-cbc-completed-pullback-triangles <absolute immutable Lean path>`.
The wrapper reported sandbox success in 2.0 s and library success in 2.3 s,
with no errors or warnings. The current wrapper runs the overlay on the server;
this is its current implementation, rather than a claim of a local compiler run.
The corrected module also passed through the same wrapper under its actual
`Sheaf/Paper/CompletedPullbackTriangles.lean` module name: sandbox 4.3 s,
library 2.3 s, no errors or warnings. No global build or live Lean edit was run.
The immutable `lean.statement` matches the signature verbatim, and the corrected
file preserves it; all lines are within 100 characters and the only proof is
`by sorry`.
