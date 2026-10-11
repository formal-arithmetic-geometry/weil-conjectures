## Worker report

The delivery defines `IsSupportedOn` and `supportedDerivedQCohProperty` in
`Sheaf.AlgebraicGeometry.SupportedDerivedCategory`, then states
`AlgebraicGeometry.supported_perfect_generator` in
`Sheaf.AlgebraicGeometry.SupportedPerfectGenerator`. The theorem takes a
quasi-compact, quasi-separated scheme, a closed subset and quasi-compact open
complement, and produces the triangulated structure and a perfect weak generator
of the supported quasi-coherent derived subcategory. The explicit witnesses for
zero object, shift, preadditivity, additive shifts, pretriangulation, and
triangulation render the triangulated-category clause; `hsub` renders the
supported full subcategory's triangulated structure; `Scheme.IsPerfect` renders
perfectness and `IsWeakTriangulatedGenerator` renders generation. The proof is
`sorry` as required.

Dependencies used: `Sheaf.AlgebraicGeometry.DerivedCategory` declarations
`schemeDerivedCategory` and `schemeDerivedQCohCategory`; `Sheaf.AlgebraicGeometry.PerfectComplex`
declaration `AlgebraicGeometry.Scheme.IsPerfect`; `Sheaf.CategoryTheory.WeakTriangulatedGenerator`
declaration `CategoryTheory.IsWeakTriangulatedGenerator`; Mathlib
`CategoryTheory.ObjectProperty.FullSubcategory`, `CategoryTheory.Pretriangulated`,
`CategoryTheory.IsTriangulated`, `Topology.IsClosed`, and `AlgebraicGeometry.QuasiCompact`.

Edge cases checked include empty support (`T = ∅`, whose complement is all of X),
full support (`T = Set.univ`, empty complement), and the empty open complement.
Searches used `rg` over `lean/Sheaf` and the source checkout for support and
perfect-generator declarations, plus Mathlib grep for supported derived objects;
no existing declaration matching the theorem was found. The dependency notion
`def-pc-supported-derived-category` was missing a Lean declaration, so its new
module is included in this delivery.

## Dependency modules

`def-pc-supported-derived-category`: no existing declaration stated the supported
subcategory notion. The module defines restriction-to-the-open-complement support
and the corresponding full-subcategory property.

## Earlier second reading (a previous round; superseded)

Read the node and both modules. The hypotheses `X` quasi-compact and
quasi-separated, `T` closed, and quasi-compact complement are rendered directly.
The conclusion's triangulated supported subcategory, single perfect object, and
weak-generator clauses are each present; the explicit categorical witnesses make
all ambient structures required by the Lean definitions visible.

## New nodes

`def-pc-supported-derived-category` adds the missing supported-object notion.

## Second reading by E1

Step 1 list and verdicts against the node statement:

1. `X` is a scheme, rendered as `X : Scheme.{u'}`; the required quasi-compact and
   quasi-separated hypotheses are `[CompactSpace X]` and `[QuasiSeparatedSpace X]`.
   Verdict: same hypotheses (the project convention records these properties this way).
2. `T` is a closed subset of `X`, rendered as `(T : Set X)` with
   `hT : IsClosed T`; its quasi-compact open complement is rendered by
   `hTqc : QuasiCompact (Scheme.Opens.ι ⟨Tᶜ, IsClosed.isOpen_compl⟩)`. Verdict: same
   closedness and complement hypothesis, with no stronger finiteness condition.
3. The ambient derived category is `schemeDerivedCategory X`, and the supported
   quasi-coherent property is `supportedDerivedQCohProperty X T`; the latter is the
   full subcategory of objects with quasi-coherent cohomology and zero restriction
   to `Tᶜ`, as defined in `SupportedDerivedCategory.lean`. Verdict: this renders
   `D_QCoh,T(X)` and the cohomology-support clause of the node.
4. The triangulated conclusion is
   `∃ htri : (supportedDerivedQCohProperty X T).IsTriangulated, letI := htri`.
   Verdict: exactly the assertion that the supported full subcategory is triangulated.
5. The single generator is
   `∃ E : (supportedDerivedQCohProperty X T).FullSubcategory`; its underlying object
   is `E.obj`. Verdict: one object in the supported subcategory, hence its cohomology
   sheaves are supported on `T`.
6. Perfectness is `Scheme.IsPerfect X E.obj`. Verdict: the node's perfect-complex
   clause, using the recorded project definition.
7. Generation is `IsWeakTriangulatedGenerator E` after installing `htri`. Verdict:
   the recorded `def-pc-generators` notion is used directly, with the same shift and
   Hom-detection meaning.

The additional `HasDerivedCategory` binders for `X` and every open are the carrier
instances required by the dependency definitions (`schemeDerivedCategory` and
`Scheme.IsPerfect`); they do not add a mathematical hypothesis beyond making the
node's stated notions well-typed.

Edge cases checked: `T = ∅` gives the full open complement; `T = Set.univ` gives an
empty complement; an empty complement is still represented by the displayed open;
zero objects satisfy the support condition and are handled by the weak-generator
predicate; no index set or natural-number parameter occurs; the statement is
characteristic-independent; and the universe of `T` is the scheme's universe.

Searches: `rg` over the project and slopmaster2 source for supported-derived,
perfect-generator, and weak-generator declarations, plus Mathlib searches recorded
on the node (LeanSearch, Loogle, and grep), found no existing declaration matching
this theorem or the supported-subcategory notion. The missing notion was therefore
added as the new definition node `def-pc-supported-derived-category` and its module
`SupportedDerivedCategory.lean`.

Mismatches found: none. The dependency module's `IsSupportedOn` uses restriction to
an open equal to `Tᶜ` and vanishing of every homology sheaf, which matches the source
notation for support. The theorem signature is unchanged from the worker version.
Both delivery modules compile cleanly with only the intended theorem `sorry`.
