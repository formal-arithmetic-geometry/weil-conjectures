## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage` states
`CategoryTheory.bounded_complex_mem_triangulated`; its proof is `sorry`. It uses no
new definition nodes, no dependency repairs, and no statement correction.

The node's abelian-category hypothesis is rendered by `[Abelian C]`, with
`C : Type u` and `[Category.{v} C]`. The existence of the unbounded derived category
is `[HasDerivedCategory.{w} C]`; the derived object is exactly
`DerivedCategory.Q.obj K`. The strictly full triangulated subcategory is rendered by
`S : ObjectProperty (DerivedCategory C)`, `[S.IsTriangulated]`, and
`[S.IsClosedUnderIsomorphisms]`. The complex and bounds are `(K : CochainComplex C ℤ)`
and `(a b : ℤ)`. The support clause is
`hK : ∀ q : ℤ, q < a ∨ b < q → IsZero (K.X q)`, exactly saying every term outside
`[a,b]` is zero. The term hypothesis is
`hS : ∀ q : ℤ, a ≤ q → q ≤ b →
S ((DerivedCategory.singleFunctor C 0).obj (K.X q))`, placing each term in degree
zero through Mathlib's `singleFunctor`. The conclusion is
`S (DerivedCategory.Q.obj K)`.

The statement dependencies used are Mathlib's `CategoryTheory.Abelian`,
`Mathlib.Algebra.Homology.DerivedCategory.Basic` (`DerivedCategory`, `HasDerivedCategory`,
`DerivedCategory.Q`, and `DerivedCategory.singleFunctor`), and
`CategoryTheory.ObjectProperty.IsTriangulated`/`IsClosedUnderIsomorphisms` from
`Mathlib.CategoryTheory.Triangulated.Subcategory`. The proof dependency
`lem-weil-pbc-complex-ses-triangle` is available as
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact` and supplies the distinguished
triangle for a degreewise short exact sequence.

Edge cases checked include `a > b` (the support condition forces every term to be
zero, so the conclusion follows from `ContainsZero`), `a = b` (one-term induction),
zero terms or gaps inside the interval, negative integer degrees, a nonzero
differential, and arbitrary zero or nonzero objects of the abelian category. No
retract, flatness, projectivity, cohomology, or nonzero assumptions are introduced.
The use of `IsZero (K.X q)` avoids excluding empty support intervals.

Searches for an existing declaration: `msearch.py leanfinder` queried “bounded cochain
complex belongs to triangulated subcategory containing terms” and returned only
T-structure support declarations (`DerivedCategory.IsGE`, `IsLE`, and truncation
lemmas), with no termwise devissage statement. `msearch.py loogle` queried
`ObjectProperty.IsTriangulated, CochainComplex, DerivedCategory` and returned no hits
(the identifier is not a Loogle query constant). `msearch.py grep` queried
`bounded.*triangulated|triangulated.*bounded` under Mathlib CategoryTheory and
Algebra Homology and returned no hits. `rg` over `lean/WeilConjectures` and
`lean/Sheaf` found only specialized stupid-truncation or cohomology results; no
matching declaration. The Mathlib `DerivedCategory.TStructure.prop_of_bounded` result
concerns bounded homology with a property on homology objects, so it is not this
statement.

The original module and identical mathematical signature compiled cleanly twice with
`scompile.py`. The final topic-path/docstring revision is pending the published library
becoming available: both the compile wrapper and dry run currently report “Live
published library is unavailable” and cannot resolve the Mathlib module prefix.
The only expected postponed proof is this theorem's `sorry`.

Additional search: `msearch.py leansearch`, “A bounded complex belongs to every
triangulated subcategory containing its terms in degree zero”, returned eight results:
subcategory closure classes, derived T-structure support and existence of bounded
representatives, with no matching theorem. The nearby project's
`DerivedCategory.bounded_bifunctor_devissage` also uses cohomology hypotheses and two
exact variables, and does not give the present termwise statement. The proposed full
name and item id have no match in the project or the upstream name index.

Source inspected: `literature/stacks-project/derived.tex`, lemma-K-bounded-derived
(Tag 0FCP), especially the displayed stupid-tail triangles. This delivery extracts
the finite triangle induction, without its K-group assertion. All three dependency
node statements and recorded declaration signatures/docstrings were inspected.

## Second reading by NH

This is the author's second pass; the maintainer supplies the independent review.
Read the node and final module together. `C`, its category instance and `Abelian`
express the arbitrary abelian category. `HasDerivedCategory.{w}` allows the chosen
localization size, independent of object universe u and original Hom universe v.
The `ObjectProperty` describes precisely the full subcategory on its objects;
`IsClosedUnderIsomorphisms` makes it strictly full. `IsTriangulated` contains zero,
all integer shifts, and middle-vertex closure; under shifts/rotations this is
equivalent to the node's third-vertex closure, with no additional requirement.
Mathlib explicitly supplies `IsTriangulatedClosed₃` from this class.
`hK` says termwise zero outside the closed integral interval, not cohomological
vanishing. `hS` quantifies over exactly that interval; `singleFunctor C 0` is
`Q` of the single complex (Mathlib `Q_obj_single_obj`). The conclusion applies S
to Q of that same K. There is no `a ≤ b` binder: the empty interval is retained.
The zero, single-term and two-term cases, negative endpoints, and gaps all agree.
No retract closure, term projectivity/flatness, or cohomology-class condition is
present. No mismatch or node fault was found. The file was moved to the general
CategoryTheory/DerivedCategory topic and the proof docstring was expanded to the
node's five steps; the mathematical signature did not change.

## Saved-packet retry, 2026-10-21

Retained the saved module and node without changes. Compared the sandbox node
against the current shared node: only `lean` differs. The recorded signature
matches the module verbatim, every line is within 100 characters, and the current
three statement-dependency records still supply the notions used above. Re-read
the source's stupid-truncation triangles and the Mathlib signatures for `Abelian`,
`HasDerivedCategory`, `DerivedCategory.Q`, and `DerivedCategory.singleFunctor`.
No repair note exists for this item.

Started with `deliver2.py NH lem-weil-pbc-bounded-complex-triangulated-devissage
--no-push` as instructed. It failed with unknown module prefix `Mathlib`; server
confirmation said `Live published library is unavailable`. Two direct
`scompile.py` retries and a final dry-run retry also failed before elaborating
the theorem. The final diagnostic is that the published Mathlib object file
`Mathlib/Algebra/Homology/DerivedCategory/Basic.olean` does not exist; server
confirmation again says `Live published library is unavailable`. Nothing was
pushed. This is a published-build availability failure, not a missing declaration
or an elaboration diagnostic that can be repaired in this packet.

## Dispatcher retry, 2026-10-21

Started with the prescribed saved-packet dry run. It fails before elaboration: the
published object file `Mathlib/Algebra/Homology/DerivedCategory/Basic.olean` is
missing, and server confirmation says `Live published library is unavailable`.
A direct `scompile.py` retry reports the same missing object file and server
confirmation. The theorem and its recorded signature (including `:=`) still
match verbatim, and all source lines meet the 100-character limit.

Refreshed the node copy from the current read-only node, preserving only the saved
`lean` addition; this retains the newly present empty `lean_audit` field, so no
non-`lean` field differs from the current node. The Lean module is unchanged.
This external published-build failure cannot be repaired in the sandbox or by
changing a correct import. Packet retained for the next retry; nothing pushed.

## Successful saved-packet repair, 2026-10-21

The first dry run now reaches preflight; the published-library outage described
above is historical. Its sole diagnostic was that `lean.statement` included the
assignment delimiter `:=`, while the current checker extracts the signature
without it. Removed that delimiter from the JSON record only; the Lean source
and mathematical statement are unchanged. Direct `scompile.py` validation then
passed both sandbox and library compilation, with no errors or warnings.

Rechecked the current node and all three statement-dependency bindings against
the saved module and the Mathlib source docstrings/signatures. The source's
Tag 0FCP stupid-truncation triangles still supply exactly the finite induction.
The item differs from the current shared node only in `lean`; there are no
new or repaired dependency nodes. All universes and binders are explicit,
all lines fit 100 characters, and the sole postponed proof remains
`CategoryTheory.bounded_complex_mem_triangulated`. The prior second reading's
hypothesis-by-hypothesis comparison remains valid, including empty intervals
and termwise rather than cohomological support.
