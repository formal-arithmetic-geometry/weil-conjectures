## Worker report

The module `Sheaf.Paper.ScalarExtensionExactIntrinsic` states the repaired intrinsic version of
this lemma. It imports the published `Sheaf.Paper.SfRationalizationKaroubi` interface, whose raw
rationalized category is the scalar localization of the current
`sfIntegralConstructibleCategory` and whose functor `sfRationalScalarExtension` is fixed by the
canonical completed integral restriction on objects and localized pure tensors. The theorem
`sfScalarExtension_exact_triangulated` asserts the two source clauses: a coherent integer-shift
comparison exists, and under that comparison the scalar-extension functor preserves
distinguished triangles (`IsTriangulated`).

The Lean binders render every source hypothesis: `D : FiniteFieldDatum`, `[Fact l.Prime]`,
`hl : l ≠ D.p`, finite coefficient fields `E` and `L` via
`[Field -] [Algebra (Padic l) -] [FiniteDimensional (Padic l) -]`, the
`Padic l`-algebra inclusion `ι : E →ₐ[Padic l] L`, and an arbitrary scheme `Y`. The conclusion
is exactly `∃ h : (sfRationalScalarExtension l E Y D.p hl L ι).CommShift ℤ` followed by the
conditional `IsTriangulated` proposition with that instance. The global datum is used only for
its prime `D.p`, as in the repaired intrinsic rationalization interface; no relation between
`Y` and the finite-field datum is added.

Dependencies read from the DAG and source declarations:

- `def-weil-finite-field-fiber`: `WeilConjectures.FiniteFieldDatum` in
  `Sheaf.Paper.FiniteFieldFiber`.
- `def-weil-rationalization-karoubi`: repaired intrinsic declarations in
  `Sheaf.Paper.SfRationalizationKaroubi`, especially
  `sfRationalConstructibleCategory`, `sfRationalScalarExtension`, and
  `sfRationalScalarExtension_additive`.
- `def-weil-integral-scalar-extension`: current universe-general interface
  `WeilConjectures.integralScalarExtensionOfUniverses` in
  `Sheaf.Paper.IntegralScalarExtensionUniverses`.
- `lem-weil-integral-scalar-extension-constructible`: intrinsic preservation and restriction
  declarations `sfIntegralScalarExtension_constructible`,
  `sfConstructibleIntegralScalarExtension`, and
  `sfConstructibleIntegralScalarExtension_smul` in
  `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.

Edge cases checked: equality `E = L` with `ι = AlgHom.id` is included; arbitrary schemes include
empty schemes; the raw localization keeps the integral objects and adds no idempotent completion;
all integer shifts are covered by `CommShift ℤ`; and `l ≠ D.p` is explicit. No finite-type,
separatedness, or geometric condition on `Y` was introduced.

Searches made: `msearch.py` LeanFinder for completed rational scalar-extension exactness (only
generic localization/triangulated-functor hits); `msearch.py` Loogle for
`CategoryTheory.Functor.IsTriangulated` (generic declarations only); `msearch.py` grep for
`mapDerivedCategory|IsTriangulated` in `Mathlib/CategoryTheory` (no coefficient-specific
match); `rg` over `WeilConjectures/` and `lean/Sheaf` for `rationalScalarExtension` and
`sfIntegralConstructible`; and `grep -rl` over `dag/nodes` for all citers. The exact intrinsic
rationalization dependency was found in `Sheaf.Paper.SfRationalizationKaroubi`; no existing
exactness theorem for this item was found.

The archived attachment was invalidated because it targeted the retired
`boundedConstructibleDerivedCompleteIntegralCategory`. This delivery uses the repaired intrinsic
category and preserves the source statement and coefficient cases.

## Earlier second reading (a previous round; superseded)

The intrinsic theorem header was checked against the module after the first dry run. The repaired `SfRationalizationKaroubi` declarations and the source coefficient hypotheses are used verbatim; no additional geometric hypothesis is present. The dry-run preflight feedback was applied: the node now records branch `newtargets-dag` and the exact parsed theorem signature.


## Second reading by NV

I independently opened the delivered node and theorem, the blueprint source at order
1883, the defining rationalization source at order 1460, and the recorded dependency
modules. I first checked the inherited NY statement correction against those sources:
the global datum and prime inequality are explicitly assumed by the defining source;
the inclusion is a Q_l-algebra inclusion; Y is arbitrary. The correction introduces
neither a geometric hypothesis nor a restriction to proper extensions. Its record is
already on the base and is unchanged by this delivery. There is no item repair note
in coord/repair-notes on the inspected base.

The statement checklist, in source order, is:

| Node object, hypothesis or conclusion | Lean rendering and verdict |
| --- | --- |
| Global finite-field datum (p,a,q,k0,k) | `D : FiniteFieldDatum.{d}`; the actual structure has prime p, positive a, q=p^a, the finite base field and its algebraic closure. Exact. |
| A prime l distinct from p | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`. Exact. |
| Finite extensions E and L of Q_l | Each has `Field`, `Algebra (Padic l)` and `FiniteDimensional (Padic l)` binders. These are fields, not merely finite-type algebras. Exact. |
| Inclusion E into L over Q_l | `ι : E →ₐ[Padic l] L`; a unital homomorphism from a field is injective, so no additional injectivity hypothesis is necessary. Exact. |
| Any scheme Y | `Y : AlgebraicGeometry.Scheme.{u}`; no over-base, finite-type, separatedness, nonemptiness, or Noetherian binder. Exact. |
| The specified completed, restricted, rationalized scalar functor | `sfRationalScalarExtension l E Y D.p hl L ι`, with its source and target `sfRationalConstructibleCategory`. Opened its actual definition and `sfRationalScalarExtension_existsUnique`: objects are the completed integral extension restricted by `sfConstructibleIntegralScalarExtension`; morphisms are the prescribed localized pure tensors. Exact. |
| Preserve shifts | `∃ h : (...).CommShift ℤ`; Mathlib's `CommShift` includes natural comparison isomorphisms for every integer, with zero and addition coherence. This is a conclusion, not a supplied hypothesis. Exact. |
| Preserve every distinguished triangle using those comparisons | The dependent lambda installs that same h and asserts `(...).IsTriangulated`. Opened Mathlib `CategoryTheory/Triangulated/Functor.lean`: its field universally quantifies triangles and requires distinguished images under `mapTriangle`, including the connecting arrow. Exact. |

I opened all four statement-dependency signatures. `FiniteFieldFiber` supplies the
actual global datum. `SfRationalizationKaroubi` uses raw `ScalarLocalization` of
`sfIntegralConstructibleCategory`, with the induced shift and image distinguished
triangles, and takes no idempotent completion. Its completed transition is uniquely
specified on objects and pure tensors, so it is not an arbitrary functor chosen from
mere existence. `IntegralScalarExtensionConstructibleIntrinsic` preserves precisely
`sfIntegralConstructible`, lifts the ambient functor to its full subcategory, and
retains the actual integral scalar action. The recorded
`integralScalarExtensionOfUniverses` and the equal-universe `integralScalarExtension`
used by this restriction are both literally the same
`integralScalarExtensionWellDefined` localization witness at the common universes;
the new public import makes the currently recorded interface explicit.
There are no new nodes or dependency modules in this delivery.

Edge cases: E=L and `AlgHom.id` are allowed; any Q_l-algebra embedding is allowed,
without a strict-extension condition or an embedding in a chosen algebraic closure.
Empty schemes, zero objects and zero triangles are included by the universal scheme
and triangle binders. There is no index set in the statement. The tower index n=0
is internal to the dependency's convention for positive finite levels and adds no
hypothesis here. All integer shifts, including zero and negative integers, are
covered. All coefficient primes distinct from D.p are covered; no condition on the
residue characteristics of Y is added. The datum universe d is independent. The
scheme and finite coefficient models use the published common universe u,
universally quantified; finite extensions of Padic admit small models in any such
universe. No equality of the small site's object and morphism universes is imposed.
All variables and universes in the delivered signature are bound explicitly.

Independent searches (2026-10-16): LeanFinder query "rationalized completed change
of coefficients sends distinguished triangles to distinguished triangles" found
generic `map_distinguished`, localization and homotopy-category results only.
Loogle `CategoryTheory.Functor.CommShift` found the general shift interface and its
coherence API, not this functor. LeanSearch "An exact functor on completed integral
constructible complexes induces a shift commuting functor preserving distinguished
rationalized triangles" returned generic derived/homotopy functors and
`IsTriangulated.map_distinguished`, not the required theorem. Direct rg searches of
Mathlib, upstream WeilConjectures and project lean/Sheaf used
`scalar.*[Ee]xtension.*(triangulated|exact)`,
`[Ee]xtension.*[Ii]sTriangulated`, `sfScalarExtension_exact`, and
`rationalScalarExtension.*(triangulated|exact)`.
I opened the apparent matches `ScalarExtensionExactTriangulated`,
`ScalarExtensionExact`, and `PbcScalarExtension`: the former two use retired
`rationalScalarExtension` / bounded-category attachments; the latter uses the PBC
coefficient category and its dimension/invertibility input. None states exactness
for the currently recorded intrinsic functor. The new declaration name has no
Mathlib, upstream, or existing project match. No duplicate definition is introduced.

I read Stacks derived.tex at `proposition-construct-localization` (05R6),
`proposition-derived-functor` (05SE), and `lemma-find-existence-computes` (06XN).
The latter two assume an exact input and a resolving class inverting the specified
weak equivalences; the node's cone calculation and K-flat steps provide exactly
those hypotheses. The localization proposition supplies the image-triangle
criterion used in step 6; it does not require a Karoubi completion.

I also opened the inherited correction's citers: `prop-functor-package` uses this
lemma for its exact finite-extension clause within the global datum;
`def-weil-algebraically-closed-coefficients` uses it for the transition inclusions,
including equality; `lem-fix-operation-reduction` uses the same functor for field
passage. All three recorded holds:true verdicts remain correct. No citer is edited.

Mismatches repaired: H8, the original docstring compressed the six DAG proof steps
into one paragraph and omitted the homotopy signs, cone connecting arrow, resolving
class argument, linear restriction and localized tensor naturality. It now carries
the entire six-step node proof, with sources and dependency ids. The module also
omitted explicit imports for the recorded statement and proof dependencies; these
are now public for statement dependencies and ordinary imports for proof-only
modules, including the two Mathlib modules serving the homotopy-category leaf.
The theorem signature, objects and hypotheses needed no change. The only theorem
proof remains `by sorry`; there are no definitions, hollow data, local notations,
private notions, additional axioms, or proved auxiliary statements.

Validation: the original module compiled cleanly through the prescribed scompile.py.
The repaired module compiled cleanly through that wrapper (sandbox 5.8 s, library
4.8 s), with no warnings; a docstring terminator spacing warning from the prior
check was corrected without disabling its linter.
The node's lean.statement was compared verbatim with the unchanged file signature.
