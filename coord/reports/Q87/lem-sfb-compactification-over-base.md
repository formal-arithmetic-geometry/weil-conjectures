## Worker report

The module `lean/Sheaf/SixFunctors/CompactificationOverBase.lean` states
`AlgebraicGeometry.compactification_over_base`. It uses the landed declaration
`AlgebraicGeometry.Compactification.BoundaryCompactification` from
`Sheaf.Compactification.BoundaryRefinement` for the conclusion: a nonempty object
is a compactification whose open immersion is quasi-compact, with the proper
structure morphism and factorization data supplied by the existing
`AlgebraicGeometry.Compactification` structure.

The hypotheses are rendered as follows. `S X Y : Scheme.{u}` are schemes in one
universe. `[CompactSpace S]` is quasi-compactness of the base and
`[QuasiSeparatedSpace S]` is its quasi-separatedness. `[X.Over S]` and `[Y.Over S]`
make X and Y S-schemes, while `[f.IsOver S]` makes `f : X ⟶ Y` an S-morphism.
The classes `[IsSeparated (X ↘ S)]`, `[LocallyOfFiniteType (X ↘ S)]`, and
`[QuasiCompact (X ↘ S)]` say that X is separated and of finite type over S.
The classes `[IsSeparated (Y ↘ S)]` and `[QuasiCompact (Y ↘ S)]` say that Y is
separated and quasi-compact over S. The conclusion
`Nonempty (Compactification.BoundaryCompactification f)` states existence of a
compactification of f with quasi-compact open immersion, exactly the notion in
`sk-def-nagata-sketch-data`.

The statement dependency declaration used is
`Sheaf.Compactification.BoundaryRefinement`,
`AlgebraicGeometry.Compactification.BoundaryCompactification`. The declaration
was read in full: it is the `WideSubcategory` on the full subcategory of
compactifications with `QuasiCompact c.i`, so its objects carry precisely the
required compactification and quasi-compact-open conditions. The proof plan
imports `WeilConjectures.Compactification.NagataCompactification`, corresponding
to `sk-thm-nagata-compactification`; the remaining dependency notions are the
Mathlib declarations recorded by their DAG nodes (`Scheme.Over`,
`LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `QuasiSeparated`, and
`CompactSpace`).

Edge cases checked: the class `CompactSpace` allows the empty scheme and zero
rings; no nonemptiness of S, X, Y, or any index type is assumed. The finite-type
condition is the exact conjunction of locally finite type and quasi-compactness,
and no finite-type hypothesis is imposed on Y. Universes are shared explicitly
by all three schemes, and every variable is explicitly bound.

Searches made: `msearch.py Q87 lem-sfb-compactification-over-base leanfinder
"compactification of a separated finite type morphism over a quasi-compact
quasi-separated base"` returned eight general hits (quasi-compactness,
properness, and normalization), with no compactification-existence theorem;
`msearch.py ... loogle "AlgebraicGeometry.HasCompactification,
AlgebraicGeometry.IsSeparated, AlgebraicGeometry.LocallyOfFiniteType"` returned
zero hits and reported the unknown identifier `AlgebraicGeometry.HasCompactification`;
`msearch.py ... grep "HasCompactification|NagataCompactification|compactification"
AlgebraicGeometry` returned zero hits. I also searched the project with `rg` for
`lem-sfb-compactification-over-base` and for `HasCompactification`; no existing
project declaration states this S-relative theorem. The existing
`BoundaryCompactification` declaration is used rather than redefining the
compactification notion.

## Second reading by Q87

I independently read the sandbox node and module, the authoritative
main-20261015 blueprint statement and proof, every statement dependency record,
and the declarations described below. No repair note exists for this item.
There is no `statement_change`, new definition node, or dependency module in
this delivery. The node's statement agrees verbatim with its blueprint source.
The supporting Stacks source is `literature/stacks-project/flat.tex`, section
`section-compactify` (lines 9278 onward) and `theorem-nagata` (lines 9950 onward):
its base is qcqs, its morphism separated of finite type, and its compactification
is a quasi-compact open immersion into a proper scheme. No Noetherian, field,
characteristic, reducedness, or nonemptiness assumption is implicit there.

Object/hypothesis/conclusion inventory, with the Lean open:

| Node item | Lean rendering and verdict |
| --- | --- |
| Arbitrary schemes S, X, Y | `{S X Y : Scheme.{u}}`; correct, polymorphic in arbitrary `u`. |
| S is quasi-compact | `[CompactSpace S]`; correct, no Hausdorff condition. |
| S is quasi-separated | `[QuasiSeparatedSpace S]`; correct absolute scheme property. |
| X and Y are S-schemes | `[X.Over S] [Y.Over S]`, with structure maps `X ↘ S`, `Y ↘ S`; correct. |
| X separated over S | `[IsSeparated (X ↘ S)]`; correct diagonal condition. |
| X of finite type over S | `[LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]`; exactly the dependency's conjunction. |
| Y separated over S | `[IsSeparated (Y ↘ S)]`; correct. |
| Y quasi-compact over S | `[QuasiCompact (Y ↘ S)]`; correct relative property, not an extra finite-type assumption. |
| Every S-morphism f | `(f : X ⟶ Y) [f.IsOver S]`; universally quantified after the structure maps, with exactly their commuting triangle. |
| Some ambient scheme and maps X → Z → Y | `Nonempty (Compactification.BoundaryCompactification f)`; underlying `Compactification f` has fields `Z`, `i`, `g`. |
| Their composite is f | Underlying field `comm : f = i ≫ g`; correct orientation-equivalent equation. |
| First map quasi-compact open immersion | Underlying field `isOpenImmersion` and `QuasiCompactObjects` property `QuasiCompact c.i`; both clauses present. |
| Second map proper | Underlying field `isProper : IsProper g`; correct. |
| No density or choice clause | `Nonempty` supplies existence only; correct. No scheme-theoretic density is imposed. |

I opened `Sheaf.Compactification.BoundaryRefinement` and upstream
`WeilConjectures.Compactification.Defs` and `Refinement`. In particular,
`QuasiCompactObjects f` is the full subcategory on `QuasiCompact c.i`, and
`BoundaryCompactification f` is a wide subcategory of that category. I also read
Mathlib's `ObjectProperty.FullSubcategory` and `WideSubcategory` structures:
the latter has only an `obj` field and imposes no new condition on objects.
Thus its boundary condition restricts refinement arrows, not the witnesses
asserted by this theorem. The dependency interface is usable exactly as recorded;
a second compactification definition would be wrong.

The other dependency interfaces were checked at their source declarations:
`Mathlib.AlgebraicGeometry.Over` defines `Scheme.Over` as `OverClass` and
`Scheme.Hom.IsOver` as `HomIsOver`, with
`f.IsOver S ↔ f ≫ Y ↘ S = X ↘ S`;
`Morphisms.FiniteType` defines `LocallyOfFiniteType` on affine restrictions;
`Morphisms.QuasiCompact` defines the compact-preimage condition;
`Morphisms.Separated` defines the closed diagonal condition;
`Morphisms.Proper` defines `IsProper` extending separated, universally closed,
and locally finite type (universal closedness supplies quasi-compactness).
`Morphisms.QuasiSeparated` defines `QuasiSeparated` by its quasi-compact diagonal
and proves its equivalence with the topological absolute
`QuasiSeparatedSpace` for the terminal map. `Topology.Defs.Filter` defines
`CompactSpace` by compactness of the entire underlying space. These are the
recorded dependency notions, without specialized or stronger replacements.

Proof-plan check: the source proof and the node's three steps agree. The file's
old step 1 omitted the crucial derivation that Y is quasi-compact. I expanded it
to record both X and Y quasi-compact and Y quasi-separated, with the exact
permanence nodes; step 2 now names each cancellation/permanence clause and
step 3 explicitly forgets density. I read
`WeilConjectures.Compactification.Dense.exists_isDense_compactification`:
it takes exactly separated, locally finite type, quasi-compact f and qcqs Y.
The former public import of `NagataCompactification` was a proof-only import
and did not expose that recorded dense existence declaration. I replaced it
with ordinary `import WeilConjectures.Compactification.Dense`, which imports
Nagata too. All remaining Mathlib proof-dependency declarations are available
through the public compactification dependency. I also clarified the opening
docstring: it is X's structure map that is assumed finite type and separated.
No theorem signature, node statement, or mathematical conclusion changed.
The only theorem body remains `by sorry`; no data definitions or proofs added.

Edge cases: empty X permits an empty compactification, and empty S forces the
S-schemes to be empty; neither case is excluded by any binder. Empty Y is
covered whenever the given f exists. Zero-ring affine schemes are consequently
allowed. Proper f admits its identity compactification, without requiring a
dense or unique witness. There is no index set, degree n, or coefficient ring
in this statement, so empty-index, n = 0 and coefficient-zero cases introduce
no restrictions. All characteristics and non-Noetherian qcqs bases remain
included. One common arbitrary scheme universe is the recorded `Scheme.Over`
and compactification convention; there is no extra universe equality or
bounded test-scheme quantifier. Every universe and variable is explicitly
bound (`set_option autoImplicit false`), and no hidden instance is assumed.

Independent searches, using different phrasing from the worker:

- LeanFinder through `msearch.py`: "a map between schemes over a common base
  factors through a proper scheme by a quasi compact open embedding" returned
  eight constituent-property hits (`UniversallyClosed`, `IsProper`,
  `QuasiCompact`, proper pullbacks, `IsProper.of_comp`, `QuasiCompact.of_comp`),
  no complete relative compactification theorem.
- Loogle through `msearch.py`: `"Compactification"` returned zero hits, with
  no parser/service error.
- LeanSearch through `msearch.py`: "relative compactification existence for
  morphism between separated schemes over qcqs base" returned eight hits on
  separatedness, quasi-compact preimages and qcqs permanence, no exact theorem.
- `rg` in Mathlib/AlgebraicGeometry for `nagata|compactification|compactif`
  found no such definition or theorem. `rg` in upstream WeilConjectures and
  project lean/Sheaf for `HasCompactification`, `exists.*Compactification`,
  `Nonempty.*Compactification`, relative compactification spellings, and the
  proposed declaration name found the general Nagata/dense theorem and the
  already used boundary category, not this statement. I inspected the closest
  additional hit, `WeilSheaf.LowerShriek.hasCompactification_of_over`: it is
  over `Spec k₀` and assumes the separated/finite-type/quasi-compact properties
  of f itself, so it is not this arbitrary-S theorem. Searches of
  `dag/lean_names_upstream.json` and the project found no name collision.

Verdict: every hypothesis and conclusion clause is exact. Only the proof
import and docstring needed repair; no new nodes or dependency repairs are
needed. `lean.statement` was checked verbatim against the unchanged signature.
All lines in the delivered Lean module are at most 100 characters.

Validation after repairs: `scompile.py Q87 lem-sfb-compactification-over-base
lean/Sheaf/SixFunctors/CompactificationOverBase.lean` compiled the sandbox and
library forms cleanly (1.5 s and 1.6 s), with no warnings or errors.
