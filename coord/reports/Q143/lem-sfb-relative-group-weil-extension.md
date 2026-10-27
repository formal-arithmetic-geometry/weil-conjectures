## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeGroupWeilExtension` states
`AlgebraicGeometry.existsUnique_relative_group_weil_extension`, with one `sorry` and no
definitions or additional lemmas. The original node is unchanged except for its `lean`
record. No dependency module, new node or statement correction is needed.

Source read: Bosch--Lütkebohmert--Raynaud, *Néron Models*, §4.4 Theorem 1 and its
proof, printed pp.109–110, PDF pages 115–116 (zero-based indices), in the primary scan
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The theorem concerns an S-rational map to a smooth separated S-group, defined in
codimension at most one. The node renders its domain as an explicit fibrewise dense
open. The proof is local on the source and uses the diagonal difference and flat
descent; the docstring records all seven steps of the accepted DAG proof.
The latest blueprint's `det-thm-sf-ctf-stability-direct-images`, proof (3), and the
node's `blueprint.from.via` identify the supporting alteration/trait-extension route.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Base scheme S | `(S : Scheme.{u})` |
| Finite affine cover by Noetherian spectra | `[IsNoetherian S]`; Mathlib `isNoetherian_iff_of_finite_iSup_eq_top` identifies precisely this condition |
| Every local ring is an integrally closed domain | `_hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)` |
| Smooth structural morphism Z → S | `(Z : Scheme.{u}) (p : Z ⟶ S) [Smooth p]` |
| Group scheme H over S, with multiplication, identity, inverse and group laws | `(H : Over S) [GrpObj H]`; the cartesian monoidal structure on `Over S` uses fibre products over S, and `GrpObj` extends `MonObj` with inverse and both inverse identities |
| Smooth H → S | `[Smooth H.hom]` |
| Diagonal of H → S is a closed immersion | `[IsSeparated H.hom]`, whose sole field is `IsClosedImmersion (pullback.diagonal H.hom)` |
| Open subscheme U of Z | `(U : Z.Opens)`, with canonical scheme `U.toScheme` and inclusion `U.ι` |
| Given S-morphism u : U → H | `(f : U.toScheme ⟶ H.left)` with `_hf : f ≫ H.hom = U.ι ≫ p` |
| U_s dense in Z_s for every s | `_hdense : ∀ s : S, Dense ((p.fiberι s) ⁻¹' (U : Set Z))`; `p.fiber s` is the specified residue-field fibre, and this inverse image is exactly the underlying open of its base change U_s |
| U contains every z with dim O_{Z,z} ≤ 1 | `_hcodim : ∀ z : Z, ringKrullDim (Z.presheaf.stalk z) ≤ 1 → z ∈ U` |
| Existence and uniqueness of an S-morphism extending u | `∃! g : Z ⟶ H.left, g ≫ H.hom = p ∧ U.ι ≫ g = f` |
| No quasi-compactness required of Z or H | There is no compactness, finite-type or finite-presentation binder on Z or H; `Smooth` only requires local finite presentation |
| No commutativity or connectedness of the group | `GrpObj H` has neither assumption; no `IsCommMonObj`, `CommGrpObj` or connectedness binder is present |

The common arbitrary universe `u` is explicitly declared and all scheme objects have
that universe, as in Mathlib's scheme category and morphisms. No auto-bound variables
are used: the module sets `autoImplicit false`. Normality is the exact inline stalk
condition; upstream `IsNormalScheme` was read but would additionally impose global
integrality and would exclude disconnected normal bases, so it is not used.

Recorded statement dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, through the exact definition of `IsSeparated`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber` and `AlgebraicGeometry.Scheme.Hom.fiberι`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`.

Additional existing APIs: `AlgebraicGeometry.IsNoetherian` in
`Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsSeparated` in
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, `CategoryTheory.GrpObj` in
`Mathlib.CategoryTheory.Monoidal.Grp`, and `IsIntegrallyClosed` in
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. Their full definitions and
docstrings were read. There is no private version of any notion.

Already stated proof dependencies are imported privately: `Morphisms.Proper`
(proper base change), `Morphisms.UniversallyOpen` (flat lfp openness and maps over
fields), `Sites.Fpqc` (the fpqc precoverage and subcanonicity), and `Gluing`
(scheme morphism gluing). `Morphisms.Smooth` already supplies smooth open restriction,
smooth base change and smooth flatness; `Morphisms.Separated` supplies
`ext_of_isDominant_of_isSeparated`. Three proof-only nodes have no usable recorded
declaration yet and therefore no import: `lem-sfb-smooth-normal-ascent`,
`lem-trf-smooth-reduced-dense-pullback`, and
`lem-sfb-smooth-section-rational-extension`. None is needed to type this statement.

Edge cases checked before writing and again against the signature: empty S and Z;
empty fibres, on which density is vacuous; U = Z; empty U (possible only for empty Z
under the hypotheses); disconnected normal Noetherian bases; noncommutative groups;
disconnected and non-quasi-compact group schemes; non-quasi-compact smooth sources;
points of local dimension zero or one; and arbitrarily large finite local dimensions
or infinite Krull dimension. Only the stated ≤ 1 condition is imposed. In particular,
there is no implicit global integrality or nonemptiness assumption. `∃!` quantifies
uniqueness among precisely those morphisms which are over S and restrict to f.

Searches actually run, through `msearch.py Q143 lem-sfb-relative-group-weil-extension`:

- LeanFinder: “Weil extension theorem: a rational map from a smooth scheme over a
  normal noetherian base to a smooth separated group scheme defined at codimension
  one extends uniquely”. Eight hits, including rational-map function-field
  representatives and separated equality; no extension theorem.
- Loogle: `GrpObj, AlgebraicGeometry.Smooth, AlgebraicGeometry.IsSeparated`.
  No hits, with diagnostic `unknown identifier 'GrpObj'`; this query does not
  establish absence and was supplemented by direct source inspection.
- Mathlib grep: `weil.*extension|Weil.*Extension|GrpObj`, subdirectory
  `AlgebraicGeometry`. Seventeen hits, giving uses of the existing group-object
  API but no Weil extension theorem.
- LeanSearch: “A morphism from a fibrewise dense open of a smooth scheme over a
  normal Noetherian base to a smooth separated group scheme extends uniquely when
  defined at all codimension one points”. Eight hits: separated equality,
  `Scheme.PartialMap` and smooth open immersions; none supplies existence here.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `Weil extension`, `WeilExtension`, `weil_extension`, `weilExtension` and group-object
  usage. No matching extension theorem. The only broad “Weil extension” match is
  the unrelated extension-by-zero construction in `TraceFormula/OpenSquare.lean`.
  Group scheme sources consistently use the same Mathlib `GrpObj (Over ...)` API.
- Exact declaration-name search in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf`: no collision for
  `existsUnique_relative_group_weil_extension`.

No node faults or statement disputes found. Server compilation through `scompile.py`
passed for both sandbox mode (1.5 seconds) and library mode (1.6 seconds), with no
errors or non-sorry warnings. The node's `lean.statement` is extracted verbatim from
the theorem signature; all other node fields are preserved.

## Second reading by Q143

I reopened the node and module and checked the correspondence table against both.
This is the dispatcher's single-worker rereading; independent review is supplied by
the maintainer, as specified in the task, rather than attributed to another worker.
The normality conjunction includes domains as well as integral closure; Noetherianity
is imposed only on S. Both structural maps are smooth. `GrpObj` is on `Over S`,
so all three operations and their laws are relative to the correct base. Relative
separatedness is precisely the closed-diagonal condition and is not absolute
separatedness. The preimage of U under the fibre inclusion expresses density of
the correct residue-field fibre, including empty fibres, without choosing a map.
The codimension condition uses the full stalk of Z and allows dimension zero as
well as one. The two conclusion equations assert S-linearity and the exact
restriction, and uniqueness is scoped to that conjunction. No commutativity,
connectedness or quasi-compactness was accidentally introduced. No mismatch or
change was found on this rereading. The signature and record agree verbatim.
