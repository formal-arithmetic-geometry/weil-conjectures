## Worker report

The module `Sheaf.AlgebraicGeometry.ProperBasic` states
`AlgebraicGeometry.proper_basic`. Its binders are schemes `X S : Scheme.{u}`, a
morphism `f : X ⟶ S`, and the hypothesis `[IsProper f]`, exactly the node's
proper morphism hypothesis. The conclusion is the conjunction
`IsSeparated f` (separated), `UniversallyClosed f` (universally closed),
`LocallyOfFiniteType f` together with `QuasiCompact f` (finite type),
`QuasiCompact f` (the explicit quasi-compact clause), and
`QuasiSeparated f` (quasi-separated). Its final clause is
`IsAffine S → X.IsSeparated ∧ CompactSpace X`, expressing that an affine base
makes the source separated and quasi-compact. No hypotheses are added or
removed, and no clause is omitted.

The dependency `def-weil-proper-morphism` is the Mathlib declaration
`AlgebraicGeometry.IsProper` in
`Mathlib.AlgebraicGeometry.Morphisms.Proper`; the module imports that declaration.
The other property declarations are Mathlib's `IsSeparated`, `UniversallyClosed`,
`LocallyOfFiniteType`, `QuasiCompact`, `QuasiSeparated`, `IsAffine`, and
`Scheme.IsSeparated`.

Edge cases checked: the theorem permits arbitrary schemes, including the empty
scheme, and does not impose nonemptiness or finite-dimensional hypotheses. The
universe is shared (`Scheme.{u}`), so no cases are excluded. The affine clause
is an implication and therefore also permits any affine base, including the
empty affine scheme.

Searches for an existing project declaration or duplicate notion: `rg -n
"proper_basic|Basic consequences of properness" lean/Sheaf` found no match;
`rg -n "IsProper|proper morphism" WeilConjectures` found no project theorem
with this statement. `msearch.py ... leanfinder "proper morphism is separated
universally closed finite type quasi-compact quasi-separated"` returned
`AlgebraicGeometry.IsProper` and no theorem listing this conjunction.
`msearch.py ... loogle "IsProper, IsSeparated, UniversallyClosed"` found only
Mathlib property declarations. Grep of Mathlib's Morphisms files confirmed the
same classes and the `UniversallyClosed` to `QuasiCompact` instance. Thus no
existing declaration states this node.

## Earlier second reading (a previous round; superseded)

Reading the node and module independently, the Lean theorem introduces exactly
`X`, `S`, `f`, and `[IsProper f]`. Each of the five property clauses is present
verbatim as a conjunct, and the final affine specialization has precisely the
source's two conclusions (`X.IsSeparated` and `CompactSpace X`). The module
uses Mathlib's recorded properness declaration and does not define a duplicate.
The statement compiles with only the expected `sorry` warning.


## Second reading by J1

I independently opened the node copy, its only statement dependency
`def-weil-proper-morphism`, the delivered module, and Mathlib's actual declarations.
The literature files are absent from this machine's repository; I read the blueprint
source and Stacks morphisms.tex definition-proper (01W1) on the project server over ssh.
That definition introduces an arbitrary morphism of schemes and assumes no base field,
Noetherian condition, nonemptiness, or other standing restriction. I also read the
Stacks separated-permanence lemma used for composition of separated morphisms.

Object/hypothesis/conclusion checklist, in node order:

- Schemes X and S: `{X S : Scheme.{u}}`. Same general schemes, with no extra
  structure. PASS.
- Morphism f from X to S: `(f : X ⟶ S)`. Same morphism. PASS.
- Properness: `[IsProper f]`, the dependency's recorded
  `AlgebraicGeometry.IsProper` from Mathlib.AlgebraicGeometry.Morphisms.Proper.
  Its signature extends IsSeparated, UniversallyClosed, LocallyOfFiniteType.
  The UniversallyClosed-to-QuasiCompact instance makes this exactly the Stacks
  separated/finite-type/universally-closed definition, not a stronger hypothesis. PASS.
- Separated f: `IsSeparated f`, meaning its diagonal is a closed immersion. PASS.
- Universally closed f: `UniversallyClosed f`, meaning every base change is a
  closed map. PASS.
- Finite type f: the pair `LocallyOfFiniteType f` and `QuasiCompact f`.
  The former alone would be weaker: I checked FiniteType.lean's affine ring-map
  condition and QuasiCompact.lean's compact-open-preimage condition. The pair is
  exactly finite type, and the same QuasiCompact conjunct also renders the next
  clause. PASS.
- Quasi-compact f: `QuasiCompact f`. PASS.
- Quasi-separated f: `QuasiSeparated f`, whose declaration requires the diagonal
  to be quasi-compact, not a global restriction on either scheme. PASS.
- If S is affine: `IsAffine S → ...`, after the general conclusions, with no
  affine hypothesis on the entire theorem. PASS.
- Then X is separated: `X.IsSeparated`, Mathlib's absolute separatedness
  (separated over the terminal scheme), distinct from separatedness of f. PASS.
- Then X is quasi-compact: `CompactSpace X`, compactness without a Hausdorff
  assumption, exactly scheme quasi-compactness. PASS.

Edge cases: empty X and empty affine S are allowed; there is no Nonempty binder.
There is no index set, zero module, integer n, or coefficient characteristic in this
statement. Both schemes inhabit the arbitrary common universe u, as Mathlib's
scheme category requires; there is no independent smaller test-object universe,
field restriction, or dimension assumption. All variables and the universe are
explicitly bound. The conclusion is neither weakened nor strengthened.

Independent searches used different queries from the worker's: LeanFinder
`proper over affine base source compact separated` returned isProper_eq,
isProper_iff, IsProper.toIsSeparated, composition results, and the field-base
compactness theorem. Opening Proper.lean showed isProper_iff gives only three
clauses; the compactness theorem is restricted to a field base. None states this
whole node. Loogle `IsProper, CompactSpace` reported unknown identifier IsProper
and no hits. LeanSearch `basic properties of proper scheme morphisms` was
unavailable (Internal Server Error); no verdict is inferred from that failure.
Direct rg for `proper_basic|IsProper.*∧|IsProper.*IsSeparated|proper.*consequence`
in Mathlib AlgebraicGeometry, WeilConjectures, and the repository lean/Sheaf
found the component definitions and unrelated properness conclusions, not this
conjunction with the affine specialization. No duplicate statement or missing
notion was found. No new nodes or dependency modules are needed.

Mismatches repaired: the Worker report called LocallyOfFiniteType alone finite
 type; I clarified that finite type is its conjunction with QuasiCompact. The
 theorem's proof docstring was too compressed and did not name the node's proof
 dependencies: I expanded it to follow every step, naming all four dependencies
 and explaining the whole-base compactness argument and affine-base separatedness.
 The signature and node record remain unchanged, with lean.statement matching
 the signature verbatim. There are no definitions, local notation/instances, or
 additional proved declarations; the sole theorem has a sorry proof.

Validation: the repaired module was compiled with scompile.py under its default
limit, with no errors or warnings other than declaration uses sorry.
