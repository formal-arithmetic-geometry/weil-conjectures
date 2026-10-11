## Worker report

The module `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteResLE` states
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_resLE`, with proof `sorry`.
No definition is added and the item node changes only in `lean`.

Hypothesis and clause correspondence:

- Schemes X and S: `{X S : AlgebraicGeometry.Scheme.{u}}`, with explicit arbitrary universe u.
- Morphism f: `(f : X ⟶ S)` in the category of schemes.
- f locally quasi-finite in Stacks 01TD: `(hf : IsLocallyQuasiFinite f)`, using exactly
  the recorded project predicate, whose affine witnesses include finite type.
- Open subschemes U of X and V of S: `(U : X.Opens) (V : S.Opens)`; their schemes are
  Mathlib `U.toScheme` and `V.toScheme`, with the restricted structure sheaves.
- f(U) contained in V: `(e : U ≤ f ⁻¹ᵁ V)` is precisely the pointwise image-containment condition.
- The inclusions are Mathlib `U.ι` and `V.ι`. Mathlib already supplies their
  `AlgebraicGeometry.IsOpenImmersion` instances, so these are consequences of the open
  subscheme construction, not additional hypotheses.
- The unique induced morphism is `f.resLE V U e : U.toScheme ⟶ V.toScheme`.
  Mathlib `Scheme.Hom.resLE_comp_ι` gives `f.resLE V U e ≫ V.ι = U.ι ≫ f`, the required
  commutative square. Since V.ι is an open immersion and hence mono, the square determines
  this morphism uniquely; selecting the canonical morphism excludes no choice allowed by the node.
- Conclusion: `IsLocallyQuasiFinite (f.resLE V U e)`, again the same Stacks predicate.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, the category of locally affine locally ringed spaces.
- `pqf-def-quasifinite`: Sheaf.AlgebraicGeometry.QuasiFiniteMorphism,
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, defined by quantification over all
  points using `IsQuasiFiniteAtPoint`; the latter uses affine opens, the induced appLE
  algebra, an Algebra.FiniteType witness, and Algebra.IsQuasiFiniteAtPrime.
- `def-weil-open-immersion`: Mathlib.AlgebraicGeometry.OpenImmersion,
  `AlgebraicGeometry.IsOpenImmersion`. The canonical inclusions from
  Mathlib.AlgebraicGeometry.Restrict satisfy it; that module also defines `resLE` and
  proves `resLE_comp_ι`. These are available transitively through the sole import.

The declaration docstring carries all five DAG proof steps, with their node identifiers.
Nothing is proved during stage 2. No dependency record is unusable.

Source check: the local `literature/stacks-project/morphisms.tex` is absent on this machine,
so the original Stacks pages were opened directly:
[01TD](https://stacks.math.columbia.edu/tag/01TD),
[01TH](https://stacks.math.columbia.edu/tag/01TH), and
[03JA](https://stacks.math.columbia.edu/tag/03JA).
The affine-pair characterization and its use for restrictions agree with the node.
No statement correction or STATEMENT-DISPUTED flag is needed.

Edge cases checked before writing:

- Empty U: there are no points to test; the conclusion is vacuous exactly as Stacks defines it.
- Empty V: e forces U empty; the same vacuous conclusion applies.
- Empty source or target schemes: allowed by the Scheme binders; no nonemptiness assumption appears.
- U = X and V = S: restriction is the original morphism through the canonical top-open isomorphisms.
- Arbitrary non-affine, non-quasi-compact opens: no affine or quasi-compact hypothesis is added.
- Arbitrary schemes and characteristics: no field, reducedness, Noetherian, or separatedness assumptions.

Searches for an existing statement (all service calls used msearch.py and are recorded in searches.jsonl):

- LeanSearch: "restriction of a locally quasi-finite morphism to open subschemes is locally
  quasi-finite"; service unavailable (Internal Server Error), recorded as unavailable.
- LeanFinder: the same query; eight hits, including instLocallyQuasiFiniteResLE and
  instLocallyOfFiniteTypeResLE. The former uses Mathlib.LocallyQuasiFinite, whose definition
  explicitly omits finite type; neither states the theorem for the dependency predicate.
- Loogle: "AlgebraicGeometry.LocallyQuasiFinite, AlgebraicGeometry.Scheme.Hom.resLE";
  one hit, AlgebraicGeometry.instLocallyQuasiFiniteResLE, again the different Mathlib predicate.
- Mathlib grep via msearch.py: "resLE|class LocallyQuasiFinite" in
  AlgebraicGeometry/Morphisms/QuasiFinite.lean; three hits including the restriction instance.
  Read its full signature and the defining class/docstring; no exact match.
- Local rg: "IsLocallyQuasiFinite|lqf-restriction-to-opens|isLocallyQuasiFinite_resLE" in
  lean/Sheaf, WeilConjectures, and dag/lean_names_upstream.json; only the dependency definition.
- Local rg of the item identifier in WeilConjectures: no hits.
- Local rg in Mathlib.AlgebraicGeometry for resLE and its square; found the existing canonical
  restriction in Restrict.lean, which is reused rather than redefined.

Validation: server compilation and delivery preflight are run with the prescribed tools.
The independent second reading remains for the next worker; nothing is pushed by this worker.

## Second reading by F1

I independently read the item JSON, its entire Lean module, all three statement
 dependency nodes and their recorded declarations. There are no new definition nodes,
 dependency modules, or statement corrections in this delivery.

Source: the repository's Stacks checkout is absent. I fetched the original
`morphisms.tex` from the Stacks project's GitHub into this item's scratchpad and read
lines 3522–3562, 3664–3728, and 15495–15515, including the section introduction.
I also checked the official pages for [01TD](https://stacks.math.columbia.edu/tag/01TD),
[01TH](https://stacks.math.columbia.edu/tag/01TH), and
[03JA](https://stacks.math.columbia.edu/tag/03JA).
There is no standing base-field, Noetherian, separatedness, or quasi-compactness
assumption in the quasi-finite section. The locally finite type hypothesis of 01TH
follows from 01TD here; the quasi-compactness hypothesis of 03JA concerns its bounded
fibres conclusion and is not a hypothesis of the restriction assertion.

The node's objects, hypotheses, and conclusion, matched individually:

1. Schemes X and S: `{X S : AlgebraicGeometry.Scheme.{u}}`. PASS. I read
   `Scheme.lean:42` (locally affine locally ringed spaces) and `:74` (morphisms of
   locally ringed spaces), the declarations of `def-pc-scheme`.
2. A scheme morphism f from X to S: `(f : X ⟶ S)`. PASS; no property or extra
   structure on this morphism is implicitly assumed.
3. f locally quasi-finite: `(hf : IsLocallyQuasiFinite f)`. PASS. I read
   `QuasiFiniteMorphism.lean:45` and its `IsQuasiFiniteAtPoint` definition at line 33.
   They use exactly all points of X, affine neighbourhoods, the `appLE` algebra,
   an explicit finite-type witness and `Algebra.IsQuasiFiniteAtPrime`. I also read
   `QuasiFiniteAtPrime.lean`: this is isolation of the canonical prime in the fibre
   spectrum, under finite type. These are the notions of 01TD and its introductory
   ring convention, not Mathlib's predicate which omits finite type.
4. Arbitrary open subschemes U of X and V of S: `(U : X.Opens) (V : S.Opens)`.
   PASS. I read `Restrict.lean:46`: `toScheme` restricts the locally ringed space to
   the open subset. This is the node's induced open subscheme structure, not an
   unrelated scheme on the same point set.
5. f(U) contained in V: `(e : U ≤ f ⁻¹ᵁ V)`. PASS. This says precisely that every
   point in U maps to V; it assumes neither equality nor surjectivity.
6. The inclusions are open immersions: `U.ι` and `V.ι`, constructed at
   `Restrict.lean:52`, with the instance at line 57. PASS. I read the declaration
   of `def-weil-open-immersion` in `OpenImmersion.lean:38–39`; it is the underlying
   locally ringed space open immersion. Here these properties follow from the
   open-subscheme constructions and add no hypotheses.
7. The unique induced morphism U to V and its square: `f.resLE V U e`. PASS. I read
   `Restrict.lean:775` and `resLE_comp_ι` at line 789. The codomain/source are exactly
   `V.toScheme`/`U.toScheme`, and the square is
   `f.resLE V U e ≫ V.ι = U.ι ≫ f`. Open immersions are monomorphisms
   (`OpenImmersion.lean:550`), so any morphism in the node's square equals this
   canonical one. Naming it instead of binding it and assuming the square drops
   no allowed morphism and no conclusion.
8. The restriction is locally quasi-finite:
   `IsLocallyQuasiFinite (f.resLE V U e)`. PASS. It is the very same dependency
   predicate as in hypothesis 3; no finite-fibre substitute or affine special case.
   The binders retain the order f, its property, U, V, and image containment.

Edge cases: U empty gives a vacuous pointwise conclusion. V empty forces U empty
by e. Empty source and target schemes are allowed. Top opens recover the original
map via the usual open-subscheme isomorphisms. Opens need not be affine or
quasi-compact. No field, characteristic, reducedness, or finiteness restriction is
present. The explicit arbitrary universe u is the universe of Mathlib's scheme
category and of the dependency predicate; opens stay in that universe. Any pair
of schemes can be considered in a common universe. There is no test-scheme
quantification in a smaller universe. Index sets, zero modules, and n = 0 are not
parameters of this statement; zero rings and their empty spectra are covered.

Independent searches, with wording different from the first reader's:

- LeanFinder via msearch.py: "local quasi finiteness preserved by shrinking domain
  and codomain to open subschemes". Eight hits; I opened the relevant Mathlib
  restriction instances and definition in `Morphisms/QuasiFinite.lean:53–75,129–134`.
  `instLocallyQuasiFiniteResLE` concerns the other predicate (no finite type);
  `instLocallyOfFiniteTypeResLE` covers only the finite-type clause.
- LeanSearch via msearch.py: "A scheme morphism quasi finite at every point remains
  so on open restrictions". Service unavailable (Internal Server Error), recorded
  by the search tool; no mathematical verdict is inferred from unavailability.
- Loogle via msearch.py: `AlgebraicGeometry.Scheme.Hom.resLE,
  AlgebraicGeometry.LocallyQuasiFinite`. One hit: the same Mathlib restriction
  instance, not the project's Stacks-compatible statement.
- Local rg on Mathlib, the source's `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: `IsLocallyQuasiFinite`, quasiFinite/restriction
  names, and `isLocallyQuasiFinite_resLE`; also resLE/restrict/restriction/shrinking
  searches in quasi-finite modules. Only the dependency definition and the
  different `QuasiFiniteLocusOpen` assertion occur in the project. No existing
  exact declaration and no name collision was found. The existing open-restriction
  construction is reused, not defined a second time.

H5–H9: no definitions or instances are added, and the sole proof is `by sorry`.
The module and theorem docstrings name the source and blueprint id. All five proof
steps match the node: local finite type, the smaller affine pair, fibre isolation
and 01TH (4), equality of the restricted section maps and prime, then the universal
pointwise conclusion. The sole import provides the predicate and its scheme
constructions. All binders and the universe are bound; the namespace is upstream
compatible; every Lean line has at most 100 characters. The node's recorded
`lean.statement` equals the file's signature verbatim.

Mismatches and repairs: none. I kept the correct Lean and node unchanged and added
only this independent reading. Validation uses the prescribed single-file server
compile and both delivery runs; their results are recorded below.

Validation results: scompile.py compiled the 46-line module cleanly in 1.6 seconds
(exit code 0). The direct signature/line-length check passed. deliver2.py --no-push
printed OK: the delivery passes preflight and compiles, with nothing pushed during
that dry run.
