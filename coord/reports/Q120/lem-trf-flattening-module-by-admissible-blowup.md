## Worker report

The module `Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup` states
`AlgebraicGeometry.exists_flat_finitePresentation_moduleStrictTransform_admissibleBlowup`
with `sorry`. There are no definitions or other postponed theorems. I read the
statement and complete proof of Stacks Tag 0815, `flat.tex`,
`theorem-flatten-module` (lines 9017–9129), and the item and its seven original
statement dependencies. The natural-language statement is unchanged.

Hypotheses and conclusion, clause by clause:

- The schemes are `{S X : Scheme.{u}}`, with the universe explicitly bound.
  `[CompactSpace S]` and `[QuasiSeparatedSpace S]` render the qcqs base.
- `(f : X ⟶ S) [QuasiCompact f] [LocallyOfFinitePresentation f]` renders the
  quasi-compact, locally finitely presented morphism. There is no quasi-separatedness
  assumption on `f` or `X`. Stacks phrases quasi-compactness as quasi-compactness of
  `X`; for a morphism to the qcqs base these formulations agree.
- `(F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]` renders precisely the
  finite-type quasi-coherent module, without coherence or global finite presentation.
- `(U : S.Opens) (hU : IsCompact (U : Set S))` is the quasi-compact open in the base.
- `hfp` uses `Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι` to restrict the actual
  module to `X_U`, and asks for its `IsFinitePresentation`. This is restriction to
  the open subscheme, not an arbitrary module on a chosen fibre product.
- `hflat` quantifies over every `x : X` with `f x ∈ U`. Its module is the actual
  stalk of `F`, given by `RingedSpace.moduleStalkFunctor`; its scalar action comes
  from restriction of scalars along `(f.stalkMap x).hom`. It asserts flatness over
  `S.presheaf.stalk (f x)`. The stalk of the open `U` at `f x` is canonically this
  local ring, so this says exactly that `F|X_U` is flat over `U`.
- The existential `B : IsAdmissible S U` retains its finite-type quasi-coherent
  centre `B.I` and disjointness of its support from `U`. The modified base is
  the canonical `B.I.blowup` with map `B.I.blowupMap`. This provides the requested
  blowup datum with the identity identification with its own blowup; choosing this
  representative does not restrict the existence assertion.
- The first conclusion quantifies over all points of the explicitly scheme-valued
  pullback `Limits.pullback f B.I.blowupMap`. It asserts flatness of the stalk of
  `Scheme.Modules.moduleStrictTransform f B.I F` over the base stalk, with scalar
  restriction along the second projection's stalk map. Thus flatness concerns
  the strict transform as a module over the modified base, not flatness of the
  ambient morphism.
- The second conclusion is `IsFinitePresentation` of that same canonical strict
  transform as a module on the full ambient fibre product. It is not merely finite
  presentation on the open or on the scheme strict transform.

The strict-transform API requires the module-form finite-type witness for the ideal.
Both occurrences explicitly supply
`B.I.isFiniteType_toModules_sheaf B.finiteType`. This uses the already landed
`lem-pqf-finite-type-ideal-module`, rather than adding a hypothesis or an extra
existential conclusion. I added that node and the already landed
`def-pc-module-stalk-functor` to `stmt_deps` to record the interfaces used in the type.
No new nodes or dependency replacements are delivered.

Dependency declarations read and used:

- The convention-only `def-weil-pbc-scheme-conventions` declares no new notion.
  Its qcqs conventions use Mathlib `CompactSpace` and `QuasiSeparatedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, and the scheme `QuasiSeparatedSpace`
  interpretation (class source at line 50 and following equivalence).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (class at line 45).
- `WeilConjectures.Blowup.AdmissibleBlowup`:
  `AlgebraicGeometry.IsAdmissible` (full structure at line 129), with fields
  `I`, `finiteType`, and `disjoint_support`.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`:
  `AlgebraicGeometry.Scheme.Modules.moduleStrictTransform`; I read all four
  construction declarations and their docstrings. This is the cokernel of the
  kernel inclusion of the canonical restriction map to the complement of the
  exceptional inverse image, retaining the centre.
- `WeilConjectures.AlgebraicGeometry.Coherent`: the full live source obtained by
  `scompile.py --source`, including the docstring fixing quasi-coherence and finite
  type as Mathlib's classes. No `IsCoherent` assumption is used.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.IsFiniteType` (line 142); and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent`, `SheafOfModules.IsFinitePresentation` (line 267).
- `Sheaf.AlgebraicGeometry.FiniteTypeIdealModule`:
  `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_toModules_sheaf`, with
  its full signature, construction proof, and source docstring read.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` (definition at line 104),
  using the actual underlying abelian sheaf stalk and its ordinary local-ring action.
  I checked the complete current source with `scompile.py --source` and imported
  this recorded upstream module in place of its retired side-module name.
- Mathlib `Scheme.Modules.restrictFunctor` (Modules/Sheaf.lean:348) restricts to
  the open subscheme; `ModuleCat.restrictScalars` supplies the explicit action.

All currently stated proof dependencies are imported without `public` unless also
needed in the statement. The module docstring records the complete 13-step DAG
proof: induction, etale localization, elementary devissage, finite-presentation and
flatness checks, affine pushforward, generic freeness, free subtraction and support
dimension drop, transformed exactness, descent/composition, and the final dense-open
finite-presentation argument. Proof dependencies currently having neither `lean`
nor `mathlib_match` are not imported: etale-flattening-descent,
elementary-module-devissage, strict-transform-affine-pushforward, generic-free-blowup,
module-admissible-blowup-calculus, free-subtraction-flatness,
strict-transform-universal-exact, boundary-divisor-cartier, and
flat-finite-type-dense-presentation (each with its DAG prefix as in the item).

Edge cases checked: `U = ∅` is permitted, so both open hypotheses can be vacuous;
no density is imposed. `U = S` is permitted and the unit-ideal blowup is available
when the module is already flat and finitely presented. The empty base and empty
source are permitted; no `Nonempty` assumption occurs. The zero module is allowed.
No relative dimension, characteristic, Noetherianity, separatedness of `f`, or
surjectivity is imposed. All stalks and the pullback have the scheme universe `u`.
The first compile exposed an ambiguity in coercing a categorical pullback directly
to a point type; explicitly annotating that pullback as `Scheme.{u}` fixed it.

Searches actually run through `msearch.py Q120 <item>`:

- `leanfinder`: “A finite type quasi coherent module flat and finitely presented
  over an open becomes flat and finitely presented after an admissible blowup of
  the base”. Eight hits concerned finite presentations, ordinary flatness and
  universal openness; none states flattening by blowup.
- `loogle`: `AlgebraicGeometry.IsAdmissible, SheafOfModules.IsFinitePresentation`.
  Zero hits; `IsAdmissible` is unknown to the Mathlib search service.
- `grep`: `flatten|Flatten|StrictTransform` in Mathlib `AlgebraicGeometry`.
  Zero hits.
- `leansearch`: “A quasi coherent finite type module becomes flat after an
  admissible blowup”. Eight ordinary module flatness/localization hits, no match.
- Direct `rg` in upstream `WeilConjectures`, including `Blowup` and
  `Compactification`, found comments explicitly saying that module flattening is
  absent from the formalized upstream route. Searching by the exact item id found
  no declaration. Direct `rg` in `lean/Sheaf` found the scheme-flattening theorem,
  whose proof cites this module theorem, and unrelated uses of “flatten”; no match.
  The proposed full declaration name has no hit in `dag/lean_names_upstream.json`,
  upstream, or the published side sources.
- Direct search for `toModules.IsFiniteType` located the existing ideal-module
  bridge and its DAG node, which are reused.

Validation: `scompile.py Q120 <item> <module-file>` passed for both its sandbox and
library-path checks, with no warnings (5.3 and 5.4 seconds respectively). The only
proof in this delivery is the required `sorry` for the item's theorem. No statement
correction or disputed mathematical assertion was needed.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
