## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiExcellentEtaleDirectImageFiniteness` states
`AlgebraicGeometry.Etale.quasiExcellent_etale_direct_image_finiteness`, with one
postponed theorem and no new definitions. The node statement is unchanged.

Hypothesis and conclusion correspondence:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Finite field B of characteristic ell: `(B : Type (u + 1)) [Field B] [Finite B]
  [CharP B ell]`. No coefficient field embedding or ground field is assumed.
- The schemes V and T: `{V T : Scheme.{u}}`.
- Both schemes quasi-compact and quasi-separated: `[CompactSpace V]
  [QuasiSeparatedSpace V] [CompactSpace T] [QuasiSeparatedSpace T]`.
- The morphism and finite presentation: `(g : V ⟶ T)
  [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]`.
  This is precisely the Stacks 01TP convention recorded by both convention nodes.
- The two permitted alternatives are the disjunction `hcase : IsProper g ∨ (...)`.
  In the second alternative, `∀ U : T.affineOpens, IsQuasiExcellent Γ(T, U.1)`
  quantifies over every affine open and uses the dependency's ring predicate;
  `∀ t : T, IsUnit (ell : T.presheaf.stalk t)` says ell is invertible everywhere.
  Being a unit in every local ring is equivalent to invertibility on the scheme.
- Ordinary small etale sites and constant B-module coefficients are rendered by
  `Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)` and the same expression for T.
  These are the fixed-coefficient module sheaves authorized by the dependency records.
- Derived direct image is `rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) g`.
  The first conjunct quantifies over K in the existing bounded-below derived category
  and assumes `DerivedCategory.isBoundedConstructible B V K.obj`; its output is
  `DerivedCategory.isBoundedConstructible B T` of the underlying derived image.
  This covers every bounded constructible complex: the bounded cohomology interval
  implies bounded-below cohomology, and D-plus is the corresponding full subcategory.
  There is no choice of a representative or alternate derived functor in the statement.
- The second conjunct is `IsProper g → ∃ d : ℕ, ∀ M q, (d : ℤ) < q → IsZero ...`.
  Natural d expresses exactly an integer d >= 0. The quantifier is outside all module
  sheaves M, including nonconstructible M, so the bound is independent of M.
  Its last term is degree-q homology of Rg_* of the degree-zero single complex of M,
  exactly R^q g_* M. Degrees q are arbitrary integers. Properness is a premise only
  here; no uniform bound is asserted for a merely quasi-excellent nonproper map.
  In the proper branch hcase needs no quasi-excellence or unit condition.

Dependencies read and reused:

- `def-weil-scheme-morphism-properties` and `def-weil-pbc-scheme-conventions` are
  convention records, not declarations. Their leaves give Mathlib's `Scheme`,
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`, and `IsProper`.
  Read the full class definitions in Morphisms/FinitePresentation, QuasiCompact,
  QuasiSeparated and Proper; scheme qcqs is expressed on its underlying space.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsQuasiExcellent`:
  Noetherian, G-ring, and open regular locus for every finite-type algebra.
  Read its full module and docstrings; no scheme-level duplicate is introduced.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`; the recorded
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` now lives in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, also imported.
  Read the actual signatures and docstrings in both modules. The latter is the
  right-derived functor of the former on D-plus.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`
  (read using `scompile.py --source` because absent from the older local checkout),
  and `DerivedCategory.Plus`, its single and homology functors. The underlying
  category is `AlgebraicGeometry.Etale.DerivedCategoryModule`, whose full abbreviation
  and docstring were read in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
  Read both local module and current source via `scompile.py --source`.
  This is finite-value constructibility of every cohomology sheaf together with
  vanishing outside an integer interval, not the older upstream predicate.

All recorded, stated proof-dependency modules are imported without `public`.
The two new stage-1 proof inputs, `lem-per-quasi-excellent-finite-type-stability`
and `lem-per-gabber-open-immersion-sheaf-finiteness`, have no Lean declaration and
therefore no module to import; their explicit proof steps remain in the docstring.
The docstring gives all eight proof steps with their dependency identifiers.

Source checks: read Bhatt--Scholze Theorem 6.7.1 and Remark 6.7.3 in the supplied PDF,
and ILO Expose XIII 1.1.1, 1.1.2 and 2.1.2 in its supplied PDF. ILO states the bound
for each constructible sheaf and explicitly handles infinite-dimensional bases in
section 3. This delivery respects the node's proper-only all-sheaf uniform bound.
Read also the current blueprint ancestor's Artin--Gabber proof, Step 3.

Edge cases checked before writing:

- g = identity: derived image is identity and the proper bound may be zero.
- V empty, including T empty: image and all higher images are zero. Affine opens
  include the empty open, whose zero coordinate ring is allowed by IsQuasiExcellent.
- K = zero and M = zero: output and vanishing have their usual categorical meaning.
- ell equal to a residue characteristic: proper case is still included. For a
  nonproper map over that characteristic, the unit condition excludes the known
  Artin--Schreier counterexamples (e.g. affine line over an algebraically closed field).
- Nonproper and nonseparated finite-presentation maps are allowed; no separatedness,
  dimension bound, Noetherianity instance or field-of-definition binder is added.
- d = 0 and q = 0: the strict inequality excludes q = 0 from the claimed vanishing.
- B is any finite extension of the prime field, not only the prime field itself.
- The scheme universe u and coefficient/module universe u+1 follow the existing
  declarations; no separate smaller test-algebra universe or new equality is imposed.

Searches for an existing exact declaration (2026-10-18):

- msearch.py leanfinder: "Derived etale direct image preserves bounded constructible
  complexes for proper morphisms or quasi excellent bases with invertible finite
  field coefficients" returned eight etale morphism/constructible image declarations,
  none this theorem.
- msearch.py loogle: "IsQuasiExcellent, isBoundedConstructible,
  rightDerivedLowerStarPlus" returned zero hits, unknown IsQuasiExcellent.
- msearch.py grep: "quasiExcellent|QuasiExcellent|constructible.*direct|finiteness"
  in Mathlib/AlgebraicGeometry returned three unrelated finiteness imports/comments.
- msearch.py leansearch: "Etale derived direct image finiteness over quasi excellent
  schemes for finite field coefficients" returned eight etale morphism and finite
  presentation declarations, none direct-image finiteness.
- rg of the item id and quasi-excellent/direct-image/constructible names in
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures and lean/Sheaf found the shared
  ring predicate, and proper/finite-type direct-image results restricted to schemes
  over a field. These have extra ground-field and coefficient hypotheses and do
  not give the present arbitrary-base disjunction. Upstream Stability.lean itself
  describes the missing quasi-excellent hypothesis for its different amplitude
  statements. No existing exact declaration was found.
- rg in dag/lean_names_upstream.json for quasi-excellent names gave no match.

No new nodes, dependency repairs, statement corrections or disputed statements.

## Second reading by N7

Single-worker clause-by-clause reread against the unchanged node: both disjuncts
are present, every finite-presentation and qcqs hypothesis is bound, B is finite
and a field of the specified prime characteristic, the affine-open ring predicate
is reused, and all terms are on ordinary small etale sites. The first conjunct
covers bounded constructible inputs in D-plus; boundedness supplies membership
in D-plus. The second conjunct has d outside M and q and assumes properness,
without introducing a ground field, Noetherianity, excellence, a dimension bound,
or invertibility in the proper case. No mismatch was found and no correction
was required. Independent review is the maintainer's delivery review, as specified
in the dispatcher brief; no second agent was started.
