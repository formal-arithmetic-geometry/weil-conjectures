## Worker report

The module `Sheaf.AlgebraicGeometry.OpenDirectImageClassicalAmplitude` states
`AlgebraicGeometry.ProEtale.openDirectImage_classical_amplitude`. Its only proof is
`sorry`. It states the unchanged node, including all three numbered clauses. There
are no new definitions, new nodes, dependency repairs, or statement corrections.

The source read is the complete main-20261015 blueprint node
`sec-six-functors-basics/sk-cor-geo-open-finiteness-ii/det-geo-open-finiteness-ii-amplitude.md`,
and its unit `_section.md`. The six-step natural-language proof in the theorem
docstring follows the node's proof, including the module/abelian comparison without
assuming that forgetting coefficients preserves injectives.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| A finite ring Λ | `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]`; no commutativity or nonzero-ring assumption |
| ℓ-power annihilation for some r ≥ 1 | `(ℓ : ℕ) (hΛ : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : Λ, (ℓ ^ r) • x = 0)`; additive natural-number multiplication is multiplication by the integer scalar, so this says exactly ℓ^r Λ = 0 |
| Finite-type k-schemes X and Y | `(X Y : Scheme.{u})`, `X.Over (Spec (.of k))`, `Y.Over (Spec (.of k))`, and both `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism |
| Open immersion of k-schemes j | `(j : X ⟶ Y) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]` |
| d = cd(j) < infinity | `∃ d : ℕ, (@Scheme.Hom.torsionEtaleCohomologicalDimension ... j ... ...) = (d : ℕ∞) ∧ ...`; a natural-number representative exists exactly when this ENat-valued dimension is finite, and equality forces it to be the specified least dimension |
| qcqs needed to form cd(j) | Explicit arguments to the recorded dimension use `quasiCompact_iff_compactSpace` on the structure morphism, `LocallyOfFiniteType.isLocallyNoetherian`, `IsLocallyNoetherian.quasiSeparatedSpace`, `quasiCompact_of_compactSpace`, and `QuasiSeparated.of_quasiSeparatedSpace`. These are consequences of the hypotheses, not additional binders. |
| Clause (1), every module sheaf F and q > d | First universal conjunct, `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and `q : ℤ`, with `(d : ℤ) < q` |
| Clause (1), R^q j_et,* F = 0 | `IsZero` of `DerivedCategory.Plus.homologyFunctor ... q` on `Etale.rightDerivedLowerStarPlus ... j` applied to `DerivedCategory.Plus.singleFunctor ... 0` of F |
| Clause (2), every such F and q > d | Second universal conjunct, with exactly the same F, degree, and inequality |
| Clause (2), H^q(Rj_proet,* ν_X^*F) = 0 | `IsZero` of pro-etale `DerivedCategory.Plus.homologyFunctor ... q` on `(lowerStar ... j).rightDerivedFunctorPlus.obj` of `(comparisonUpperStar ... X).mapDerivedCategoryPlus.obj` of F in degree zero |
| Clause (3), M in D+ with cohomology in [a,b] | Third universal conjunct quantifies `(a b : ℤ)` and `M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`; its hypothesis is `∀ q : ℤ, (q < a ∨ b < q) → IsZero (...)` |
| Clause (3), image has cohomology in [a,b+d] | Its conclusion is `∀ q : ℤ, (q < a ∨ b + (d : ℤ) < q) → IsZero (...)`, on the same derived direct image of the canonical comparison pullback |

The fixed-ring sheaf presentation is the one used by the recorded
`Scheme.proEtaleSiteComparisonModules`: its left adjoint is definitionally
`ProEtale.comparisonUpperStar`. The imported module
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` identifies fixed-ring etale
module sheaves with modules over `finiteCoefficientEtaleRingSheaf` via
`finiteCoefficientEtaleRealization_isEquivalence`, and fixed-ring pro-etale module
sheaves with modules over `finiteCoefficientRingSheaf` via
`finiteCoefficientRealization_isEquivalence_ring`. Its
`finiteCoefficientComparison` is definitionally comparison inverse image followed
by this realization. Thus no coefficient category or inverse image has been
replaced: these are the recorded equivalent presentations. The finite ring is
discrete without needing an extra topology binder in the fixed-ring encoding.
The common value universe is u+1, matching both small sites and the recorded
comparison interface. The schemes range over arbitrary u.

The bounded-below right derived direct images are the recorded injective-resolution
models: `Etale.rightDerivedLowerStarPlus` unfolds to
`(Etale.lowerStar ... j).rightDerivedFunctorPlus`, and the pro-etale clause uses
that generic bounded-below right derived functor directly. The restriction of
the K-injective-derived construction to D+ is determined by the same universal
property. No unrelated map, arbitrary choice of functor, or assumed amplitude
is introduced.

Dependency declarations read and used:

- `def-kun-cd`: `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`,
  `Scheme.torsionEtaleCohomologicalDimension` and
  `Scheme.Hom.torsionEtaleCohomologicalDimension`; the latter is used directly,
  with the source's nonnegative/empty-scheme convention.
- `def-weil-pbc-site-comparison-morphism`:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`, whose actual adjoint functors are
  `ProEtale.comparisonUpperStar` and `ProEtale.comparisonLowerStar` from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `def-weil-pbc-proetale-modules`:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`,
  `ProEtale.FiniteCoefficientModules`, `finiteCoefficientEtaleRealization`,
  `finiteCoefficientRealization`, and `finiteCoefficientDerivedComparison`,
  with the exact equivalences discussed above.
- `def-weil-scheme-over-base`: Mathlib's
  `AlgebraicGeometry.Scheme.Over` and `Scheme.Hom.IsOver`,
  `Mathlib.AlgebraicGeometry.Over`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its quasi-compact imports.
- `def-sfb-right-derived-functor`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its universal property;
  the statement uses the canonical bounded-below models described above.

All stated proof-dependency modules are imported without `public` (or publicly
when also a statement dependency). This includes the recorded
`WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf`, whose
current source was read with `scompile.py --source` because it is absent from
the older local source checkout. No dependency record is changed.

Edge cases checked against the statement and proof:

- Empty X or Y: no nonemptiness is imposed; the nonnegative cd convention
  supplies d=0 for the empty source. The explicit qcqs arguments still apply.
- Identity j: cd(j)=0; clauses (1)-(2) give positive-degree vanishing and
  clause (3) preserves [a,b].
- Zero ring, zero sheaf, and zero complex: allowed. No `Nontrivial` is added.
- Characteristic k = ℓ: allowed; no invertibility or characteristic restriction.
- Finite noncommutative rings: `[Ring Λ]`, left `ModuleCat` modules throughout.
- r=1 is included. No primality hypothesis on ℓ is added beyond the node text;
  the theorem is valid even for all natural ℓ since finiteness already makes
  every coefficient module torsion.
- a=b gives the shifted-sheaf case [a,a+d]. Arbitrary negative a,b and arbitrary
  gaps in cohomology are allowed. When a>b the interval hypothesis forces all
  input cohomology to vanish; no `a ≤ b` assumption silently removes this case.
- q=d is deliberately not asserted to vanish in clauses (1)-(2). q may be any
  integer, exactly as in the recorded cd definition.

Searches for an existing statement (no exact match):

- `msearch.py ... leansearch` query: "The derived direct image of an open
  immersion of finite type schemes over a field has finite cohomological
  amplitude on torsion etale sheaves and their proetale pullbacks". Eight
  hits: open-immersion definitions, open ranges, finite-type facts, scheme
  structure maps, stalk restriction, and opens functors; no amplitude theorem.

- `msearch.py ... leanfinder` query: "The derived direct image of an open
  immersion of finite type schemes over a field has bounded cohomological
  amplitude on torsion etale and proetale module sheaves". Eight hits: etale
  morphism/finite-type facts, derived t-structure images, and affine-limit
  section facts; none states this amplitude theorem.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.Scheme.Hom.torsionEtaleCohomologicalDimension, DerivedCategory.IsLE`.
  No hits; the Mathlib-only service does not know the project's dimension
  declaration. Repeated with known names
  `CategoryTheory.Functor.rightDerived, AlgebraicGeometry.IsOpenImmersion`:
  zero hits.
- `msearch.py ... grep` query `cohomologicalDimension|rightDerived.*IsLE`
  in Mathlib `AlgebraicGeometry`: zero hits.
- `rg -n 'open.*[Aa]mplitude|[Aa]mplitude.*open|torsionEtaleCohomologicalDimension|det-geo-open-finiteness-ii-amplitude'`
  over upstream `WeilConjectures` and project `lean/Sheaf`: upstream hits
  concern open extension by zero, Tor amplitude or stability; project hits
  concern definitions and other finite-dimension results. No statement of
  these three clauses. The literal node id has no upstream hit.
- Exact new declaration-name search in Mathlib, upstream, project `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no existing declaration.

Validation: the delivered module passed `scompile.py Q102
 det-geo-open-finiteness-ii-amplitude` with the default 60-second per-file limit,
without errors or warnings. All universes and variables are explicitly bound
and `autoImplicit` is disabled. Every line is at most 100 characters. The node
copy changes only `lean`; its signature is extracted verbatim from the module.
The UTC date in the record is from the machine clock, as required.

No STATEMENT-DISPUTED issue was found.

## Earlier second reading (a previous round; superseded)

I independently read the sandbox node and theorem against the main-20261015
blueprint node and its unit `_section.md`. I also read Stacks
`etale-cohomology.tex`, definition-cd-f and lemma-finite-cd (0F0Z/0F10),
`proetale.tex`, lemma-morphism-comparison (09A6), and
`sites-cohomology.tex`, lemma-modules-abelian-unbounded (0D6J) and
lemma-cohomology-modules-abelian-agree (03FD). The source dimension is relative
torsion dimension: no finiteness of the absolute dimension of k is required.
09A6 assumes a qcqs morphism, not an invertible torsion prime. The blueprint
statement is unchanged in the node copy; there is no statement_change and no
repair note for this item.

My object/hypothesis/conclusion checklist, matched to the actual signature:

| Source item | Lean rendering and verdict |
| --- | --- |
| Field k | `(k : Type u) [Field k]`. Exact; not algebraically closed or separably closed. |
| Finite ring Λ, left modules | `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]` and `ModuleCat.{u + 1} Λ`. Exact; no commutativity or nontriviality assumption. |
| A power ℓ^r annihilates Λ, for some r ≥ 1 | `(ℓ : ℕ) (hΛ : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : Λ, (ℓ ^ r) • x = 0)`. Exact additive integer annihilation. No extra primality or invertibility binder. |
| X,Y finite-type k-schemes | `(X Y : Scheme.{u})`, both `Over (Spec (.of k))`, and both `LocallyOfFiniteType` and `QuasiCompact` structure morphisms. Exact finite-type conjunction from the recorded dependency. |
| Open k-immersion j:X→Y | `(j : X ⟶ Y) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]`. Exact, including compatibility of the two structure morphisms. |
| d is cd(j), and is finite | `∃ d : ℕ, (@Scheme.Hom.torsionEtaleCohomologicalDimension ... j ... ...) = (d : ℕ∞) ∧ ...`. Exact: equality fixes the least recorded bound, rather than an arbitrary bound. ENat has a natural-number representative exactly when finite. |
| qcqs needed to form cd(j) | Explicit arguments construct `QuasiCompact j` and `QuasiSeparated j` from compactness of X and locally Noetherianity of X,Y. These are proof terms from the stated finite-type hypotheses, not additional hypotheses. |
| (1) Arbitrary etale module sheaf F, every q>d | First universal conjunct has `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, `q : ℤ`, and `(d : ℤ) < q`. Exact; no finite/constructible condition on F. |
| (1) R^q j_et,* F=0 | First `IsZero` is Plus homology q of `Etale.rightDerivedLowerStarPlus ... j` of `singleFunctor ... 0` of F. Exact higher image of the degree-zero sheaf. |
| (2) Every such F, every q>d | Second universal conjunct repeats exactly that sheaf category and strict inequality. Exact. |
| (2) H^q(Rj_proet,* ν_X^*F)=0 | Second `IsZero` uses `(lowerStar ... j).rightDerivedFunctorPlus` after `(comparisonUpperStar ... X).mapDerivedCategoryPlus` on F[0]. Exact canonical comparison pullback and direct image. |
| (3) Integers a,b and M∈D+ on X_et | Third conjunct binds `(a b : ℤ)` and `M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Exact; a,b are not assumed nonnegative or ordered. |
| (3) Input cohomology supported in [a,b] | Hypothesis `∀ q : ℤ, (q < a ∨ b < q) → IsZero (...)` for homology of M. Exact closed interval. |
| (3) Output supported in [a,b+d] | Conclusion `∀ q : ℤ, (q < a ∨ b + (d : ℤ) < q) → IsZero (...)` for the same pro-etale derived image of comparison pullback. Exact lower and upper bound, and correct addition sign. |

I opened every statement-dependency declaration, not just its record:
`Scheme.Hom.torsionEtaleCohomologicalDimension` takes precisely qcqs j and
defines the infimum of nonnegative bounds on torsion abelian higher images;
it uses the same Plus homology and degree-zero embedding as clause (1).
`Scheme.proEtaleSiteComparisonModules` is the actual adjunction with left
functor `comparisonUpperStar`, whose definition is the specified inclusion's
Kan extension followed by sheafification. In the shared framework I read
`ProEtale.lowerStar`: it is restriction along the scheme base-change functor,
so evaluates on V×_Y X, as required. There is no arbitrary functor parameter.

For `def-weil-pbc-proetale-modules`, I read the actual coefficient presheaf,
ring sheaf, module categories, both realization functors, their equivalence
statements, and `finiteCoefficientComparison`/`finiteCoefficientDerivedComparison`.
They justify using the fixed-ring sheaf presentation: comparison is exactly
comparisonUpperStar followed by realization, and realization identifies it
with the prescribed ring-sheaf presentation, including noncommutative rings.
The discrete topology is canonical here and is not an omitted hypothesis
on an independently topologized ring. The u+1 coefficient values agree with
the common larger universe of the recorded small-site interfaces; the
scheme universe u is arbitrary and site object/morphism universes have not
been forced equal.

I read Mathlib `Scheme.Over`, `Scheme.Hom.IsOver`, `IsOpenImmersion`,
`LocallyOfFiniteType`, and `QuasiCompact` at their definitions. They render
exactly the node's geometric objects. I also read
`rightDerivedFunctorOfQuasiIsoResolutions` and its universal property, and
Mathlib `rightDerivedFunctorPlus` and its unit, plus
`Etale.rightDerivedLowerStarPlus`: the latter is definitionally the generic
bounded-below right derived functor of Etale.lowerStar. Both bounded-below
constructions in this statement compute injective resolutions; their
identification with the restriction of the K-injective model follows from
the recorded universal property. No replacement of the right-derived
notion or dependency repair is needed. The supporting finite-dimension,
comparison-direct-image, and finite-level-exactness signatures were also
read and supply the hypotheses used in the proof docstring.

Edge cases: empty X and empty Y are admitted, and the dimension convention
assigns zero to the empty-source functor. Identity j and d=0 preserve [a,b].
The zero ring, zero sheaf and zero complex are allowed. Degrees q=d are
correctly excluded from the two strict vanishing bounds; all integer
degrees, negative endpoints, a=b, a>b, and gaps in cohomology are admitted.
For a>b the input hypothesis is acyclicity, so its output is acyclic too.
The case r=1 is present. Characteristic k=ℓ is not excluded. No index-family
binder occurs, so no nonempty-index or small-index restriction arises.

Independent uniqueness searches, using words beyond the first worker's:

- LeanFinder: “For an open embedding between schemes of finite type over a
  field higher direct images of torsion module sheaves vanish above a
  uniform finite bound”. Eight hits: affine-limit section vanishing,
  derived IsGE/IsLE, and injective Ext facts; none gives this statement.
- Loogle: `"rightDerived", "IsZero"`. One hit,
  `Functor.isZero_rightDerived_obj_injective_succ`; this assumes an
  injective object and is not the required uniform geometric bound.
- Mathlib grep through msearch: `finite.*cohomological|cohomological.*amplitude`.
  No hits.
- LeanSearch: “Higher direct images under an open immersion of schemes over
  a field preserve a bounded cohomological interval up to the torsion
  cohomological dimension”. Eight hits are open-immersion image/open-range
  facts, with no higher-image bound.
- Direct rg in Mathlib, upstream WeilConjectures, shared lean/Sheaf and the
  upstream-name inventory: exact new declaration name absent. Concept
  searches `cohomological.*amplitude|amplitude.*cohomological` and
  `torsionEtaleCohomologicalDimension` find general derived bounds,
  compact-support/exceptional functors, dimension definitions and 0F10;
  none states these three clauses on classical pro-etale images. I opened
  the finite relative-dimension theorem: it supplies only finiteness,
  not this coefficient/sheaf/complex amplitude conclusion.

No mismatch found, and no Lean or node changes were needed. No new nodes
or sibling dependency modules exist to review. The module contains one
theorem with exactly `sorry`, no definitions, private notions, local
instances or notation. The module and declaration docstrings name the
source/blueprint; the six proof steps match the node, including the
noncommutative coefficient comparison and finite abutment filtration.
The node differs from the base only in lean; lean.statement is verbatim
the signature. All binders and universes are bound, autoImplicit is false,
and every Lean line is at most 100 characters.

Second-reader compilation with the prescribed scompile.py wrapper passed
both its sandbox and library checks cleanly (1.8 seconds each), with the
default 60-second limit. Only this report was appended.

Repair note (2026-10-17): the returned immutable head reported `Extra data: line 21 column 2 (char 3020)` while reading the item node JSON. I validated the retained node with `python3 -m json.tool`; it is now a single valid JSON document. The Lean module had broad imports that caused a duplicate declaration when the live overlay also supplied the relocated finite-coefficient open-immersion module. I removed only those unused broad imports and retained the canonical declarations through `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`; the required `scompile.py` check then passed for both the sandbox and library files. The item statement and `lean.statement` are unchanged.

## Second reading by Q102

This is the current independent reading, on 2026-10-17 UTC; the earlier reading and
repair note above are retained as history. I read the sandbox node, its complete
Lean module, the main-20261015 blueprint statement, proof, and unit `_section.md`.
I read Stacks `etale-cohomology.tex`, definition-cd-f and lemma-finite-cd (0F0Z,
0F10), `proetale.tex`, lemma-morphism-comparison (09A6), and
`sites-cohomology.tex`, lemma-cohomology-modules-abelian-agree (03FD) and
lemma-modules-abelian-unbounded (0D6J). The relative dimension theorem's first
clause needs no finite absolute cohomological dimension of k. The comparison
lemma assumes qcqs of the morphism, without a characteristic restriction.

My object, hypothesis and conclusion checklist is:

| Node item | Actual Lean rendering; verdict |
| --- | --- |
| A field k | `(k : Type u) [Field k]`; exact, with arbitrary scheme universe u. |
| A finite associative ring Λ | `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]`; exact, with left modules and no commutativity or nontriviality assumption. |
| ℓ-power annihilation, some r ≥ 1 | `(ℓ : ℕ) (hΛ : ∃ r : ℕ, 1 ≤ r ∧ ∀ x : Λ, (ℓ ^ r) • x = 0)`; exact integer-scalar annihilation, including r=1. |
| Schemes X and Y over k | `(X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]`; exact specified structure morphisms. |
| Both schemes finite type over k | `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism; exact recorded conjunction. |
| Open immersion j of k-schemes | `(j : X ⟶ Y) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]`; exact, including the commuting structure maps. |
| d is cd(j) | `∃ d : ℕ, (@Scheme.Hom.torsionEtaleCohomologicalDimension ... j ... ...) = (d : ℕ∞) ∧ ...`; equality fixes the recorded least nonnegative dimension. |
| Finiteness of d | The same existential gives a finite natural-number representative; exact, without choosing an arbitrary upper bound. |
| qcqs required by the dimension definition | Explicit arguments use `quasiCompact_iff_compactSpace`, `LocallyOfFiniteType.isLocallyNoetherian`, `IsLocallyNoetherian.quasiSeparatedSpace`, `quasiCompact_of_compactSpace`, and `QuasiSeparated.of_quasiSeparatedSpace`; these follow from the hypotheses and add no binders. |
| (1) Every etale module sheaf F and q>d | First conjunct universally binds `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and `q : ℤ`, with `(d : ℤ) < q`; exact, without constructibility or finite stalks. |
| (1) R^q j_et,* F=0 | `IsZero` of Plus homology q of `Etale.rightDerivedLowerStarPlus` applied to `Plus.singleFunctor ... 0` of F; exact higher direct image. |
| (2) Every such F and q>d | Second conjunct repeats the same sheaf category and strict inequality; exact. |
| (2) H^q(Rj_proet,* ν_X^*F)=0 | `IsZero` of pro-etale Plus homology q of `(lowerStar ... j).rightDerivedFunctorPlus.obj`, after `(comparisonUpperStar ... X).mapDerivedCategoryPlus.obj` on F[0]; exact canonical functors. |
| (3) M in D+ and integers a,b | Third conjunct binds `(a b : ℤ)` and `M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`; exact, without an ordering or positivity restriction. |
| (3) Input cohomology in [a,b] | `∀ q : ℤ, (q < a ∨ b < q) → IsZero (...)` for the homology of M; exact closed interval. |
| (3) Output cohomology in [a,b+d] | `∀ q : ℤ, (q < a ∨ b + (d : ℤ) < q) → IsZero (...)` for the same derived comparison pullback and pro-etale direct image; exact both bounds and sign. |

I opened the actual statement-dependency declarations. In
`Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`, the morphism
dimension is the infimum of nonnegative bounds for all torsion abelian etale
sheaves, using the same Plus homology and degree-zero embedding. Mathlib's
`Scheme.Over`, `Scheme.Hom.IsOver`, `IsOpenImmersion`, `LocallyOfFiniteType`, and
`QuasiCompact` have exactly the geometric meanings above.

The current comparison dependency record now names
`Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison`. I read its AsSmall
inclusion, induced topologies, and geometric adjunction, as well as the original
`Scheme.proEtaleSiteComparisonModules` in `ProEtaleSiteComparison`. The newer
module transports the original inclusion by equivalences and retains the original
comparison publicly. The theorem uses that original canonical module inverse
image in its native site presentation; it does not replace the comparison by an
arbitrary functor. In the exact shared pro-etale framework, `comparisonUpperStar`
is the inclusion's left Kan extension followed by sheafification, and `lowerStar`
is restriction along base change, evaluating on V×_Y X. I also read
`coord/pefw-upstream-framework.md`.

In `ProEtaleFiniteModules` I read the continuous-function coefficient presheaf,
its ring sheaf, the module categories, the etale and pro-etale realization
functors and their equivalence statements, and `finiteCoefficientComparison`.
They identify fixed-ring module sheaves with the prescribed coefficient-ring
sheaves, including noncommutative rings; comparison is `comparisonUpperStar`
followed by realization. Thus the signature's encoding is equivalent to the
node's, and the discrete topology is canonically supplied. The common u+1 value
universe is the recorded larger site universe, with no equality imposed between
site object and morphism universes.

I read `rightDerivedFunctorOfQuasiIsoResolutions` and its unit/universal property,
the Plus injective-representative interface, the injective-complex description of
`rightDerivedFunctorPlus`, and `Etale.rightDerivedLowerStarPlus`. The latter is
definitionally the generic Plus right derived functor. Its bounded-below
injective computation gives the same right derived object as the recorded
K-injective model. I read the comparison-direct-image and finite-level signatures
and the module/abelian evaluation comparison. The current sources for
`WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf` and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful` were obtained
through `scompile.py --source`; their signatures give the required sheafified
abelian higher-image description and exact faithful forgetting, respectively.

Edge cases: empty X and Y are admitted, and empty-source cd has value zero.
Identity j and d=0 give no interval enlargement. Zero rings, zero sheaves and
zero complexes are allowed. No invertibility in k, primality of ℓ, or
characteristic restriction is introduced; characteristic k=ℓ is included.
The strict bounds exclude q=d. Negative interval endpoints, a=b, missing
cohomology degrees, and a>b are covered; in the last case M is acyclic. There
is no index-family binder, hence no nonempty-index assumption. Finite rings
can be resized into the coefficient universe, and arbitrary u is quantified.

Independent searches, beyond the first worker's wording:

- LeanFinder: “Uniform vanishing bounds for higher pushforwards of finite torsion
  sheaves along open embeddings of schemes over any field”; eight hits about
  sections, affine limits and qcqs restriction, none giving this theorem.
- LeanSearch: “Higher derived pushforward of torsion module sheaves under an open
  embedding of schemes over a field has bounded amplitude on classical proetale
  complexes”; eight hits about ordinary structure-sheaf/module pushforward and
  restriction, none giving the derived finite-coefficient conclusion.
- Loogle: `"rightDerived", "IsZero"`; only
  `Functor.isZero_rightDerived_obj_injective_succ`, whose source I opened. It
  assumes an injective input and is not a uniform geometric bound.
- Mathlib grep through msearch: `higher.*pushforward.*bound|cohomological.*amplitude`;
  no hits.
- Direct rg of Mathlib, upstream WeilConjectures, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `cohomological.*[Aa]mplitude`,
  `[Aa]mplitude.*cohomological`, `torsionEtaleCohomologicalDimension`, and the exact
  new declaration name: only general amplitude discussions, other functors,
  dimension definitions and the finite-dimension theorem; no exact match.

The mathematical signature needs no correction. There are no new nodes, sibling
modules, private notions, hollow definitions, or statement_change records.
The one theorem has exactly `sorry` as its proof; its source/blueprint docstrings
and six proof steps cover the node's resolution, coefficient comparison,
vanishing, comparison, and finite truncation-filtration arguments.

The mismatch found was in the import plan: the previous repair had removed the
recorded coefficient and right-derived statement modules and all the stated
proof-dependency imports. I restored them, and included the current recorded
small-model comparison module. The full imports compile cleanly now, so the
earlier duplicate-declaration problem did not recur. I also restored the
unchanged base `lean_audit` field missing from the stale sandbox copy, ensuring
the delivered node differs from the current base only in `lean`, and refreshed
its Lean record's UTC date. The JSON parses as one document, `lean.statement`
matches the signature verbatim, all variables and universes are bound with
`autoImplicit false`, and every Lean line is at most 100 characters.

Validation: the prescribed `scompile.py Q102 det-geo-open-finiteness-ii-amplitude
lean/Sheaf/AlgebraicGeometry/OpenDirectImageClassicalAmplitude.lean` passed its
sandbox and library checks, in 2.0 and 2.2 seconds, with no errors or warnings
and the default 60-second limit. No STATEMENT-DISPUTED issue remains.
