## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCompactSupportAmplitude` states
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE`
with the sole postponed proof `sorry`. Its docstring records all nine proof steps and the
nodes they use. The helper `compactSupportAmplitudeCompactification` supplies the already
existing Nagata compactification using real data: finite type over a field gives a locally
Noetherian base, hence quasi-separated, and quasi-compactness gives `CompactSpace Y`.
It is an interface specialization for this theorem, not a new compactification notion.
No node statement is corrected and no dependency record is repaired.

Hypothesis and clause correspondence:

- A field: `(k : Type u) [Field k]`.
- Finite-type schemes over that field: `(X Y : Scheme.{u})`, their
  `Over (Spec (.of k))` structures, and both `LocallyOfFiniteType` and `QuasiCompact`
  on each structure morphism. The convention node specifies finite type as this conjunction.
- A morphism of those schemes over the field: `(f : X ⟶ Y)` and
  `[f.IsOver (Spec (.of k))]` express compatibility with the two structure morphisms.
- Separated and finite type: `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
- Geometric fibres of dimension at most d: `(d : ℕ)` and `hd`, quantified over **every**
  `y : Y`. The fibre is the recorded `pullback f` along
  `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
  (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y`.
  Its underlying space is supplied explicitly by `↑`, and the bound is
  `topologicalKrullDim ... ≤ (d : WithBot ℕ∞)`. No compactified fibre is bounded.
- Finite coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  Commutativity is the coefficient-ring convention of the recorded compact-support and
  ordinary-derived-category nodes, not a new restriction relative to their setting.
- Additive exponent invertible on Y: `[HasInvertibleExponent Λ Y]` from the existing
  upstream coefficient interface. Its full definition is the existence of a positive
  `n` with `(n : Λ) = 0` and `IsUnit (n : Γ(Y, ⊤))`. For a finite commutative ring its
  additive exponent is the order of 1: every additive order divides that order. Hence
  existence of an invertible positive annihilator is equivalent to invertibility of the
  exponent itself (the exponent divides every such annihilator).
- Every etale Λ-module sheaf F: `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`,
  with no finite-module, finite-stalk, constructibility or lisse predicate.
- Degree q greater than 2d: `(q : ℤ) (hq : 2 * (d : ℤ) < q)`. Integers are the ordinary
  derived grading; the inequality makes q positive automatically.
- `R^q f_! F = 0`: `IsZero` of the `DerivedCategory.homologyFunctor` in degree q
  applied to `rightDerivedLowerShriekOfCompactification ...` of the helper's Nagata
  compactification, evaluated on `(DerivedCategory.singleFunctor ... 0).obj F`.
  This is exactly the candidate of def-amb-etale-compact-support. For F[0], the existing
  comparison node identifies every compactification candidate with compactification-
  independent Rf_!: this requires only its bounded-below clause. The main functors and
  homology still act on ordinary **unbounded** categories, not on completed or pro-etale
  categories. `IsZero` means categorical vanishing of the resulting module sheaf.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategories`: its recorded ordinary-derived vocabulary,
  including upstream `AlgebraicGeometry.Etale.DerivedCategoryModule` and Mathlib
  `DerivedCategory.singleFunctor` / `DerivedCategory.homologyFunctor`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, with its full
  signature and docstring: exact degreewise extension by zero followed by the total
  right derived direct image on unbounded derived categories.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, the supremum of chain lengths
  in irreducible closed subsets, valued in `WithBot ℕ∞`.
- `def-weil-pbc-scheme-conventions` is a convention-only record. The declarations its
  statement points to are `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`,
  `Limits.pullback`, `Scheme.fromSpecResidueField`, and `AlgebraicClosure`. The geometric
  fibre is rendered exactly by the inline expression in def-weil-geometric-fibre's record.
- `WeilConjectures.AlgebraicGeometry.InvertibleExponent`: `HasInvertibleExponent`, read
  in full; it has the positive annihilator/unit interpretation detailed above.
- `WeilConjectures.Compactification.NagataCompactification`:
  `AlgebraicGeometry.NagataCompactification`, whose base instances are supplied in the
  helper, not added as theorem hypotheses. This proof dependency is public because the
  statement's real-data helper uses it. Every other proof dependency with a recorded module
  is imported privately, except those already needed publicly for the signature.
  Mathlib-only unrecorded proof leaves need no private declaration copies.

Edge cases checked:

- Empty X and empty geometric fibres are allowed: their dimension is bottom, so the
  dimension bound does not require nonemptiness; extension by zero of their sheaf vanishes.
- Empty Y is allowed; `hd` is vacuous there, but the conclusion is a zero sheaf on the
  empty site, as required. No nonempty hypothesis was added to either scheme.
- d = 0 retains the conclusion precisely for q > 0, including finite or empty fibres.
- q = 2d is not asserted to vanish; negative q is not included by the inequality.
- The zero sheaf and the zero finite ring are allowed; exponent 1 is an admissible
  positive annihilator of the zero ring, and no `Nontrivial Λ` binder excludes it.
- In positive characteristic the actual scheme-unit condition is retained; it is not
  replaced by a condition on k that could incorrectly exclude the empty Y case.
- All points of Y, including nonclosed points, occur in `hd`.
- The size convention is the recorded six-functor encoding: schemes and residue fields
  in u, coefficients and module stalks in u+1. Finite coefficient rings can be lifted;
  no independent smaller test-field universe makes the fibre hypothesis vacuous.

Existing-declaration searches:

- `msearch.py leanfinder`, query "compact support direct image vanishing above twice
  geometric fiber dimension etale finite ring": 8 hits, all algebraic support/basic-open
  results, none the compact-support amplitude theorem.
- `msearch.py loogle`, query
  `rightDerivedLowerShriek, compactlySupportedCohomology, topologicalKrullDim`:
  0 hits, unknown identifier rightDerivedLowerShriek in the Mathlib index.
- `msearch.py grep`, query
  `compactlySupportedCohomology|rightDerivedLowerShriek|topologicalKrullDim` in Mathlib:
  0 hits for the requested amplitude statement.
- `msearch.py leansearch`, query "Etale compact support higher direct images vanish
  above twice the geometric fibre dimension": unavailable, Internal Server Error.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for
  compact support, rightDerivedLowerShriek, geometric fibres, dimension, and exponent
  located the definitions reused above. Upstream Finiteness/DirectImage and
  Stability/DirectImage concern constructibility or different amplitude bounds; they
  do not state this unrestricted sheaf statement with an original-geometric-fibre bound.
- Direct `rg` of `lem-dg-compact-support-amplitude` in upstream found no declaration.
  The exact proposed helper and theorem names were checked for collisions.

Validation: `scompile.py Q01 lem-dg-compact-support-amplitude` compiled the module
cleanly in both its sandbox and library spelling, with no warnings other than the permitted
postponed-proof warning (none was printed). The required delivery dry run passed; only the independent second reading remains for the
second reader. Nothing was pushed.
There are no STATEMENT-DISPUTED flags, new nodes, or dependency modules.

## Second reading by Q01

I independently read the base and sandbox node, the entire Lean module, its four
statement-dependency records and their actual declarations, the geometric-fibre record,
and the Nagata and invertible-exponent source interfaces. The blueprint source was read
at `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-dg-compact-support-amplitude.md`:
its assertion agrees verbatim with the DAG statement and its two proof paragraphs impose
no constructibility or finite-stalk restriction. This is a blueprint-source node, not a
Stacks-source node. I also opened the local Stacks TeX at Tags 0A21 (irreducible locally
algebraic schemes and nonempty opens), 04CA (closed-immersion essential image and inverse
image left inverse), and 0A5D (the finite-pushforward cohomology equality in its proof).
These explain the cited proof route; they do not introduce extra statement hypotheses.

Objects, hypotheses, and conclusions, matched independently in source order:

1. A field and finite-type schemes over it: `k : Type u`, `[Field k]`,
   `X Y : Scheme.{u}`, and the two `Over (Spec (.of k))` instances. Each structure
   morphism has `LocallyOfFiniteType` and `QuasiCompact`. Verdict: exact. The
   scheme-conventions dependency explicitly defines finite type by this conjunction;
   no separatedness of either structure morphism is required.
2. A morphism of those schemes, separated and finite type: `f : X ⟶ Y`,
   `[f.IsOver (Spec (.of k))]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and
   `[QuasiCompact f]`. Verdict: exact; the over-compatibility is precisely being a
   morphism of the given field schemes. No properness hypothesis is added.
3. A bound d on the geometric fibres: `d : ℕ` and `hd : ∀ y : Y, ... ≤
   (d : WithBot ℕ∞)`. The object inside `topologicalKrullDim` is the underlying
   space of `pullback f` along `Spec.map` of the residue-field inclusion into
   `AlgebraicClosure (Y.residueField y)`, followed by `Y.fromSpecResidueField y`.
   Verdict: exact, including nonclosed points. This is verbatim the geometric-fibre
   dependency's recorded encoding. It bounds X's fibres, not the ambient compactification.
   `topologicalKrullDim` was opened in Mathlib: it is `krullDim (IrreducibleCloseds T)`.
4. A finite coefficient ring: `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`.
   Verdict: exact in this node's context. Both the ordinary-derived-category and
   compact-support dependency statements explicitly introduce a commutative coefficient
   ring. Thus `CommRing` is inherited from the definitions being used, not an added
   field/domain hypothesis. No `Nontrivial` or finite-module hypothesis is present.
5. Additive exponent invertible on Y: `[HasInvertibleExponent Λ Y]`. Verdict: exact.
   I opened the class: it requires a positive natural n with `(n : Λ) = 0` and
   `IsUnit (n : Γ(Y, ⊤))`. For a finite ring the additive exponent is the additive
   order of 1, since an integer annihilates the ring iff it annihilates 1. It divides
   every positive such n. A factor of a unit is a unit in a commutative ring, so this
   existential condition is equivalent to invertibility of the exponent itself.
   The condition is on Y, preserving also the empty-base case.
6. Every etale module sheaf F: `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
   Verdict: exact, with the dependency's fixed constant-ring module-sheaf encoding.
   There is no constructible, locally constant, finite-stalk, or finite-module binder.
7. All q above twice d: `q : ℤ` and `hq : 2 * (d : ℤ) < q`.
   Verdict: exact for ordinary cohomological grading. The strict inequality, not a
   weak inequality, is used; every integer satisfying it is positive.
8. Vanishing `R^q f_! F = 0`: `IsZero` of degree-q `DerivedCategory.homologyFunctor`
   applied to `rightDerivedLowerShriekOfCompactification ...` on
   `(DerivedCategory.singleFunctor ... 0).obj F`. Verdict: exact categorical
   vanishing of the output module sheaf. The compact-support dependency's actual
   source defines this functor as exact derived open extension followed by total
   derived proper direct image on the unbounded categories. The chosen compactification
   is the existing Nagata construction, specialized by the helper. The comparison
   dependency, opened in `EtaleCompactSupportComparisons.lean`, supplies the specified
   normalized refinement comparisons; on this bounded-below input they identify the
   chosen candidate with the notation Rf_!. No new arbitrary functor is substituted.
9. Ordinary derived categories: both `singleFunctor` and `homologyFunctor` act on
   `_root_.DerivedCategory` of etale module sheaves. Verdict: exact. There is no
   completed, pro-etale, or adic category or bound imposed on the ambient category.

Helper and dependency review (H4/H5/H12/H13):
`compactSupportAmplitudeCompactification` calls the existing `NagataCompactification f`.
Its body supplies `IsLocallyNoetherian Y` by finite type over the field, and `CompactSpace Y`
by quasi-compactness over its compact spectrum. Local Noetherianity supplies the needed
quasi-separatedness. These are consequences, not theorem assumptions. It has real data,
no `sorry`, no `Nonempty` choice, and no new compactification notion. The actual Nagata
signature requires precisely separated, locally finite type, quasi-compact f over a
quasi-compact quasi-separated base. All four statement dependencies are usable as recorded;
no new nodes or dependency modules are needed. All recorded proof-dependency modules are
imported directly. There is exactly one postponed theorem and no proved theorem in this
module. Its docstring covers each of the node's nine proof steps and cites the corresponding
nodes, and both declarations have source and blueprint docstrings.

Edge cases: X, Y, and any geometric fibre may be empty; there is no nonemptiness binder
and empty-space dimension is bottom. If Y is empty the fibre hypothesis is vacuous but
vanishing is in the sheaf category on that empty scheme. For d = 0 the assertion is exactly
q > 0, and the boundary q = 2d is excluded. The zero sheaf and zero coefficient ring are
allowed (for the latter n = 1 works); no characteristic is excluded beyond the stated unit
condition on Y. The arbitrary universe u is the recorded small-etale convention, with
coefficients and modules in u+1. The algebraic closure is in the residue field's universe,
so no smaller independently quantified field universe can make the hypothesis vacuous.
There is no index family whose empty case is discarded.

Independent searches (different wording from the worker):

- `msearch.py ... leanfinder`: "Higher etale direct image with proper supports of arbitrary
  torsion module sheaves is zero in degrees exceeding twice the fibre dimension". Eight
  hits, including `DerivedCategory.isZero_of_isLE` and etale-locus algebra, no exact match.
- `msearch.py ... loogle`: `"compactlySupportedCohomology"`. Zero hits.
- `msearch.py ... leansearch`: "Vanishing of higher compactly supported etale direct image
  above two times geometric fibre dimension". Unavailable (Internal Server Error);
  no mathematical verdict is drawn from this unavailable service.
- Direct `rg` in Mathlib, all upstream `WeilConjectures`, and project `lean/Sheaf` for
  fibre/dimension, vanishing, lower shriek, and amplitude. I opened the strongest upstream
  candidates in `Derived/Finiteness/DirectImage.lean`: both
  `isZero_homology_rightDerivedLowerShriek_singleFunctor` and
  `isZero_homology_rightDerivedLowerShriek` impose constructibility, and the former also
  assumes the exponent invertible on the field. They do not state this node's arbitrary
  sheaf result. `Derived/Stability/DirectImage.lean` concerns ordinary direct image and
  a source-dimension bound. No exact existing theorem was found. The new helper and
  theorem names have no collision in upstream or the project.

Mismatch/change verdict: no mathematical or interface mismatch found. I preserved the
Lean module and node record, and added this independent reading and new searches only.
There is no `statement_change` and consequently no correction/citer audit is required.
By direct extraction, `lean.statement` equals the full theorem signature verbatim.
No line exceeds 100 characters; universe u and every variable are explicitly bound.

Validation reproduced independently: `scompile.py Q01 lem-dg-compact-support-amplitude
lean/Sheaf/AlgebraicGeometry/EtaleCompactSupportAmplitude.lean` compiled the sandbox spelling
and library spelling cleanly (7.1 s and 8.2 s), with no errors or warnings.
