## Worker report

The module `Sheaf.RingTheory.SemilocalRestrictionLength` states the Stacks Tag 02M0
restriction-of-scalars length formula.  It introduces the canonical residue-field map
`semilocalResidueFieldMap`, the residue degree `semilocalResidueDegree`, its finiteness
predicate `semilocalResidueFinite`, and the local length `semilocalLocalLength`; these are
real constructions from the maximal-ideal and localization APIs.  The main theorem
`semilocal_restriction_length` has a `sorry` proof as required at stage 2.

The Lean rendering of the hypotheses is:

* `A` and `B` are explicit commutative rings with `[CommRing A] [CommRing B]`, and
  `[IsLocalRing A] [Algebra A B]` gives the unital map `A → B`.
* `X : Finset (MaximalSpectrum B)` and `hX : ∀ q, q ∈ X` encode the finite set of all
  maximal ideals of `B`.
* `hcon` says every maximal ideal in `B` contracts to
  `IsLocalRing.maximalIdeal A`.
* `hdeg` says the residue-field module used by `semilocalResidueDegree` is finite for
  every member of `X`; the degree is the canonical induced residue-field dimension.
* `M : Type v`, `[AddCommGroup M] [Module B M]`, and `hM : IsFiniteLength B M` encode a
  finite-length `B`-module.

The conclusion's first conjunct is
`@IsFiniteLength A _ M _ (@Module.compHom B A M _ _ (inferInstance : Module B M) _
(algebraMap A B))`, which is finite length after restriction of scalars.  Its second
conjunct is the equality of that restricted length with
`∑ q ∈ X, semilocalResidueDegree A B q (hcon q) * semilocalLocalLength B M q`.
`semilocalResidueDegree` uses the canonical map
`Ideal.ResidueField.map`; `semilocalLocalLength` uses
`LocalizedModule q.asIdeal.primeCompl M` over `Localization.AtPrime q.asIdeal`.
Using `MaximalSpectrum` supplies the maximality and prime instances for every summand,
while the residue fields are canonically equivalent to the quotient fields `B/q` and
`A/𝔪` in the source statement.

Dependency declarations used are Mathlib declarations recorded by the dependency nodes:
`Module.finrank` (node `def-weil-vector-space-dimension`), `Module.length` (node
`def-weil-pbc-module-length`), `Localization.AtPrime` (node
`def-weil-pbc-localization-at-prime`), and `LocalizedModule` (node
`def-weil-pbc-module-localization`).  The module imports the Mathlib modules supplying
these declarations.  No dependency module or new DAG node was needed.

Edge cases checked before writing: `X` may be empty (the finset sum is zero), `M` may be
zero (both lengths are zero), and the localization terms are well-typed for every
maximal ideal because `MaximalSpectrum` carries `IsMaximal`, hence `IsPrime`.  The
restriction-of-scalars module is explicit, so no accidental independent module action
is introduced.  The `hdeg` premise excludes infinite residue degrees as required by the
finite-dimensional hypothesis.

Searches for an existing declaration found no exact match.  `msearch.py leanfinder` was
run for “length of a finite module over a one dimensional local ring equals the sum of
local lengths weighted by residue field degrees” and for the semilocal restriction
formula; the returned `IsLocalRing.length_restrictScalars` requires both rings to be
local and has no localization sum.  `msearch.py leansearch` was run for “Module length
over a local ring equals sum of localized lengths weighted by residue extension degrees
in a semilocal algebra”; it returned only local-ring, product, and ramification
ingredients.  `msearch.py loogle` was run for `IsLocalRing.length_restrictScalars` and
`"length", "restrictScalars"`; neither matches the semilocal statement.  Grep searches
for `semilocal`, `length_restrictScalars`, and localization-length patterns in Mathlib,
the source `WeilConjectures`, and `lean/Sheaf` found no exact declaration.  The source
statement is Stacks Project Algebra, Tag 02M0 (`lemma-pushdown-module`).

## Earlier second reading (a previous round; superseded)

I independently reread the node, source place, and module.  The finite maximal-ideal
set is represented by `Finset (MaximalSpectrum B)` with membership hypothesis `hX`; the
contraction and finite residue-degree hypotheses are explicit.  The conclusion has both
finite restricted length and the weighted sum.  The only representation change from the
prose is the canonical residue-field form (`Ideal.ResidueField`) of `B/q` and `A/𝔪`,
with `Ideal.ResidueField.map` supplying the induced field action; this is definitionally
and canonically the source field extension.  No hypothesis or conclusion clause is
missing, and the zero-module and empty-set cases remain included.


## Second reading by Q128

I read the node's complete statement and seven proof steps, Stacks Algebra
`lemma-pushdown-module` (Tag 02M0, algebra.tex lines 12603–12642), the four
statement-dependency records and their Mathlib declarations, and the delivered module.
The source has no ambient Noetherian, integral, finite-algebra, or characteristic
hypothesis. Its rings are commutative. This section describes the final delivery and
supersedes descriptions of the removed helpers in the Worker report, which is retained.
No repair note exists for this item. There is no `statement_change` and the prose node
statement remains unchanged.

The object/hypothesis/conclusion list, matched individually:

1. A commutative local ring A with its unique maximal ideal m:
   `(A : Type u) [CommRing A] [IsLocalRing A]`, with
   `IsLocalRing.maximalIdeal A`. Correct. Mathlib's `IsLocalRing` extends
   `Nontrivial`; this matches the node's exactly-one-maximal-ideal convention.
2. The residue field k = A/m: `(IsLocalRing.maximalIdeal A).ResidueField`.
   Correct. I read `Ideal.ResidueField` and
   `Ideal.bijective_algebraMap_quotient_residueField` in
   Mathlib/RingTheory/LocalRing/ResidueField/Ideal.lean (definition at line 33,
   maximal-ideal comparison at lines 141–148). The canonical quotient-to-residue-field
   map is bijective at a maximal ideal; thus this is exactly the source's k.
3. A unital map from A to a commutative ring B:
   `(B : Type v) [CommRing B] [Algebra A B]` and `algebraMap A B`.
   Correct; for commutative rings an algebra structure is the specified unital map,
   with its forced scalar action. No finiteness or nontriviality is assumed for B.
4. A finite set X containing exactly all maximal ideals of B:
   `(X : Finset (MaximalSpectrum B))` and
   `hX : ∀ q : MaximalSpectrum B, q ∈ X`. Correct: membership types make all
   elements maximal; `hX` excludes omission of any maximal ideal; a Finset has no
   repeated elements. There is no additional `Fintype`, nonempty, or order assumption.
5. Each q contracts to m:
   `hcon : ∀ q : MaximalSpectrum B,
     q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A`.
   Correct. Quantifying over all maximal ideals agrees with quantifying over X by hX.
6. Each induced field extension k → B/q has finite dimension f_q:
   `hdeg` states `Module.Finite` for the residue fields with the explicit module
   `Module.compHom q.asIdeal.ResidueField
     (Ideal.ResidueField.map ... (algebraMap A B) (hcon q).symm)`.
   The same module argument is supplied to `Module.finrank` in the sum. Correct.
   I read `Ideal.ResidueField.map` (Ideal.lean lines 36–48): it is induced by
   the given ring map, and commutes with the maps from A and B. Together with the
   bijective maximal quotient maps above, this is the node's field extension.
   Over a field `Module.Finite` is finite dimensionality; the finrank dependency
   is used directly. There is no arbitrary coefficient action or hidden tower.
7. An arbitrary finite-length B-module M:
   `(M : Type w) [AddCommGroup M] [Module B M] (hM : IsFiniteLength B M)`.
   Correct after repair: the worker used `Type v`, unnecessarily tying M's universe
   to B's. I generalized it to an independent w. I read `Module.length_ne_top_iff`
   (Mathlib/RingTheory/Length.lean line 94), which identifies the finite-length
   predicate with finiteness of the recorded `Module.length` definition.
8. B_q and M_q are the specified localizations:
   `Localization.AtPrime q.asIdeal` and `LocalizedModule q.asIdeal.primeCompl M`.
   Correct, using exactly the recorded dependency declarations. I read the ring
   localization abbreviation and the module fraction construction, including its
   equality criterion (`LocalizedModule.mk_eq`). Maximality supplies primality.
9. First conclusion: M has finite A-length by restriction of scalars:
   the first conjunct is `@IsFiniteLength A ...` with
   `Module.compHom ... (algebraMap A B)`. Correct: the A-action is forced by
   the given B-action, with no independent A-module instance.
10. Second conclusion: length_A(M) = sum over X of f_q times length_B_q(M_q):
    the second conjunct is `@Module.length A ... = ∑ q ∈ X, ...`, using the
    identical restricted action from item 9, the finrank from item 6, and the
    localizations from item 8. Correct. The natural-number degree is coerced into
    `ℕ∞`, the recorded length codomain. Both finiteness and equality are present;
    no extra conclusion was added. Quantifier dependencies match the node.

Edge cases: M may be zero. B may be the zero ring; then its maximal spectrum and
X are empty, its unital modules are zero, and the sum is zero. Conversely, hX with
X empty forces no maximal ideals, hence B is zero. No artificial Nontrivial B or
Nonempty X has been introduced. The base A is nonzero by the explicit local-ring
convention. For B = k × k over A = k and M = k × k, the formula is 2 = 1 + 1;
for B = L a finite field extension of k and M = L it is [L:k] = [L:k] · 1.
There is no characteristic restriction, scheme, degree n, or hidden positive-index
hypothesis. A, B, M now have independent u, v, w; module localization lives in
`Type (max v w)`, as Mathlib requires, so larger and smaller module universes work.

Independent searches: I ran msearch LeanFinder for “Length after restriction to a
local base equals the residue-degree weighted sum of lengths localized at maximal
ideals of a semilocal algebra”, Loogle for `"length", "localization"`, and
LeanSearch for “A finite length module over a semilocal algebra over a local ring
has restricted length equal to the sum of residue field dimensions times localized
lengths”. Loogle found no hit. LeanSearch returned finite-generation-localization
results and length additivity; LeanFinder returned inertia degree and ramification
results. I independently searched Mathlib/RingTheory and Algebra/Module for
`semi.local`, `length.*localiz`, `localiz.*length`, and `length_restrictScalars`,
and the upstream WeilConjectures and this project's lean/Sheaf for the same concepts
and restriction/length variants. I read IsLocalRing.length_restrictScalars
(LocalRing/Length.lean lines 25–73): it assumes B local and has no semilocal sum.
I read the current `Ideal.inertiaDeg` and its maximal-quotient identification
(RingTheory/RamificationInertia/Inertia.lean), and the quotient variant in
NumberTheory/RamificationInertia/Inertia.lean. These define the weight, not this
module-length formula. The final statement uses the already recorded
`Module.finrank` directly instead of introducing another degree definition.
There is no exact existing theorem to bind as `existing: true`.

Repairs and remaining checks:

- Removed all four helper wrappers (`semilocalResidueFieldMap`,
  `semilocalResidueDegree`, `semilocalResidueFinite`, `semilocalLocalLength`) and
  used the existing Mathlib map, finite-module predicate, dimension, and lengths
  directly. They had no data holes, but needlessly renamed existing constructions.
  This also removes their incomplete source-place docstrings. Updated
  `lean.declarations` to contain only the theorem.
- Generalized M from `Type v` to `Type w`, as item 7 explains.
- Replaced the theorem's statement-only docstring with its source place and all
  seven proof steps, including the simple factors, basis flag, restricted exact
  sequences, localized simple-factor computation, localized exactness, regrouping,
  and zero cases, citing the node's non-elementary dependencies.
- Added the project's standard copyright header and the missing proof imports for
  localization exactness, simple modules, and simple filtration. The additivity
  dependency is already the public Mathlib.RingTheory.Length import. I read the
  current `WeilConjectures.RingTheory.SimpleFiltration` source using
  `scompile.py --source`; its theorem has the required finite strict filtration,
  and its import compiles in the private overlay.
- No definitions, new nodes, or dependency repairs remain in the delivery. The sole
  postponed theorem is `semilocal_restriction_length`, with precisely one `sorry`.
  No proof was supplied at this stage. No variable/universe is unbound, no local
  notation or instance is exported implicitly, and every Lean line has at most
  100 characters. `lean.statement` is extracted verbatim from the final signature.
- Compilation through the authorized scompile.py wrapper passed with no errors or
  warnings. The dry-run and final delivery are performed after this reading.
