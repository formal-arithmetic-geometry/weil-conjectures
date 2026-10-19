## Worker report

Final delivery status from the second reader: the original five-module draft
below was superseded by concurrent Q08 landings. The final packet contains only
AmplificationConsequences.lean and the item's node. Its theorem uses the landed
AMP, FIN and finite-coefficient operations; all four draft dependency modules
and their node copies were removed. The final second-reading section below
records the current signature and validation. The worker's original account is
retained here as requested.

The module `Sheaf.AlgebraicGeometry.AmplificationConsequences` states
`AlgebraicGeometry.ProEtale.finiteLevelAmplification_consequences`, with `sorry`
as its entire proof. It states the four containments of proposition 1351 and
uses the existing continuous-function coefficient sheaf and its recorded
bounded constructible essential-image predicate. All definitions have actual
data. No proof is supplied for the proposition or the postponed prerequisite
lemmas.

Hypotheses and clauses, matched individually:

- The schemes and four arrows are `X' X Y' Y`, `g'`, `f'`, `f`, `g`.
  `square : ChosenCartesianSquare g' f' f g` includes the chosen fibre-product
  identification and both projection equations.
- The coefficient datum is `A`, `[CommRing A]`, `[IsNoetherianRing A]`, and
  `d : AdicCoefficientDatum A`. Its fields are the ideal, finite generation,
  additive torsion modulo the ideal, finite positive quotients, and perfectness
  of each quotient as an A-module in degree zero. No completeness or flatness
  assumption on A or the quotients has been added.
- FIN's scheme conventions are `[IsNoetherian Y]`, `[IsNoetherian Y']`,
  `hDimY`, `hDimY'`, `hInvertY`, `hInvertY'`. The latter quantify over every
  element of every positive quotient and every stalk of the two targets.
  These are precisely the conventions already required in AMP's definition.
- The common nonnegative bound is `c : ℕ`; the amplification assumption is
  `hAmp : HasFiniteLevelAmplification ... c`, with the same bound at every level
  and on both direct images.
- `n : ℕ+` includes every integer n ≥ 1, with the actual exponent used in
  `d.quotient n = A ⧸ d.ideal ^ (n : ℕ)`; there is no n+1 reindexing.
- `a b : ℤ` and `hab : a ≤ b` render exactly the ordered cohomological interval.
- The first conjunct quantifies over all
  `K : FiniteCoefficientDerivedCategory X (d.quotient n)` satisfying
  `isBoundedConstructibleFiniteCoefficient ... K` and
  `finiteCoefficientCohomologyIn ... a b K`. Its conclusion has both the same
  bounded constructible predicate on Y for `finiteCoefficientDerivedDirectImage`
  along f and cohomology in `[a,b+(c:ℤ)]`.
- The second conjunct is the identical assertion for f' from X' to Y'.
- The third conjunct quantifies over the bounded constructible objects on Y
  with cohomology in `[a,b]`; `finiteCoefficientDerivedPullback` along g lands
  in the bounded constructible predicate on Y' with the unchanged `[a,b]`.
- The fourth conjunct is the identical assertion for g' from X to X'.
  Each quantifier is over all ambient objects satisfying the predicates, so
  these are containments of the full classes, rather than chosen witnesses or
  only the images of a selected family of complexes.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including its docstring and fields.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientComparison`, `finiteCoefficientDerivedComparison`, and
  `isBoundedConstructibleFiniteCoefficient`. The last is the full essential
  image of the recorded bounded constructible etale criterion.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage` and its public
  closure `ProEtaleOperations`: the arbitrary identified-coefficient ordinary
  module operations and their K-injective/termwise derived constructions.
  The latter's signatures and docstrings were read before supplying the finite
  coefficient-presentation adapter described below.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`:
  the actual fixed-ring pro-etale `upperStar` and `lowerStar` functors.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, the bounded finite projective model
  definition with independent localization universe.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  the scalar-extension witness specifies both the objects and the maps as the
  concrete sheafified tensor construction. Thus it determines ordinary reduction;
  this is not a choice of unspecified data from bare existence.
- The delivered prerequisite modules give `AdicCoefficientDatum`,
  `adicCoefficientDirectImageFinite`, and `HasFiniteLevelAmplification`,
  as described individually below. Their public imports expose the same
  recorded dependency declarations to the main theorem.

The two proof-only statements `prop-weil-pbc-restriction-direct-image` and
`lem-weil-pbc-pullback-preserves-bounded-constructible` have no recorded Lean
module, so they cannot be imported. They are named in the complete natural-language
proof docstring. They are not new assumptions of the theorem.

Edge cases checked: n=1 is the quotient A/I; c=0 gives `[a,b]` for all four
functors; a=b includes complexes concentrated in a single degree. Negative a,b
are allowed. Empty schemes and zero objects are not excluded; neither are the
zero coefficient ring, I=top, nor an admissible nilpotent or zero ideal. No
Nontrivial hypothesis or positive lower bound on c is imposed. The full
subcategory's isomorphism closure comes from its essential-image definition.
The site remains of object universe u+1 and morphism universe u; coefficient
rings live in u+1, with the module/derived universes inherited from the recorded
module-sheaf construction. No equality of site object and morphism universes
is imposed. No file-local notation, private definitions, or local instances
are used in public statements.

Searches (all service queries executed through msearch.py):

- LeanFinder: “finite level amplification implies cohomological amplitude
  containments for derived direct image and pullback of bounded constructible
  pro etale complexes”. Eight hits, all generic derived-category t-structure
  and single-functor lemmas; no match for this four-functor proposition.
- Loogle: `CategoryTheory.DerivedCategory, ObjectProperty`. Zero hits, with
  unknown identifier `CategoryTheory.DerivedCategory`; no match.
- LeanSearch: “finite level amplification cohomological amplitude derived
  direct image constructible pro etale sheaves”. Service unavailable with
  Internal Server Error; recorded as unavailable rather than a negative result.
- Mathlib grep: `amplification|Amplification|FiniteLevelAmplification` in
  CategoryTheory. Zero hits. Direct rg in Mathlib and the upstream name index
  found no proposed declaration names.
- Direct rg in WeilConjectures and project Sheaf for `amplification`,
  `Amplification`, and the exact blueprint id found no matching theorem. Nearby
  hits concern matrix amplification of Brauer classes and are unrelated.
- Published server node records were checked for the missing amplification,
  adic coefficient, and FIN nodes: all had null Lean records. The guessed
  `Sheaf.AlgebraicGeometry.FiniteLevelAmplification` server module was unavailable.
  Delivery branches were searched for these nodes and the two proof-only
  restriction lemmas; none supplied them. The pilot blueprint source files
  of proposition 1351 and definition 1350 were opened on the server.

No STATEMENT-DISPUTED issue was found.

## Dependency modules

The human's 2026-10-16 instruction requires stating missing existing DAG
prerequisites in this delivery. A draft of the same prerequisite chain was
present in Q08's sandbox but had not landed or been delivered. I read and
adapted a copy in this sandbox; no other worker's files were changed. The
strict reduction tower's naturality was reversed, and its composition/extensionality
fields required explicit indices and function extensionality; these are repaired.
The FIN wrapper below ensures its main recorded interface is the precise adic
specialization. All records in this delivery are owned by Q24.

- `def-weil-pbc-adic-coefficient-datum`:
  `Sheaf.AlgebraicGeometry.AdicCoefficientDatum`, main declaration
  `AlgebraicGeometry.AdicCoefficientDatum`. No published declaration was
  recorded. Its coefficient structure has all hypotheses needed here. Quotient
  transitions are the actual Ideal.Quotient.factor maps; finite coefficient
  sheaves retain their existing RingCat sections with commutativity restored.
  Their limit is the actual limit sheaf, not an arbitrary completion object.
  The strict ordinary reduction tower has uniquely tensor-characterized maps.
  Its derived tower is the universal derived functor computed on K-flat
  resolutions. Every postponed property is a named theorem with its proof plan
  and the owning node's blueprint tag, and every helper appears in
  lean.declarations.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.FiniteCoefficientOperations`, main declaration
  `AlgebraicGeometry.ProEtale.finiteCoefficientDerivedDirectImage`. The recorded
  constant-coefficient functor could not be applied literally to the recorded
  continuous-function coefficient ring sheaf. The adapter reexports all its
  existing arbitrary identified-coefficient operations and uses the canonical
  `finiteCoefficientRealization` equivalence to transport the existing
  fixed-ring operations. Equivalence is a named postponed property of that
  concrete realization; its inverse is the inverse of this concrete functor,
  not an arbitrary equivalence. Pullback is its exact termwise derived functor;
  pushforward is the ordinary K-injective right derived functor in all modules.
- `def-weil-pbc-constructible-direct-image-finiteness`:
  `Sheaf.AlgebraicGeometry.FiniteCoefficientFiniteness`, main declaration
  `AlgebraicGeometry.ProEtale.adicCoefficientDirectImageFinite`. No published
  declaration was recorded. Constructibility is explicitly linear isomorphism
  with the comparison pullback of a constructible etale module sheaf. The
  general FIN helper has exactly the two clauses: constructible nonnegative
  higher images and vanishing for q>c. The recorded wrapper specializes to
  d.quotient n with the full datum and the exact target conventions; it adds
  neither a bound-existence assertion nor any uniformity beyond the fixed c.
- `def-weil-pbc-finite-level-amplification`:
  `Sheaf.AlgebraicGeometry.FiniteLevelAmplification`, main declaration
  `AlgebraicGeometry.ProEtale.HasFiniteLevelAmplification`. No published
  declaration was recorded. Its conjunction has two FIN clauses and two
  additive, triangulated, constructibility- and interval-preserving pullback
  clauses for every positive quotient. `finiteCoefficientCohomologyIn` spells
  out vanishing outside the closed interval, exactly as the node defines.

## Statement corrected

The old statement, verbatim:

```tex
Let $\square$ be a cartesian square [def-weil-pbc-cartesian-square] with
$\Lambda$-coefficient data as in the adic coefficient datum and suppose that
$\mathrm{AMP}(\square;c)$ of [def-weil-pbc-finite-level-amplification]
holds. Then for every $n\geq1$, with $P_n=A/I^n$, and all $a\leq b$,
$$
 \begin{aligned}
  Rf_*\bigl(D^b_c(X_{\Proet},P_n)^{[a,b]}\bigr)
  &\subset D^b_c(Y_{\Proet},P_n)^{[a,b+c]},\\
  Rf'_*\bigl(D^b_c(X'_{\Proet},P_n)^{[a,b]}\bigr)
  &\subset D^b_c(Y'_{\Proet},P_n)^{[a,b+c]},\\
  Lg_n^*\bigl(D^b_c(Y_{\Proet},P_n)^{[a,b]}\bigr)
  &\subset D^b_c(Y'_{\Proet},P_n)^{[a,b]},\\
  Lg_n'^*\bigl(D^b_c(X_{\Proet},P_n)^{[a,b]}\bigr)
  &\subset D^b_c(X'_{\Proet},P_n)^{[a,b]}.
 \end{aligned}
$$
```

Proposition 1351 originally left c untyped and the scheme/coefficient
conventions inherited by AMP implicit. Definition 1350 expressly requires
FIN's conventions wherever FIN occurs. The corrected text introduces the
four morphisms, the adic datum and nonnegative c and writes those existing
conventions explicitly: Noetherian finite-dimensional Y and Y', and invertible
additive orders at every quotient level on those two schemes. The four
containments themselves are unchanged. The FIN node is added to stmt_deps
because the corrected statement explicitly cites this convention. No proof or
proof-dependency list was changed, and no unit statement is changed.

Complete citer audit: the only node whose stmt_deps or proof_deps names this
item is `thm-weil-pbc-amplification-proper`. Its use still holds. All four
schemes there are Noetherian of finite dimension. Its invertible positive
annihilator N of A/I has N^n annihilating P_n; every finite additive order
divides N^n, hence is a unit. Its bound 2e is nonnegative. Its application of
the four containments is therefore unchanged. The citer was not edited.

## Verification

Single-file compilation is exclusively through scompile.py, at nice 19 with
two threads and the unchanged 60-second file limit. The initial five-module compile passed cleanly, including every delivered file.
The adic prerequisite is additionally extended to expose the quotient-valued
derived reductions, their comparison with tower evaluation, and canonical
normalizations and quotient associators fixed by the ordinary tensor formula
and counit equation on every K-flat representative. The quotient cocycle is
a named postponed theorem with the full tensor-computation proof plan. These
complete the definition node beyond the coefficient-data portion used directly
by this proposition. The expanded module and final delivery dry run are being
checked through the same prescribed wrappers.

The expanded adic module passed the required scompile.py check cleanly in
21.9 seconds. Explicit result types on quotient-change functors avoid repeated
elaboration of nested existence witnesses. An intervening server overlay
creation failed with ENOSPC (the server tmpfs was low on inodes); the prescribed
wrapper retry passed without changing the shared build or any tool. The initial
five-module dry run printed OK; the final expanded delivery is rechecked below.

Final verification: deliver2.py Q24 prop-weil-pbc-amplification-consequences
--no-push printed OK for dry-run commit b587ba25fa: all five expanded modules
compile and the maintainer preflight passes except for the independent second
reading, which the second reader supplies. Nothing was pushed.

## Second reading by Q24

Independent second reader, 2026-10-16. The final delivery has one module,
Sheaf.AlgebraicGeometry.AmplificationConsequences, and its own node only.
The first five-module packet passed compilation and preflight, but Q08 landed
usable overlapping dependencies while the delivery waited on the group lock.
I checked the current server records after the first push and corrected that
race: all four dependency modules and node copies have been removed. This
replacement delivery uses the published interfaces and replaces the earlier
branch commit 9ceb3703c9. No dependency declaration is re-recorded or overwritten.

I read the corrected proposition against source FIRST: blueprint proposition
1351 and definition 1350, then FIN definition 1301, the adic coefficient datum
and the derived operations paragraphs. Since the literature is absent in the
local mirror, I read those exact files in the read-only server checkout. I also
read Stacks TeX at 095U (etale-cohomology.tex,
lemma-cohomological-dimension-proper), 0GL0 (more-etale.tex,
theorem-constructible-shriek), 09AI/09AK/09AL (proetale.tex, constructible
section and comparison lemmas), 09C1/09C7 (definition-Dbc and
proposition-Noetherian-adic-constructible), 099L/099M (constant Noetherian
completion section and lemma), and 06YY (sites-cohomology.tex,
lemma-derived-base-change). None states the four-functor assembly. Properness
and finite presentation in the cited finiteness theorems are inputs for proving
AMP in applications, not additional assumptions of this consequence of AMP.

Objects, hypotheses and conclusion clauses, matched with the final Lean:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Four arbitrary schemes and arrows | `{X' X Y' Y : Scheme.{u}}`, `g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` | Pass |
| Chosen cartesian square | `square : ChosenCartesianSquare g' f' f g`; the recorded structure extends CommSq and includes the chosen pullback isomorphism and both projection equations | Pass |
| Commutative Noetherian A and finitely generated ideal I | `A : Type (u+1)`, `[CommRing A]`, `[IsNoetherianRing A]`, `I : Ideal A`, `hI : I.FG` | Pass; the arithmetic datum is explicit, as in published AMP |
| A/I additively torsion | `htorsion : IsAddTorsion (A ⧸ I)` | Pass; Mathlib's finite additive order means a positive integer kills each element |
| All positive quotients finite as sets | `[hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]` | Pass; the instance provides the same given hypothesis at every level |
| All positive quotients perfect over A in degree zero | `hperfect` uses the recorded `DerivedCategory.IsPerfectRingComplex` on the degree-zero ModuleCat quotient | Pass; exactly a bounded finite projective model, with the standard localization |
| Noetherian finite-dimensional FIN targets | `[IsNoetherian Y]`, `[IsNoetherian Y']`, `hDimY`, `hDimY'` | Pass; no such assumption added on X or X' |
| Additive orders invertible locally at all levels on both FIN targets | `hInvertY`, `hInvertY'`, quantified over positive n, quotient elements, and every point/stalk | Pass |
| One common nonnegative bound and AMP | `c : ℕ`, `hAmp : HasFiniteLevelAmplification ... A I hI htorsion hperfect ... c` | Pass; same c for both maps and all n |
| Every positive quotient exponent, with the discrete topology | `n : ℕ+`, `A ⧸ I ^ (n : ℕ)`, `[TopologicalSpace ...]`, `[DiscreteTopology ...]` | Pass; this exposes the source's prescribed discrete topology, which always exists, without fixing a second coefficient object |
| Every ordered integer interval | `a b : ℤ`, `hab : a ≤ b` | Pass |
| Rf_* containment | First conjunct: every bounded constructible K on X in `[a,b]` has bounded constructible image under `finiteCoefficientDerivedDirectImage f ...` on Y, in `[a,b+(c:ℤ)]` | Pass |
| Rf'_* containment | Second conjunct, with X', Y', f', and the same bound | Pass |
| Lg_n^* containment | Third conjunct: every bounded constructible K on Y in `[a,b]` has bounded constructible image on Y' under `finiteCoefficientDerivedPullback Y ... g`, still in `[a,b]` | Pass |
| Lg_n'^* containment | Fourth conjunct, with X, X', g', and unchanged interval | Pass |
| Containments of full classes | All four conjuncts quantify over every ambient object satisfying the essential-image and interval predicates | Pass; no selected-model or chosen-witness restriction |

Dependencies were checked from their declarations and definitions, not names.
I read ChosenCartesianSquare's fields; ProEtaleFiniteModules' actual
continuous-function presheaf, ring sheaf, module category, derived category,
realization, comparison and bounded constructible essential-image predicate;
IsConstructibleEtaleModuleSheaf; PerfectRingComplexGeneral; the arbitrary
identified-coefficient operations reexported by
ProEtaleConstantDerivedDirectImage; and
DerivedChangeOfRingsIndependentCoefficients. I read the exact side-framework
FiniteCoefficient/UpperLowerStar/Defs.lean and coord/pefw-upstream-framework.md.
Its fixed-ring upperStar is Kan extension followed by sheafification, and
lowerStar is precomposition with scheme base change, for arbitrary morphisms.
The derived comparison is the exact recorded comparison inverse image followed
by concrete coefficient realization. Constructibility uses linear isomorphisms
and finite locally constant module values, matching the node and finite-ring
bounded constructible criterion.

After detecting the concurrent landings I fetched the exact current sources
with scompile.py --source, opened them in full, and matched them again:

- Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage (Q07/Q08):
  `finiteCoefficientDerivedDirectImage f Λ` derives the actual sectionwise
  module pushforward, using the canonical coefficient map given by
  precomposition with the fibre-product projection and ring sheafification.
  Its resolutions are K-injective in all coefficient modules. Pullback is
  the existing fixed-ring inverse image transported through the concrete
  realization equivalence and then descended termwise. Pass; this is the
  published ordinary uncompleted interface, and no copy is delivered.
- Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness (Q07/Q08):
  `ConstructibleDirectImageFiniteness` writes the full arithmetic datum
  explicitly. It gives the selected quotient its discrete topology internally.
  Its two clauses assert constructibility for every constructible sheaf and
  integer q≥0, and vanishing for q>c with c fixed before the sheaf. Its higher
  image is cohomology of ordinary derived image of the sheaf in degree zero.
  Pass. The published node's fixed bound, rather than the older blueprint's
  ambiguous bound-existence wording, is preserved.
- Sheaf.AlgebraicGeometry.FiniteLevelAmplification (Q08): the explicit arithmetic
  arguments are exactly those now supplied in the proposition. The FIN clauses
  have the same c at every positive n; both pullbacks preserve constructibility
  and every interval. `finiteCoefficientCohomologyIn` means vanishing in every
  integer degree i<a or b<i. Its canonical ambient shift structure and
  triangulation descend to the full subcategories. Pass.

No completed coefficient sheaf, strict reduction tower or normalization map is
needed to state this finite-level consequence. Accordingly there is no missing
data object to construct here: its complete arithmetic coefficient datum is
already expressed by Mathlib's ring, ideal, quotient, torsion and perfectness
predicates, precisely as in the published AMP/FIN interfaces. The extra direct
statement dependency `def-pc-perfect-ring-complex` names the recorded predicate
used explicitly in hperfect. No new definition node or dependency module remains.

Correction audit: the source's use of AMP already requires a nonnegative c and
the FIN conventions. Writing the arrows and these conventions explicitly changes
none of the four containments and introduces no independent geometric condition.
I searched all DAG statement/proof dependencies and found exactly one citer,
`thm-weil-pbc-amplification-proper`; no second citer exists. I read its full
statement and every proof step. Its Noetherian finite-dimensional schemes supply
both target conventions. N in I implies N^n kills P_n, every additive order
divides that invertible N^n, and c=2e is nonnegative. Its use of all four bounds
in proof step (c) still holds, so the recorded `holds: true` is correct. No unit
statement changes. The Lean's explicit arithmetic presentation is the same adic
datum and requires no further TeX statement correction.

Edge cases: n=1 is included and n=0 is deliberately absent, exactly as in the
node; c=0, a=b and negative a,b are included. Zero objects, zero coefficient
quotients, I=top, zero or nilpotent ideals when the arithmetic hypotheses hold,
and empty schemes are not excluded. The order of zero is one. Empty strata and
empty trivializing families remain possible through the recorded constructible
predicates, with no new Nonempty condition. No arbitrary index type is introduced.
Site objects remain in u+1 and morphisms in u; coefficients and module values
use the recorded u+1 size convention and the standard localization. No equality
of site object and morphism universes, field assumption, characteristic bound,
flatness, completeness, properness or finite-type hypothesis is added. Every
variable and universe is explicitly bound. Discrete topologies are unique, so
the exposed topology binders neither exclude a quotient nor change its meaning.

Independent searches, with wording different from the worker's:

- LeanFinder through msearch.py: "cohomology of right derived pushforward
  constructible sheaves has amplitude in a bounded interval". Eight generic
  derived t-structure hits; no four-functor AMP consequence.
- LeanFinder: "equivalence sheaves of modules over constant ring sheaf and
  sheaves valued in modules". Eight generic module-sheaf/forgetful-functor
  hits; no replacement for the concrete coefficient realization interface.
- Loogle: `Functor.IsTriangulated`. Unknown identifier and no hits, so this
  was not treated as evidence of absence.
- LeanSearch: "adic ring finite perfect quotients inverse system derived
  reduction functor". Unavailable (Internal Server Error), recorded as such.
- Direct rg in Mathlib CategoryTheory/Algebra/Homology, upstream
  WeilConjectures, project Sheaf and the upstream name index for cohomological
  bounds/amplitudes, constructible direct images/pushforwards and the exact
  declaration names. I opened upstream Adic/LowerStar.FiniteFor,
  Etale/Derived/Finiteness/DirectImage's invertible-exponent theorem and
  DerivedCategory/PlusDevissage. They concern adic coefficients, finite-type
  schemes over a field, or natural-transformation comparison; none states
  this proposition. Current server record/source searches DID find the new
  Q07/Q08 dependency declarations, and the final delivery reuses them.

Mismatches and changes: the original mathematical containment statement was
correct. Concurrently published dependencies made the original dependency
packet duplicate existing notions and made its AMP argument/signatures stale.
I removed all four duplicate modules and dependency node records, exposed the
coefficient hypotheses exactly as in the published AMP signature, and updated
all direct-image applications to the published `finiteCoefficientDerivedDirectImage
f Λ` interface. The new topology binders render the prescribed discrete
quotients. The four object classes and bounds are unchanged. The item's
`lean.statement` is copied verbatim from the final signature. Its entire proof
is still `sorry`, and its source/blueprint docstring carries the same stepwise
FIN restriction and pullback argument. The earlier docstring-summary additions
were in removed draft modules and are not part of the final packet. The final
compile, preflight and replacement push are recorded below.

Replacement single-file compilation: scompile.py passed cleanly against the
current published FiniteLevelAmplification overlay and its dependencies. The
sandbox and library passes took 4.2 and 5.5 seconds, respectively; no error or
unexpected warning occurred. There is now exactly one delivered Lean file.

Final replacement dry run: deliver2.py Q24
prop-weil-pbc-amplification-consequences --no-push printed
"OK (dry run): commit 4618703c7f passes the preflight and compiles; nothing pushed".
Only the report, item's node and AmplificationConsequences.lean were staged.
An initial replacement attempt hit temporary server-overlay ENOSPC; the wrapper
retry passed without changing any shared file, compiler limit or tool.
