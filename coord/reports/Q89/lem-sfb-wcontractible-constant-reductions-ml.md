## Worker report

The module `Sheaf.Paper.WContractibleConstantReductionsML` states
`AlgebraicGeometry.Scheme.wcontractible_constant_reductions_mittagLeffler`, with
`sorry` as its only postponed proof. It implements the all-degree Stacks 09C5
statement of the node, without changing its mathematical statement. I read
`literature/stacks-project/proetale.tex`, lemma
`lemma-weakly-contractible-locally-constant-ML` (09C5), including the finite-triple
comparison and Artin–Rees conclusion. The declaration docstring gives all seven
steps of the node's proof. No theorem of the project is proved in this delivery;
the two zero-morphism instances are structural functor-law data for applying the
existing termwise-complex construction.

The previous retry's claim that the item was already completed was misleading:
Q13's report and merged node are a stage-1 split, not a Lean statement. This worker
started with only the dispatcher marker files. The first deliver2 attempt failed
because the sandbox held no node. The node, module and this report now supply the
actual stage-2 work.

### Clause-by-clause correspondence

* The affine scheme is `(W : Scheme.{u}) [IsAffine W]`, using Mathlib's scheme and
  affine predicate. There is no Noetherian, connected or nonempty hypothesis on W.
* Weak contractibility is `_hW`: every epimorphism `f` of sheaves of sets on
  `ProEt.topology W` induces a surjection at `⊤_ W.ProEt`. This is precisely the
  definition in the node; no section or stronger splitting datum is assumed.
* The coefficients are `(A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]` and
  `(J : Ideal A)`. The module value universe contains the small site's objects;
  the original site still has object universe u+1 and morphism universe u. No
  equality of those two universes is imposed. This is the usual common-universe
  convention, with arbitrary coefficients after choosing a sufficiently large
  scheme universe; coefficients need not have finite underlying sets.
* `H : ConstantCompletion.D (ConstantCompletion.constant
  (proEtaleModelTopology W) A)` is the unbounded derived category of module sheaves
  over the constant commutative ring sheaf. The site is the existing
  `proEtaleSiteModel W = AsSmall.{u+1} W.ProEt`, with the topology induced by the
  existing equivalence `AsSmall.down`. This only enlarges morphism sizes; it does
  not replace the small site by the big site or restrict its objects or covers.
  Constants and final-object sections are transported along that same equivalence.
* `_hcomplete` is `ConstantCompletion.IsComplete` for the actual quotient
  `A → A/J^(0+1)`. Its body is the dependency's
  `IsLocallyDerivedRingedIdealComplete`, with standard localizations on all slices,
  applied to the kernel ideal and its inclusion. By exact constant sheafification
  this kernel is J times the constant ring. Thus it is the stated local internal
  Hom vanishing condition, not just a chosen limit isomorphism. It remains a
  hypothesis, although the node's proof can establish ML without using it.
* Positive exponents are indexed by `n : ℕ`, standing for n+1. The reduction in
  `_hconstant` is `ConstantCompletion.extend (ConstantCompletion.quotient … n)`
  applied to H. `extend` is the published universal derived extension pair, with
  its K-flat counit. It retains the quotient coefficient action, so the isomorphism
  is in D(A/J^(n+1)), not merely after forgetting that action.
* For every n, `_hconstant` gives `E : MLAlgebraDerived (A ⧸ J^(n+1))` and a
  `Nonempty` isomorphism to `mlConstantDerivedObject … E`. `MLAlgebraDerived` is a
  transparent abbreviation for the recorded algebraic derived category with its
  standard localization. `mlConstantDerivedObject` sheafifies a representative of
  E using the existing `constantModuleHomFunctor`; exactness makes the isomorphism
  class independent of that representative. The representative is supplied by the
  localization functor's actual `objPreimage`, whose image is isomorphic to E;
  no undetermined object is chosen from an unproved existence assertion.
* At n=0 the same existential requires `MLAlgebraPerfect E` via the implication
  `n = 0 → …`. This is exactly the node's E_1-perfect hypothesis. At positive n
  the implication has false premise and adds no perfectness hypothesis. The
  abbreviation unfolds to the recorded `DerivedCategory.IsPerfectRingComplex`,
  meaning a bounded finite-projective representative.
* There is no compatibility relation between these existential isomorphisms and
  no choice of algebraic transition maps in the hypotheses.
* `mlHypercohomologyTower` uses the already published
  `(ConstantCompletion.quotientPresentation … false).tower`. This is the universal
  derived strict quotient tower, whose ordinary transitions are uniquely fixed by
  the formula s tensor x ↦ quotient(s) tensor x. They are not arbitrary arrows and
  not selected from independent isomorphism existentials. Degree-q homology of this
  derived strict tower is a genuine inverse sequence of module sheaves. Evaluate
  it at `AsSmall.up.obj (⊤_ W.ProEt)` and forget the module action. Under `_hW`,
  final-object sections are exact (0946), so Γ commutes with cohomology and already
  computes RΓ, in all integer degrees. These are precisely the node's
  H^q(W,H_n) groups and their canonical maps. This use of exact evaluation avoids
  constructing a second right-derived-sections functor.
* The conclusion quantifies `∀ q : ℤ`, with no bound. Mathlib's
  `Functor.IsMittagLeffler` on the resulting functor to Type is exactly eventual
  stabilization of its images: at n it chooses m≥n whose range is contained in
  every range into n. For k≥m, functoriality gives the opposite inclusion and
  therefore equality; conversely stabilized ranges give that predicate. Forgetting
  a module does not alter its image as a subset or subgroup. Identity indices and
  arbitrary k≥m are included. There is no finite-cardinality shortcut.

### Dependency declarations and imports

I read the statement and Lean record of every original statement dependency and
opened their recorded source declarations and docstrings:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, using the same small pro-etale
  site, intrinsic constant-ring module category, and ordinary derived localization.
  The present equivalent small-model presentation permits the existing local
  completeness predicate to apply; it is not a copied definition of that category.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  exactly `SheafOfModules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`, `objPreimage` and
  `DerivedCategory.homologyFunctor`.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, the universal
  derived scalar extension computed on K-flat models.
* `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`:
  `CategoryTheory.IsLocallyDerivedRingedIdealComplete`, reused through
  `ConstantCompletion.IsComplete` with the actual quotient kernel.
* `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`.
* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` and its retained Mathlib site,
  sheaf and cohomology interfaces. Hypercohomology here is computed by exact
  evaluation as explained above, not by applying positive-degree sheaf cohomology
  to an arbitrary unbounded derived object.

The statement-dependency list gains three already landed nodes whose existing
canonical helpers are used: `lem-weil-pbc-constant-completion-equivalence`
(`Sheaf.Paper.ConstantCompletionEquivalence`, the `ConstantCompletion` API),
`lem-pur-site-constant-module-hom`
(`Sheaf.CategoryTheory.SiteConstantModuleHom`, `constantModuleHomFunctor` and
`constantModuleHomRingIso`), and `def-weil-proetale-inverse-image`
(the existing `proEtaleSiteModel` and `proEtaleModelTopology` from its
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` infrastructure). I read these actual
constructions, including the strict tower's universal property, tensor normalization,
constant-module sheafification and the AsSmall equivalence. The narrower
ProEtaleInverseImage module supplies those size-transport definitions directly;
there is no need to import the later finite-coefficient consumer module in that
node's expanded record.

Every already stated proof dependency's module is imported, without `public`
unless it is also a statement dependency. Mathlib leaves are imported from their
recorded files. The only proof dependency without a Lean record or Mathlib match
is `lem-sfb-perfect-constant-derived-map-local`; it is not needed to type this
statement and has no module to import. It remains explicitly identified as 09BE
in the proof plan. No dependency is waiting on this delivery, and no import cycle
was introduced. This delivery does not create or restate that proof-only theorem.

The helper abbreviations and definitions merely instantiate the existing notions
for this node. There are no new DAG nodes, dependency replacements, hollow data,
private definitions, local instances or local notation. Every variable and universe
is bound explicitly, with `set_option autoImplicit false` in the file.

### Edge cases

Checked empty W (zero module sections and trivial ML, without excluding the empty
cover), zero H, the zero coefficient ring, J=0 (constant reduction tower), J=A (zero
reductions), and nilpotent J (eventually fixed reductions). At n=0 the first residue
is A/J, and `MLAlgebraPerfect` imposes exactly its finite-projective-model condition.
Every q, including negative degrees and degrees outside any model's support, is
included. The same definitions handle m=n, k=m, and identity transitions. Infinite
Noetherian rings such as Q[[t]] and nonlocal rings are not excluded. No finite or
nontrivial instance, connectedness or faithful constant-realization assumption is
added to the theorem.

### Searches

All four required search modes were run with `msearch.py` for this group and item:

* LeanFinder: “Mittag Leffler hypercohomology of constant derived ideal power
  reductions on weakly contractible affine pro etale schemes”. Eight hits, including
  affine-limit section lemmas, `localCohomology` and formally-etale algebra; no match.
* Loogle: `"MittagLeffler", "Sheaf"`. Zero hits.
* Mathlib grep: `[Mm]ittag.*[Ss]heaf|[Ss]heaf.*[Mm]ittag|weaklyContractible.*[Cc]omplet`.
  Zero hits.
* LeanSearch: “Mittag Leffler hypercohomology of constant derived reductions over
  a Noetherian ring on weakly contractible affine schemes”. Eight hits, including
  `CategoryTheory.Sheaf.H`, condensed constants and module sheaf data; no match.

Direct rg searches in the upstream WeilConjectures tree and project lean/Sheaf
covered weak contractibility, constant reductions, Mittag–Leffler, derived constants,
ideal quotient towers, and each introduced declaration name. The upstream item-id
grep returned no match. The generic ML predicate exists in
`Mathlib.CategoryTheory.CofilteredSystem` and is reused; no existing theorem gives
this node's Noetherian derived-sheaf ML conclusion. The upstream-name index has no
collision with any delivered name. Existing constant, completeness, scalar-extension
and tower constructions were found and reused rather than redefined.

### Validation

`scompile.py Q89 lem-sfb-wcontractible-constant-reductions-ml
lean/Sheaf/Paper/WContractibleConstantReductionsML.lean` compiles the complete module
on the server, including its full proof-dependency import list, with no errors or
warnings. Only the principal theorem has `sorry`. All lines are at most 100 characters.
No statement dispute, source correction, or dependency-module repair is required.

## Second reading by Q89

I am the second reader and did not write the statement. I read the node's statement,
all seven proof steps, the worker report, the full delivered Lean module, the original
statement-dependency records, and the actual declarations used below. There is no
maintenance repair note for this item. I read Stacks `proetale.tex`,
`lemma-weakly-contractible-locally-constant-ML` (09C5, lines 5988–6071), including
its finite-triple comparison. The source assumes a weakly contractible affine,
a Noetherian coefficient ring, an ideal, and a constructible complete derived object
with individually constant reductions. Here complete H and perfect constant residue
supply that constructibility input, as the node explicitly explains. Shifting gives
all integer degrees. Neither source nor node assumes finite quotient sets or compatible
constant markings. No correction of the mathematical node statement is needed.

My object/hypothesis/conclusion inventory and H3 comparison is:

| Node clause | Lean rendering and verdict |
| --- | --- |
| Affine scheme W | `(W : Scheme.{u}) [IsAffine W]`. Mathlib's scheme and affineness; exact. |
| Weakly contractible small pro-etale site | `_hW` quantifies over every set-sheaf epimorphism on `ProEt.topology W` and requires its component at `op (⊤_ W.ProEt)` to be surjective. Exactly the node's definition, with no extra splitting or geometric assumption. |
| Commutative Noetherian ring A and ideal J | `(A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] (J : Ideal A)`. Exact; no field, characteristic, cardinal-finiteness, localness or nonzero hypothesis. |
| H in the unbounded derived category of constant-A module sheaves | `H : ConstantCompletion.D (ConstantCompletion.constant (proEtaleModelTopology W) A)`. `constant` is the recorded constant commutative-ring sheaf, `Mod` is the existing `ringedSiteModules`/`SheafOfModules`, and `D` uses `HasDerivedCategory.standard`. Exact up to the published equivalence of small sites. |
| Locally derived J-completeness | `_hcomplete : ConstantCompletion.IsComplete (ConstantCompletion.quotient ... A J 0) H`. Opening `IsComplete` gives `IsLocallyDerivedRingedIdealComplete` with standard derived restrictions on every slice and the actual kernel ideal of A → A/J. The kernel's section formula in `kernelIdeal_existsUnique`, or the `flat_and_quotients` formula for this quotient, identifies it with J times the constant ring sheaf. Thus this is local internal-Hom vanishing at all ideal sections, with no boundedness assumption; exact. |
| Reductions H_n for positive exponents | `ConstantCompletion.extend (ConstantCompletion.quotient ... A J n)` means derived tensor with A/J^(n+1). `DerivedExtension` retains its universal comparison and K-flat computation; no arbitrary functor is substituted. Exact after reindexing n ↦ n+1. |
| Algebraic derived constants at every level | `_hconstant : ∀ n : ℕ, ∃ E : MLAlgebraDerived (A ⧸ J ^ (n + 1)), ...`. `MLAlgebraDerived` is exactly `DerivedCategory (ModuleCat ...)` with standard localization. The `Nonempty` isomorphism is in the quotient-coefficient category, rather than only after forgetting scalars. Exact. |
| Perfect E_1 | `(n = 0 → MLAlgebraPerfect E)` is required inside the same existential as its marking. `MLAlgebraPerfect` unfolds to `DerivedCategory.IsPerfectRingComplex`: a bounded finite-projective model with a derived isomorphism. At n=0 it requires precisely the chosen E_1 to be perfect; at positive n it imposes nothing. Exact. |
| Constant realization of E | `mlConstantDerivedObject` applies the existing `constantModuleHomFunctor` termwise to the actual localization representative `DerivedCategory.Q.objPreimage E`, then localizes. `objObjPreimageIso` identifies that representative with E; exact constant realization makes the result independent up to isomorphism. This is a genuine construction, not data selected from an undetermined sorry existence. Exact. |
| Canonical quotient transitions | `mlHypercohomologyTower` takes `(ConstantCompletion.quotientPresentation ... A J false).tower`. Its `QuotientPresentationLaws` retain the universal derived comparison to the ordinary `reductionTower`; `reductionStep_existsUnique` fixes its maps on sheafified tensors by s ⊗ x ↦ quotient(s) ⊗ x. Exact. |
| Hypercohomology groups and their maps | The tower's degree-q `DerivedCategory.homologyFunctor` is followed by `SheafOfModules.evaluation` at `AsSmall.up.obj (⊤_ W.ProEt)` and `forget`. Under `_hW`, the recorded weakly contractible evaluation theorem makes sections exact. Thus Γ of cohomology equals the cohomology of RΓ, naturally in every transition, including for unbounded H. Exact; not ordinary sheaf H^q applied to a derived object. |
| Every integer q | The conclusion is `∀ q : ℤ`. No bounded or nonnegative range is imposed; exact. |
| Eventual equality of images at each n | `(mlHypercohomologyTower ... q).IsMittagLeffler`. I opened Mathlib's definition in `CofilteredSystem.lean`: it chooses an arrow m → n whose range is contained in every range into n. In ℕᵒᵖ this gives m≥n; for k≥m, functoriality gives the reverse containment, hence equality. Conversely stabilized ranges imply the definition by comparing at max(k,m). Forgetting module structure retains exactly these images. Exact, neither stronger nor weaker. |
| No compatibility of markings | Each n has an independent existential E and isomorphism. No algebraic transition maps or coherence of these markings are hypotheses; exact. |
| No finite quotient sets | No `Finite`, `Fintype` or finite-cardinality hypothesis occurs. No finite-range shortcut is used; exact. |

I opened the dependency interfaces, rather than relying on their names:
`proEtaleDerivedCategory`, `ringedSiteModules`, `IsLocallyDerivedRingedIdealComplete`,
`DerivedCategory.IsPerfectRingComplex`,
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients`,
`constantModuleHomRingIso`/`constantModuleHomFunctor`, and the `ConstantCompletion`
constructions `constant`, `D`, `quotient`, `kernelIdeal`, `IsComplete`, `DerivedExtension`,
`extend`, `reductionStep`, `reductionTower`, `QuotientPresentationLaws`, and
`quotientPresentation`. I also checked the Mathlib scheme, Noetherian, constant-sheaf,
derived-localization and homology interfaces and the site/cohomology record.
The three added statement dependencies are already landed records and their actual
helpers are used; they are not new definitions or dependency replacements.

In particular `proEtaleSiteModel W = AsSmall.{u+1} W.ProEt` and
`proEtaleModelTopology` is the topology induced by `AsSmall.down`. I opened these
in `ProEtaleInverseImage.lean`, together with the sectionwise module transports.
Every object and covering of the original small site is retained. The original
object universe u+1 and morphism universe u are not identified; the model raises
only Hom size to u+1. Coefficients and module values live in the common ambient
universe u+1. This is the node's small-site/ambient-coefficient convention, not an
assumption that A is small in the scheme's universe. There is no independently
smaller universe for test objects that could make a hypothesis vacuous.
The current expanded inverse-image record primarily names later finite-coefficient
operations; its original arbitrary-ring `ProEtaleInverseImage` infrastructure remains
published and is the relevant imported module here. The finite-ring adjunction is
not used to type this statement.

Edge cases: empty W is allowed, and its empty covering forces terminal (zero)
module sections; zero H and the zero coefficient ring are allowed. J=0, J=A,
and nilpotent J all give their actual quotient towers, not an exceptional branch.
n=0 denotes exponent 1 and exactly the perfect residue. There is no exponent-zero
assumption to add. Every q, including negative degrees, is quantified. Repeated
indices m=n and k=m are identity transitions in ℕᵒᵖ. There is no arbitrary index
family in this theorem, so an empty index set is inapplicable; empty coverings are
retained. No characteristic or connectedness is excluded. No implicit universe or
term variable remains unbound (`autoImplicit false`, sole declared universe u).

Independent H4 searches, using different wording from the worker's report:

* `msearch.py ... leanfinder "Cohomology of individually constant adic derived
  reductions has eventually stable images on a projective sheaf topos object"`
  returned eight hits, including `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`,
  `localCohomology.diagram`, and affine-limit section lemmas. None states this node.
* `msearch.py ... loogle '"IsMittagLeffler"'` returned the generic Mathlib predicate
  and its range/surjectivity lemmas. I read the predicate; it is reused here.
* `msearch.py ... grep` with
  `([Mm]ittag|[Ee]ventual[Rr]ange).*(adic|constant|sheaf)|(adic|constant|sheaf).*([Mm]ittag|[Ee]ventual[Rr]ange)`
  found no match.
* Direct `rg` in the upstream `WeilConjectures`, project `lean/Sheaf`, Mathlib,
  and `dag/lean_names_upstream.json` checked Mittag/eventual ranges, adic constant
  reductions, the item id, and every delivered declaration name. Generic ML limit
  lemmas and completed-constant realization helpers concern different statements;
  none duplicates this Noetherian hypercohomology assertion or a delivered full name.

H5/H6/H8/H9: the helper definitions use actual termwise sheafification, localization
representatives and the published canonical quotient tower. There are no hollow data,
private notions, local instances or local notation. The only postponed proof is the
principal theorem. The two zero-morphism instances supply computational structural
laws for the existing functor; they prove no additional mathematical statement.
All declarations have source/blueprint docstrings. All seven proof steps match the
node, including Artin–Rees and the single-largest-index comparison. The only defect
I found was documentation: the proof plan used source tags but omitted the DAG ids
of its inputs, and the multi-declaration module lacked its main-declaration list.
I added those cross-references and the list. I changed no Lean signature, helper data,
hypothesis, conclusion, mathematical node field or dependency interface.
There are no new definition nodes or dependency modules to review under H12/H13,
and no `statement_change` requiring a citer audit.

Validation: the entire delivered file compiled via
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q89
lem-sfb-wcontractible-constant-reductions-ml
lean/Sheaf/Paper/WContractibleConstantReductionsML.lean` with no errors or warnings
(the library file took 3 seconds). The same wrapper passed again after the documentation changes,
with no errors or warnings (2.4 seconds for the library file). A direct comparison confirms that
`lean.statement` is verbatim the file's theorem signature; only `lean` and the
three landed additions to `stmt_deps` differ from the base node. All Lean lines
are at most 100 characters and there is exactly one `sorry` term.

## Maintainer review correction (stage-2 reviewer, 2026-10-17)

The delivered statement fixed the coefficient ring in `Type (u + 1)` on
`proEtaleModelTopology W` (= `AsSmall.{u+1} W.ProEt`), i.e. it forced the coefficient
universe to equal the site's object universe. The only citer,
`lem-sfb-adic-residue-lisse-perfect-lift` (landed before this delivery), works with
`A : Type (max v (u + 1))` on `coefficientProEtaleModelTopology.{u, v}` and applies this
lemma to the restriction of its complex with the same `A`, so the delivered form could not
be applied when `v > u + 1`. The reviewer generalized the module to the existing
coefficient-sized model `coefficientProEtaleModelTopology.{u, v} W`
(`Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`, def-weil-proetale-inverse-image),
with `A : Type (max v (u + 1))`. At `v = 0` this is literally the delivered statement.
To avoid Lean's unsolvable `?w + 1 =?= max (u + 1) v` constraints, the two zero-morphism
instances, `MLAlgebraDerived`/`MLAlgebraPerfect` and the new abbreviation
`mlTowerCohomology` (standard-localization cohomology of strict towers) are stated over an
arbitrary small site/ring universe `w`. No hypothesis, conclusion, quantifier or
dependency changed; weak contractibility remains on `ProEt.topology W` with `Type (u + 1)`
set sheaves, exactly as in the recorded weakly-contractible evaluation lemma.
The file compiles cleanly through tools/nt_compile.py (no errors or warnings).

