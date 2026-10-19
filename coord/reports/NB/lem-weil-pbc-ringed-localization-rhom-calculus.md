## Worker report

The delivery states `lem-weil-pbc-ringed-localization-rhom-calculus` in
`Sheaf.Paper.RingedLocalizationRHomCalculus`. No proof is supplied: the three named
theorems have `sorry` as their whole proofs. All helper definitions have concrete data.
The earlier unrecorded helper drafts were moved to scratchpad because the current
library already supplies their notions. There are no new nodes or dependency repairs.

Sources read: sites-cohomology.tex, `lemma-internal-hom` (08J9) and
`lemma-restriction-RHom-to-U` (08JB), including their proofs; algebraization.tex,
`lemma-map-twice-localize` (0996), especially (3) and its fraction calculation.
The imported general restriction statement was also read in full. It supplies the
exact functors and the relocalization isomorphism used in the comparison square.

Hypothesis and clause mapping:

* A small site is `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`;
  its commutative ring sheaf is `R : Sheaf J CommRingCat.{u}`. These are the same
  universes as the recorded general-site RHom. The module category is the transparent
  `localizationModules R = ringedSiteModules ...`; `localizationDerived`,
  `localizationQ` and `localizationRHom` specialize the existing declarations to
  `HasDerivedCategory.standard`, rather than constructing different categories.
* The sectionwise sheafification localization is exactly
  `ringedSectionLocalization`. Its argument is a compatible global section family,
  so no terminal object of C is assumed. On a slice, `localizationSliceCoefficient`
  uses the recorded `ringedSliceSection R U f`, with arbitrary `f : R(U)`.
* `IsBoundedLocalizationComplex R P` spells out BOTH bounds with integers a,b and
  `IsZero (P.X n)` outside them. In every degree it requires an isomorphism to the
  categorical direct sum of `Fin k` many recorded localization sheaves. No splitting
  condition on differentials is imposed. `k = 0` is permitted. The term R is included
  by the global section one. This predicate packages the hypothesis of this node,
  rather than introducing an independent mathematical notion.
* Exact termwise restriction is `localizationComplexRestriction`; derived restriction
  is the existing `overFunctor.mapDerivedCategory`. `localizationRestrictionCompIso`
  is explicitly the composition comparison followed by derived `overFunctorMap`.
  Its data are the sectionwise identity relocalization, not a chosen isomorphism.
* `localizationTensorComplex R S` is literally `(tensorLeft S).mapHomologicalComplex`.
  Therefore its degree n is S tensor P^n and its differential is 1 tensor d_P.
  `localizationSliceComplex R U f` is termwise restriction followed by that functor.
* `ringedLocalization_kflat_models` states K-flatness of the restricted P and of the
  coefficient complex concentrated in degree zero, and an isomorphism between their
  total tensor and the ordinary localized complex. These certificates express that
  the identity K-flat replacements compute derived tensor, using precisely the
  definition specified in the node. No arbitrary proposed derived-tensor bifunctor
  or additional flatness hypothesis is introduced. The finite-sum flatness argument
  and restriction-flatness input are described in its proof docstring.
* `ringedLocalization_tensor_product` states that localizing the summand at g after
  localization at f gives the coefficient localization at f*g. Together with the
  existing left-adjoint tensor functor this gives the assertion on finite sums.
* In `ringedLocalizationRHom_calculus`, e is a natural isomorphism of the RHom
  restriction functors. Evaluating it at `(op (Q.obj P), N)` gives exactly the first
  display. The auxiliary e,s comparison interfaces use the general restriction
  assertion of source 08JB so that the final square can also be evaluated at the
  coefficient localization and at the localized complex. They are not hypotheses
  restricting P or N. The first conjunct is the successive-restriction identity.
* c is the second displayed isomorphism. Its coefficient argument is the actual
  localization in degree zero, its inner Hom uses derived restrictions of Q(P),N,
  and its right argument is Q of the ordinary localized complex. Its P argument has
  exactly `IsBoundedLocalizationComplex R P` as a hypothesis.
* The second conjunct is simultaneous naturality: `a : P' ⟶ P` is ANY chain map,
  and `b : N ⟶ N'` is ANY derived morphism. The outer Hom is contravariant in the
  ordinary localized complex; the nested Hom is contravariant in P and covariant
  in N, as the displayed equation specifies.
* The final conjunct quantifies over EVERY `a : V ⟶ U` and f in R(U), restricts f
  by `R.obj.map a.op`, and supplies localization comparisons l and a natural tensor
  complex comparison t. Its equation compares restriction of c with c on V after
  applying s twice, using the fixed relocalization comparison in both P and N.
  Thus this is a commuting compatibility square, not merely pointwise Nonempty
  comparisons. No boundedness condition on N, on its representative or on its
  K-injective resolution occurs anywhere.

Dependency declarations used and read:

* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q` (lines 74–103).
* `Sheaf.Algebra.Homology.DerivedInternalHom`: `CategoryTheory.derivedInternalHom`,
  and its comparison and representative signatures/docstrings.
* `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`
  (lines 45–62), the total tensor from the recorded tensor-complex node.
* `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`, including its separate
  object/morphism universes and the actual acyclic total-tensor predicate.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `overMap`, `overFunctorMap` (lines 59–87).
  The slice topology and ring-sheaf restriction were read in Sites/Over.lean,
  lines 248–266 and 512–526.
* `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction`
  (lines 54–67 and 125–145), applied to the identity ring-presheaf map.
* `Sheaf.CategoryTheory.RingedSectionLocalization`:
  `ringedSectionLocalization`, `ringedSliceSection`, and their actual presheaf
  construction and compatibility signatures. These replace the earlier helper draft.
* `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`: the six exactness
  instances and `ringedInternalHom_restriction`, including its full coherence
  equation and docstring. The current module is available in the side library.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat`:
  `SheafOfModules.isFlat_over`, now recorded on the previously missing prerequisite.

The latter three existing DAG ids have been added to stmt_deps. They are real landed
prerequisites, not new copies. All original dependencies are retained. Proof-dependency
modules are imported as the plan for stage 3. The three theorem docstrings reproduce
all six steps of the node's proof, including exact sheafification, bounded flat
K-flatness, fraction multiplication, K-injective Hom, naturality and further restriction.

Edge cases checked: the zero complex (any two bounds), the empty finite sum, empty
site, zero ring, section f=0 (zero localization), f=1 (the unit), g=1 and g=0, arbitrary
non-diagonal differentials among the localization summands, and arbitrary unbounded N.
The compatibility square allows every slice arrow, including identities. There is
no nonempty-family or nonzero-ring assumption. No statement dispute was found.

Searches actually run (search log in searches.jsonl):

* LeanFinder, “Derived internal Hom commutes with slice restriction and currying
  localization of bounded localization complexes”: eight hits, mostly
  `Functor.mapDerivedCategoryFactors`, shift/single comparisons and derived fraction
  maps. None is the complete localization/RHom calculus statement.
* Loogle, `Localization.Away, CochainComplex`: zero hits.
* Mathlib grep, `localization.*[Hh]om|[Hh]om.*localization` in
  `Algebra/Category/ModuleCat`: two ordinary ModuleCat/Localization.lean comments
  about scalar extension, not this derived-site statement.
* The same rg in upstream WeilConjectures/Algebra/Category/ModuleCat had no match;
  rg of the complete upstream tree for this node id had no match. Project searches
  found no `ringedLocalizationRHom` or `IsBoundedLocalizationComplex` declaration.
* DAG searches by localization, derived restriction and internal-Hom titles found
  the published RingedSectionLocalization and RingedInternalHomExactRestriction
  interfaces and confirmed that the formerly missing slice-flatness node has landed.
  The actual signatures, not only their names, were read. Earlier search failures
  (including LeanSearch HTTP 500) are retained in searches.jsonl as unavailable,
  not as evidence of no match.

Validation uses scompile.py's server entry point only (nice 19, two threads,
60 seconds per file). The script's current ordinary CLI first tries a local compiler,
so this worker calls its existing `run_server` function directly, without changing
any tool. No local compiler, lake build, repository edit or direct git command is used.
The final module compiled cleanly on the server in 6.0 seconds with no errors or warnings;
all required side dependencies also compiled individually. The module text checker reports
no findings (line width, source/blueprint docstrings, verbatim signature, sorry-only proofs).
The delivery dry run is invoked through deliver2.py with `--no-push` and its compiler
function directed to scompile.py's existing `run_server` entry point. A disposable clone
under this item's scratchpad is selected through WEIL_CLONE_PREFIX, preserving the
read-only project checkout. No second-reading text is written by this worker.

The first delivery dry run printed OK: compilation and preflight passed, with only the
independent second reading left for the next worker; nothing was pushed. After making
statement-dependency imports explicitly public, the final packet is checked again by the
same server-only dry run. No statements or definitions changed in that import adjustment.

## Second reading by NB

I read the node statement, its source places (Stacks 08J9, 08JB, and 0996), every
recorded dependency signature, and the submitted module. The itemized correspondence is:

* The small site is `C : Type u` with `[SmallCategory C]` and topology `J`; Lean binds
  `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`. Verdict: exact.
* The commutative ring sheaf is `R : Sheaf J CommRingCat.{u}`; Lean uses that object,
  and `localizationModules R` is the recorded ringed-site module category. Verdict: exact.
* Unbounded derived modules, `Q`, and derived internal Hom are the existing
  `DerivedCategory`, `DerivedCategory.Q`, and `derivedInternalHom` at the standard
  localization size. Verdict: exact; no alternate category is introduced.
* Section localization is `ringedSectionLocalization R`, and slice coefficients are
  `localizationSliceCoefficient R U f` using the recorded `ringedSliceSection`; no
  terminal object or nonzero section hypothesis is added. Verdict: exact.
* `P` is a bounded complex whose terms are finite direct sums of localization sheaves.
  `IsBoundedLocalizationComplex` gives integer lower and upper bounds, `IsZero` outside
  them, and a finite `Fin k` coproduct in each degree, with `k = 0` allowed. Verdict:
  exact, including the zero and empty-sum cases.
* Restriction is `localizationComplexRestriction`; derived restriction is
  `localizationDerivedRestriction`; further restriction is
  `localizationDerivedOverMap`, with canonical comparison
  `localizationRestrictionCompIso`. Verdict: exact canonical constructions.
* For `U` and `f : R(U)`, `localizationSliceComplex` is restriction followed by tensor
  with the degree-zero coefficient `localizationSliceCoefficient`; its differential is
  tensorized. Verdict: exact.
* `ringedLocalization_kflat_models` states K-flatness of both factors and the
  isomorphism from the total tensor to the ordinary localized complex. Verdict: exact
  realization of the node's specified K-flat identity replacements.
* `ringedLocalization_tensor_product` states localization at `f` tensor localization
  at `g` is localization at `f*g`, via the sectionwise fraction construction. Verdict:
  exact, with no extra flatness or finiteness assumption.
* The main theorem supplies `e` (RHom restriction), `s` (further-slice RHom
  comparison), and `c` (the displayed currying/localization isomorphism), followed by
  the restriction coherence square, simultaneous naturality in arbitrary chain maps
  and derived morphisms, and the final compatibility square with coefficient and tensor
  comparisons. Verdict: every clause and quantifier is present in the node's order.
* The final quantifiers impose no boundedness on `N`, its representative, or a
  K-injective resolution. Verdict: exact.

Edge cases checked: empty site and empty finite sums; zero complex and zero ring;
`f = 0`, `f = 1`, `g = 0`, and `g = 1`; `n = 0`; arbitrary differentials between
summands; identity and arbitrary slice arrows; and unbounded target `N`. All are
covered by the submitted types and no hidden nonemptiness or characteristic assumption
appears. Universes use the common site/ring universe required by the dependency
interfaces and leave no unbound variables.

Searches were repeated with `rg` over Mathlib, the upstream WeilConjectures tree, the
project Lean tree, and DAG declarations, plus LeanFinder/Loogle queries for localization,
derived RHom, and tensor complexes. No existing declaration states this complete
calculus or defines `IsBoundedLocalizationComplex`; the recorded section-localization,
exact-restriction, and slice-flatness declarations are the canonical dependencies.

No mismatch was found. I changed no statement, definition, hypothesis, or conclusion;
I only added this second-reading record. The module compiles with `scompile.py` and
contains only the permitted postponed theorem proofs (`sorry`).

Second-reader search details: LeanFinder query `internal Hom localization tensor bounded
complex sheaves` returned Tor and monoidal-closed sheaf results, none an exact match;
Loogle `Localization.Away, CochainComplex` returned zero hits. The searches are logged
by `msearch.py` in this item's searches.jsonl. Exact-name rg over the whole upstream
WeilConjectures tree and project Lean tree found no submitted declaration collision.
The broader rg found ordinary module-localization and derived algebra base-change
results, not this ringed-site calculus. DAG search also found the existing section
localization and restriction nodes: these are reused through the stated imports.

The source context introduces only a ringed site in 08J9/08JB and a global section in
0996; no hidden Noetherian, terminal-object, characteristic, or boundedness assumption
is required. I opened the concrete localization presheaf and its localization-lift
restriction maps, the actual localization-induced RHom functor, K-flat acyclic-total-
tensor predicate, and the restriction functors and their exactness signatures. The
standard derived-category specialization introduces no extra mathematical hypothesis.
The node has no `statement_change`, and this packet has no new nodes or dependency
modules requiring a separate correction or new-node audit. Preflight confirms the
recorded main signature agrees verbatim with the module. The required dry run printed
OK after the second-reading section was added.
