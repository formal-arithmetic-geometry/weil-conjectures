## Worker report

The module `Sheaf.Paper.IntegralDerivedReduction` defines
`WeilConjectures.integralDerivedReduction`, with the actual completed coefficient
sheaf as source and the actual finite constant coefficient sheaf as target. It
is the exact universal left derived functor of termwise change of rings along
the existing limit projection. No item's statement is changed and no new DAG
notion is introduced. All new theorem proofs are `sorry`; definitions contain
real constructions or choices characterized by the universal property in the
recorded dependency theorem.

Hypotheses and clauses, individually:

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite extension: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The valuation ring, chosen uniformizer, its powers,
  quotient rings and reductions are the recorded `Padic.coefficientExtension*`
  declarations, imported through and used by completed integral coefficients.
* The global characteristic convention ell != p is `(D : FiniteFieldDatum.{d})
  (hl : l ≠ D.p)`, exactly as the recorded completed coefficient interface.
* Scheme: `(Y : AlgebraicGeometry.Scheme.{t})`, with its existing
  `Scheme.ProEt.topology Y`. No qcqs, nonemptiness, flatness, boundedness or
  constructibility assumption is imposed on Y or the input complex.
* Positive exponent: `(n : ℕ)` denotes the exponent `n+1`, consistently with the
  recorded completion dependency. Index zero means reduction modulo the first
  power; every positive integer exponent occurs.
* A_(E,n) and its constant sheaf are the recorded
  `integralCoefficientSheaf l E Y n`. The commutative presentation
  `integralCoefficientCommRingSheaf` forgets to this exact ring sheaf.
* Completion and projection are the recorded
  `completedIntegralCoefficientSheaf` and `completedIntegralCoefficientProjection`.
  Their commutative presentations have exactly the same ring data and maps.
  The limit is not replaced by the discrete constant valuation-ring sheaf.
* The source derived category is exactly
  `completedIntegralDerivedCategory l E Y D hl`. The target is
  `DerivedCategory (SheafOfModules (integralCoefficientSheaf l E Y n))`, the
  localization of finite constant coefficient module sheaves; the larger
  coefficient universe is a size lift of the recorded pro-etale derived category.
* For arbitrary K, apply `(integralDerivedReduction ...).obj K`; this defines
  reduction on the entire unbounded derived category and on all morphisms.
* Ordinary change of rings is `integralReductionChangeOfRings`. Its defining
  witness `integralReductionExistence` fixes both its object action to
  `SheafOfModules.changeOfRings` and its map action to
  `SheafOfModules.changeOfRingsHom`, up to the stated object equalities.
  Its `mapHomologicalComplex (ComplexShape.up ℤ)` is therefore precisely
  termwise tensor extension, with the required target coefficient action.
* K-flat and K-flat resolution use the repaired dependency's
  `CochainComplex.IsKFlatIndependentCoefficients` and
  `CochainComplex.IsKFlatResolutionIndependentCoefficients`: total tensor with
  every acyclic complex is acyclic, and augmentation is a quasi-isomorphism.
  `exists_isKFlatResolutionIndependentCoefficients` retains existence with flat
  terms and termwise epimorphic augmentation; those optional stronger model
  properties are not added as restrictions on input K.
* Exact functor L pi_n^*: `integralDerivedReductionUniversal`,
  and `integralDerivedReduction_exact` supply the universal property and the
  existence of a shift comparison with its triangulated-functor proof. The latter
  is a postponed helper theorem directly stating this clause of the owning node,
  with its proof plan by specialization of the general theorem.
  `integralDerivedReductionCounit` is the universal transformation from derived
  localization followed by reduction to ordinary termwise change of rings.
* Computation on P: the postponed helper
  `integralDerivedReduction_counit_isIso` states the computation clause of this
  node, directly specialized from the general theorem (proof plan in its docstring).
  `integralDerivedReductionKFlatIso` is `asIso` of that counit at the image of a
  K-flat P. Its inverse is uniquely determined by the named isomorphism proof. `integralDerivedReductionResolutionIso` first
  inverts the derived image of the augmentation P -> G and composes with the
  K-flat counit isomorphism. This is the node's canonical computation of
  K tensor^L A using any K-flat resolution. Comparing two resolutions by
  inverse/composition through this same reduction object gives the canonical
  comparison; comparisons for a third resolution compose by inverse cancellation.
* All choices are determined in the equality used downstream: ordinary tensor
  has fixed objects and maps, and the derived pair has the left derived universal
  property. No unconstrained Nonempty functor or arbitrary map is selected.

Dependency declarations used:

* `Sheaf.NumberTheory.Padics.CoefficientExtension`:
  `Padic.coefficientExtensionRing`, `Padic.coefficientExtensionTransition`, and
  the valuation-ring/uniformizer data used by those definitions.
* `Sheaf.Paper.CompletedIntegralCoefficients`:
  `WeilConjectures.integralCoefficientSheaf`,
  `completedIntegralCoefficientSheaf`, `completedIntegralCoefficientProjection`,
  `completedIntegralModuleSheaves`, `completedIntegralDerivedCategory`, and
  the added commutative-ring presentations listed in that node's lean record.
* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` and the Mathlib site,
  constant-sheaf and standard localization definitions used in its body.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its resolution predicate.
* `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  `SheafOfModules.changeOfRings` and `SheafOfModules.changeOfRingsHom`, whose
  full object/map actions occur in the repaired derived-change-of-rings theorem.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` and its
  underlying-ring abbreviation. The original theorem is generalized only in
  universe levels and standard sheafification infrastructure.

Edge cases checked: n=0 is exponent one, not the zero quotient; zero and
unbounded complexes are included; the empty scheme is included; E=Q_l is
included; no size equation is imposed between d, t and u. The module universe
is max u (t+1); the small site still has object universe t+1 and morphism
universe t. Sheafification and the abelian-category infrastructure are supplied
by the completion dependency's small-model transport. No STATEMENT-DISPUTED
claim and no statement correction.

Searches made before writing:

* msearch LeanFinder: "Derived reduction of completed integral coefficient
  sheaves modulo powers of a uniformizer on the pro-etale site"; eight hits
  concerning period rings and algebraic completion, no matching sheaf functor.
* msearch Loogle: "Functor.totalLeftDerived, SheafOfModules.changeOfRings";
  zero hits (unknown identifier Functor.totalLeftDerived in the service index).
  The actual local Mathlib source for Functor.IsLeftDerivedFunctor,
  totalLeftDerived and universal uniqueness was read directly.
* msearch grep: "derivedReduction|derived_reduction|totalLeftDerived" in
  Algebra/Homology: zero hits.
* rg in project Lean and WeilConjectures for integralDerivedReduction,
  derivedReduction, completedIntegral.*Comm and completedIntegral.*Reduction:
  no matching declaration. Search for the exact blueprint id in upstream:
  no hits. DAG searches show the genuine general change-of-rings/K-flat nodes
  already present; these are repaired under (B), not duplicated as new nodes.
* Read the full recorded declarations/docstrings for all seven dependencies;
  read Mathlib ring, sheaf reflection, limits and derived functor APIs, and
  the completed coefficient size-transport instances.

Sources read: Bhatt--Scholze PDF, printed p.49, Section 6.5, Definition 6.5.1
and Lemma 6.5.4; Stacks sites-cohomology.tex K-flat resolution (06YS),
derived tensor quasi-isomorphism (06YT), derived pullback (06YV/06YY).
General ringed-site derived pullback justifies arbitrary Y, even though the
constructibility setup of Bhatt--Scholze starts with qcqs X.

## Dependency modules

`def-weil-completed-integral-coefficients`: keep every old declaration unchanged
and add commutativity of the completed ring sections, the corresponding
CommRingCat presheaf/sheaf, and the finite coefficient sheaf and limit projection
in CommRingCat. The old RingCat-only record could not instantiate the dependency
requiring commutative ring sheaves. The added commutativity theorem has the
full proof plan (evaluate the limit and use jointly injective projections).
All other added declarations are explicit constructions from those same data.

`def-pc-kflat-complex`: its recorded predicate fixes coefficients to
max(site-object, site-morphism). The new module retains exactly the total-tensor
acyclicity definition and quasi-isomorphic-resolution definition, but with a
separate coefficient universe. Named monoidal-localization and tensor-zero
proofs are postponed with their source and complete proof docstrings. They
supply only proof infrastructure; the tensor construction is the existing one.
The old module is imported for shared infrastructure, not replaced or weakened.

`lem-pc-kflat-resolution`: the new module gives its full statement in arbitrary
coefficient universe using the repaired K-flat definition. Flat terms,
quasi-isomorphic augmentation and epimorphism in every degree are all retained.
The original proof plan and proof-dependency imports are retained.

`lem-pur-derived-change-of-rings`: the new module gives the same complete
existence/universal/computation theorem in independent coefficient universe,
using the repaired K-flat definition and resolution. In particular it fixes
morphism action as well as object action; it is not mere existence of an
uncharacterized functor. Its sheafification assumption is the usual standard
site-size infrastructure and is constructed canonically in our application.
The original proof plan and proof imports are retained.

Validation: all five delivered modules passed clean server compilation through
scompile.py, nice 19, two threads, 60 seconds per file. The main module took
53.8 seconds; the four dependency modules took 3.5, 1.5, 1.1 and 1.3 seconds.
No warning remains. The final dry run explicitly uses scompile.run_server to
avoid the wrapper's newly present local fast path; no compiler tool is invoked
directly. Final clean
compilation and deliver2.py --no-push preflight results are recorded by the
last validation run. The independent second reading is left to the next worker.
The two own-node helper theorems postponed in the main module are
`integralDerivedReduction_exact` and `integralDerivedReduction_counit_isIso`;
they state precisely the exactness and K-flat computation clauses of the node,
with the general derived-change-of-rings theorem as their complete proof plan.
The two proof-witness aliases are semireducible definitions so elaboration shares
the nested existential witness instead of repeatedly expanding it; the defProp
lint is disabled only for those aliases. They merely apply/project the recorded
dependency theorem and introduce no new unproved fact.

## Earlier second reading (a previous round; superseded)

I read the node, all seven dependency-node statements and recorded signatures,
the five original sandbox modules, and the corresponding base modules. I read
Stacks sites-cohomology.tex at definition-K-flat (06YN), lemma-K-flat-resolution
(06YS), lemma-derived-tor-quasi-isomorphism-other-side (06YT), and the derived
pullback section and lemma-derived-base-change (06YY). Bhatt--Scholze Section 6.5,
printed p.49, assumes qcqs X for constructibility; the operation in this node is
the general ringed-site construction of Stacks, which needs no qcqs hypothesis.
The node concerns arbitrary complexes, not only constructible complexes.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Prime ell: `l : ℕ`, `[Fact l.Prime]`. PASS.
2. Finite field extension E/Q_l: `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
   `[FiniteDimensional ℚ_[l] E]`. I opened CoefficientExtension: its spectral
   absolute value, valuation subring, chosen uniformizer, ideal power, quotient
   and quotient-factor transition are exactly the dependency's objects. PASS.
3. Global characteristic convention: `D : FiniteFieldDatum.{d}` and
   `hl : l ≠ D.p`, as in the completed coefficient dependency. There is no
   additional characteristic restriction on Y. PASS.
4. Scheme Y: `Y : AlgebraicGeometry.Scheme.{t}`, with `Scheme.ProEt.topology Y`.
   The site is the existing small pro-etale site, with objects in t+1 and
   morphisms in t. No separatedness, qcqs or nonemptiness hypothesis. PASS.
5. Positive integer exponent: Lean `n : ℕ` means exponent n+1 in
   `integralCoefficientSheaf`, whose body uses
   `Padic.coefficientExtensionRing l E (n+1)`. This parametrizes every positive
   exponent, consistently with the dependency. PASS.
6. A_(E,n) and its constant sheaf: `integralCoefficientSheaf` is the forgotten
   constant CommRingCat sheaf on the ULift of that exact quotient. I read the
   constant-sheaf construction and ProEtaleDerivedCategory signature; the
   coefficient lift is necessary for independently sized E and Y. PASS.
7. Completed sheaf and projection: `completedIntegralCoefficientSheaf` is the
   limit of the quotient sheaf sequence, and
   `completedIntegralCoefficientProjection` is `limit.π` at `op n`.
   `completedIntegralCommRingSheaf` and `completedIntegralCommRingProjection`
   retain the same ring data and map, rather than introduce a discrete constant
   valuation-ring sheaf. PASS after the missing surjectivity clause below.
8. The arrow marked twoheadrightarrow: the first worker supplied only a map.
   Added `integralDerivedReductionProjection_locallySurjective`, stating
   `Presheaf.IsLocallySurjective` of this very projection. Its proof plan lifts
   local constant quotient representatives to the valuation ring, then uses
   all their compatible reductions and the limit universal property. This is
   exactly sheaf surjectivity, not sectionwise surjectivity on every object.
   PASS after repair; this is a clause of the owning definition node.
9. Source D(Y_proet,O_E): `completedIntegralDerivedCategory l E Y D hl` is the
   standard unbounded localization of completed-coefficient module sheaves.
   Target: `DerivedCategory (SheafOfModules.{max u (t+1)}
   (integralCoefficientSheaf l E Y n))`. It is the dependency's constant-ring
   module construction with the ambient coefficient universe enlarged, not the
   derived category over a discrete constant O_E. PASS.
10. Arbitrary K and a K-flat resolution P -> G representing K:
    `(integralDerivedReduction ...).obj K` is defined for every derived object.
    `integralDerivedReductionResolutionIso s hs` works for every augmentation
    with `CochainComplex.IsKFlatResolution s`, namely `QuasiIso s ∧ IsKFlat P`.
    No flat-terms or boundedness condition is added to this computation. PASS.
11. Existence even with flat terms and termwise surjectivity:
    `exists_isKFlatResolutionIndependentCoefficients` has all four clauses:
    K-flatness, exactness of tensorRight by each term, QuasiIso, and degreewise
    Epi. Exact tensorRight is flatness, and Epi is local/sheaf surjectivity.
    The quantifier is every unbounded G, in independent coefficient universe r.
    PASS.
12. Termwise tensor along pi_n: `integralReductionChangeOfRings` chooses the
    witness whose object action is `changeOfRings φ M` and whose map action is
    `eqToHom (h M) ≫ changeOfRingsHom φ M a ≫ eqToHom (h N).symm`.
    I opened TensorProduct: these are sheafified sectionwise extension of
    scalars and the sheafification of id tensor a, with the quotient action.
    Its mapHomotopyCategory therefore includes the right differential maps.
    The chosen ordinary functor is fixed on both objects and arrows. PASS.
13. Canonical independence: `integralDerivedReductionCounit`, its universal
    instance, and `integralDerivedReductionKFlatIso` give the canonical counit
    comparison on every K-flat P. `integralDerivedReductionResolutionIso`
    inverts the derived image of s, then composes with that comparison.
    Comparisons between two resolutions pass through the same derived object;
    comparisons for a third compose by inverse cancellation. PASS.
14. Exact functor L pi_n^*: `integralDerivedReductionUniversal` states the left
    derived universal property; `integralDerivedReduction_exact` supplies a
    CommShift and triangulatedness. The general dependency also retains
    pointwise existence and quasi-isomorphism preservation between K-flat
    complexes. The identity-site ring map is the actual limit projection,
    so this is precisely the derived pullback in the last clause. PASS.

Edge cases: n=0 denotes exponent one, so no positive exponent is lost and the
zero-exponent quotient is not substituted. The zero complex, arbitrary shifts
and unbounded complexes are admitted. The empty scheme is admitted. There is
no varying index family in this node; its completion sequence is ℕᵒᵖ, not an
empty indexing set. E=Q_l and every prime distinct from the global p are
admitted. Universes d, t, u are independent. Coefficients live in max u (t+1);
no equality between site object and morphism universes is imposed. The new
`integralReductionSiteEssentiallySmall` is constructed by `essentiallySmallSelf`
and is infrastructure, not an extra input hypothesis.

Independent searches: msearch LeanFinder query "unbounded derived scalar
extension for sheaves of modules along a quotient ring sheaf" returned eight
hits (sheafification, abelianity and local cohomology), none this functor.
Loogle "SheafOfModules, Functor.IsLeftDerivedFunctor" returned no indexed
match (unknown derived-functor identifier). msearch grep
"scalarExtension|reductionModIdeal|derivedChangeOfRings" returned no hits.
Direct rg searches used reduction/Reduction, changeOfRings/change_of_rings,
scalar extension, and the actual declaration names in Mathlib, upstream
WeilConjectures, side Sheaf, and the exact 51-module framework checkout.
I opened upstream Etale.reductionModIdeal: it is an endofunctor on sheaves of
constant Λ-modules on the etale site, not extension from the completed ring
sheaf to quotient-ring modules on the pro-etale site. I opened
ModuleObjects.DerivedExtendScalars and ModuleObject.ChangeOfCoefficients:
they use internal modules over condensed ring objects, not this recorded
SheafOfModules encoding. They are not exact matches.

The direct search did reveal a concurrent published repair of KFlat. The
first worker's IndependentCoefficients predicate had become a duplicate of
`CochainComplex.IsKFlat`. I removed that module and its replacement record,
and changed every use to the published `IsKFlat`/`IsKFlatResolution`.
The published KFlat module now has separate site/coefficient universes and
relative-smallness infrastructure. The compiler still selected an older live
artifact when this module was not supplied among siblings. This delivery
therefore includes the published KFlat declarations as a dependency module,
with its current node record and an explanatory lean.note. It introduces no
second predicate and does not revert the concurrent repair.

Dependency-module review: CompletedIntegralCoefficients keeps the old inverse
system, limit, categories and restriction functor verbatim, and adds only the
commutative presentation on the same sections and maps. Its sole new postponed
commutativity proof uses jointly injective limit projections. KFlat retains the published generalized declarations; its first tensor-zero
proof docstring is corrected as described below. KFlatResolutionIndependentCoefficients
still needs a repair because the recorded General theorem fixes coefficients
to max(site universes); its repaired statement uses the published K-flat
predicate and retains every node clause. DerivedChangeOfRingsIndependentCoefficients
has the same remaining coefficient-size issue, and retains object AND arrow
identifications, quasi-isomorphism preservation, pointwise existence, universal
pair, exactness and counit computation. Relative smallness is now explicit in
these two generic signatures, and constructed canonically for our site. Their
node lean.statement fields were refreshed verbatim from the repaired signatures.
No new DAG notion, statement correction or target change is required.

No data are sorry. The choices of ordinary functor are fixed on objects and
maps, and the derived pair is determined up to its universal compatible
isomorphism. `asIso` uses named isomorphism proofs. Every theorem supplied in
this delivery has only sorry as proof and a source/blueprint/proof docstring;
the newly added projection theorem supplies the previously omitted clause.
The earlier worker validation and five-module description refer to the
pre-review version; this section and the following validation record supersede
those descriptions.


The first dry-run preflight rejected an unchanged KFlat source as a delivered
module and its inherited NR authorship record. I corrected lean.by to NB and
repaired an actual documentation gap: the first tensor-zero helper's proof
plan inferred zero-morphism preservation just from being a left adjoint.
The replacement plan tensors the zero presheaf, uses preservation of the
initial/zero object by sheafification, then factors each zero morphism through
that zero object. All signatures and definitions of the published KFlat
module are unchanged. This is a documentation repair of the dependency,
not another definition of K-flatness.

Final validation: the repaired five-module delivery, including the projection
local-surjectivity theorem, compiled cleanly through the prescribed wrapper.
`deliver2.py NB def-weil-integral-derived-reduction --no-push` printed
`OK (dry run): commit f026e94bce passes the preflight and compiles; nothing pushed`.
All delivered files have been compiled separately; no global build was run.


## Repair of immutable-head timeout (2026-10-15)

The maintainer returned head 062c3673a5ae because the main module exceeded
the 60-second file-only limit. I repaired the elaboration cost in the
existing module; I did not split it or raise the limit.

`integralReductionDerivedExistence` previously inferred its result type by
projecting the nested existential returned by `integralReductionExistence`.
That inferred type retained the dependency's underlying-ring presentations
and localization instances. Later projections repeatedly converted this
large type to the named completed and finite coefficient module categories.
The repair writes its full result type explicitly using those named
categories, the chosen ordinary functor, the same universal counit, the
left-derived universal property, triangulatedness, and the K-flat counit
isomorphism. Its body is the same projection of the same witness. The
compiler checks the conversion once at this boundary. No mathematical
hypothesis, statement clause, construction, declaration name, or import
changes; no extra theorem or postponed proof is introduced. The node's
recorded main signature remains verbatim unchanged.

Validation: the prescribed scompile.py wrapper compiled all five delivered
modules locally, each separately. The main module took 11.8 seconds as both
Sheaf.Stage2.Sandbox4 and Sheaf.Paper.IntegralDerivedReduction, with no
errors or warnings. The four dependency modules also passed. The 60-second
limit, nice 19, and two-thread settings were retained. This supersedes the
older validation timing and server-only workaround described above.

## Second reading by NB

I reread the node statement against the source place (Bhatt--Scholze §6.5,
p. 49, Definitions 6.5.1 and Lemma 6.5.4) and the recorded dependency
signatures. The checklist is:

1. `l : ℕ` is prime (`Fact l.Prime`): rendered by every declaration in the
   module; PASS.
2. `E/ℚ_[l]` is a finite field extension: rendered by `E`, `Field E`,
   `Algebra ℚ_[l] E`, and `FiniteDimensional`; PASS.
3. `D` and `hl : l ≠ D.p` supply the global characteristic convention: PASS.
4. `Y` is an arbitrary scheme and uses its small pro-etale site: PASS; no
   qcqs, separation, nonemptiness, or boundedness assumption is added.
5. The positive exponent is represented by `n : ℕ` as `n + 1` in the recorded
   coefficient sheaf: PASS, including exponent one at `n = 0`.
6. `integralCoefficientSheaf l E Y n` is the exact finite constant coefficient
   sheaf, and `completedIntegralCoefficientSheaf` is the inverse limit: PASS.
7. `completedIntegralCoefficientProjection ... n` is the actual limit
   projection; its locally-surjective sheaf clause is stated by
   `integralDerivedReductionProjection_locallySurjective`: PASS.
8. The source and target derived categories are rendered by
   `completedIntegralDerivedCategory ...` and
   `DerivedCategory (SheafOfModules (integralCoefficientSheaf ...))`, with
   target universe `max u (t + 1)`: PASS.
9. `integralDerivedReduction` is defined for every derived object and its
   counit is termwise `changeOfRings`; the witness fixes object and morphism
   actions: PASS.
10. K-flat resolutions, including the existence theorem with flat terms and
    degreewise epimorphic augmentation, are imported from the recorded
    independent-coefficient dependencies: PASS; these are not input
    restrictions.
11. The universal left-derived property is
    `integralDerivedReductionUniversal`; exactness is the postponed theorem
    `integralDerivedReduction_exact`; PASS.
12. Computation on a K-flat complex is
    `integralDerivedReduction_counit_isIso`, and computation from any
    K-flat resolution is `integralDerivedReductionResolutionIso`: PASS.
    The latter gives the canonical comparison through the same derived object,
    so comparisons compose for a third resolution.

Edge cases are covered: `n = 0` means the first power, zero and unbounded
complexes and the empty scheme are allowed, `E = ℚ_[l]` is allowed, and the
universes `d`, `t`, and `u` remain independent. The completion index is the
fixed nonempty natural inverse system; no empty-index assumption is introduced.

Searches were repeated with LeanFinder/Loogle and `rg` over Mathlib, the
upstream `WeilConjectures` tree, and the project `lean/Sheaf` tree for
`integralDerivedReduction`, derived reduction, scalar extension, and
`totalLeftDerived`. No existing declaration has this notion or statement.
The exact recorded dependency declarations were opened, including the
independent-coefficient K-flat and derived-change-of-rings interfaces.

The first reading found two mismatches and repaired them. The ordinary
projection had only a map, so the module now states the missing local
surjectivity clause for the sheaf projection. The derived witness also had
an expensive inferred existential result; its result type is now written
explicitly, preserving the same universal property, exactness, and K-flat
computation. No node statement, hypothesis, quantifier, or definition was
weakened or strengthened. The dependency modules retain real constructions;
all postponed proofs have source and blueprint docstrings, and no definition
contains `sorry` data.
