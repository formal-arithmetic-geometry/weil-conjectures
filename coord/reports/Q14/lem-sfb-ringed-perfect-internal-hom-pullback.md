## Worker report

### Repair of returned head 12f557b33b4a (2026-10-23 UTC)

The initial required dry run on the saved packet passed (15580f1212d), but the
requested self-check reproduced the independent review diagnostic: proof_deps
contained lem-coef-ringed-pullback-hom-evaluation-comparison and
lem-sfb-ringed-derived-adjoint-lift although no proof step listed them in uses.
Removed these two surplus entries, restoring proof_deps exactly to the union of
the five accepted steps' uses and to the current main branch's proof_deps.
No proof step or mathematical statement changed. The theorem quantifies a supplied
AdjointLift, so its proof does not invoke the lift-existence theorem; the final
accepted elementary step derives naturality from evaluation and tensorator
naturality directly. The existing definitions remain available through their
correct definition nodes in stmt_deps. This repairs the precise immutable-head
return without inventing proof uses or changing the accepted argument.

The current-main comparison checked that statement and all five proof steps are
identical, and that only the authorized definition-dependency additions and lean
record differ from main. The theorem signature and body are retained. Previous
validation entries below describe the historical packet; validation of this
repair is recorded at the end.


Q14. Historical packet preparation, 2026-10-23 UTC, for immutable head
ffd0ef75cd686229398b157edbe7e0b589134cf5. The assigned sandbox initially held only
launcher markers and searches.jsonl. Restored its node, module and report from that
exact head, then rebased the node metadata on the current read-only shared source.
All writes are confined to the assigned sandbox; no agents were started.

The Lean file Sheaf/SixFunctors/RingedPerfectInternalHomPullback.lean is byte-for-byte
identical to the returned head. It states
CategoryTheory.RingedDerivedComparisons.ringedPerfectInternalHomPullback with sorry.
The reviewer already accepted its hypotheses, every clause, universes and docstring.
The repairs below change dependency ownership only; the mathematical statement and
all five proof steps stay verbatim. There is no statement correction or dispute.

### Repair of the return: H2/H12 theorem-stmt_dep

(a) The item now cites the landed def-sf-ringed-derived-adjoint-lift-data, whose
existing:true declaration is CategoryTheory.RingedDerivedComparisons.AdjointLift
in Sheaf.SixFunctors.RingedDerivedAdjointLift. The existence theorem
lem-sfb-ringed-derived-adjoint-lift is not a statement dependency. It is also not
an explicit proof dependency: the accepted proof works with the supplied lift.

(b) Added def-sfb-ringed-pullback-hom-comparison, an existing:true attachment on
Sheaf.Paper.RingedPullbackHomEvaluationComparison for exactly the four existing
definitions pullbackHomFunctor, pullbackHomTensorModel, pullbackHomTensorator,
and ringedPullbackHomComparison. Its TeX defines beta as the right-adjunction
transpose of L(ev) after t inverse. It asserts no naturality or invertibility.
No Lean definition or module is copied, and the published module is unchanged.

(c) The item cites this definition node in stmt_deps. The theorem node
lem-coef-ringed-pullback-hom-evaluation-comparison is not a statement dependency;
the accepted proof establishes naturality directly, so it needs no explicit
proof dependency on that theorem.
The current main branch has neither of the two rejected statement-dependency
additions, so this packet simply adds the two correct definition dependencies to
main. The five proof steps and their proof-dependency union match main exactly.
No base dependency is removed.
The existing public imports expose the data; the theorem also lives in the same
module, so no duplicate import is needed. Other proof modules remain plain imports.

### Hypotheses and clauses

`Site.{u,w}` is the existing ringed-site presentation of lem-sfb-ringed-derived-monoidal-comparisons, not a new category. X is the source and Y the target. X.A and Y.A are commutative ring sheaves, X.D and Y.D are the ordinary unbounded derived categories of their existing module-sheaf categories; the universe levels implement def-weil-size-convention. The small-site encoding is the same one used by the recorded RingedToposMorphism and comparison modules. The four sheafification/local-bijectivity class arguments are the canonical small-site infrastructure required to apply the existing perfectness predicate, on Y and its localized sites; they impose no flatness, finiteness or cohomological bound.

`f : Morphism X Y` is exactly the recorded RingedToposMorphism, allowing arbitrary geometric morphisms, not just continuous site functors. `l : AdjointLift f` is the existing normalized K-flat derived module pullback with the structural ring map and inverse/direct images identified with f. Its existence is already stated by lem-sfb-ringed-derived-adjoint-lift. This is presentation data for Lu*, not an extra assumed isomorphism or exactness hypothesis. The tensor comparison in the reused map is built from the fixed K-flat representative models.

`pullbackHomFunctor` abbreviates derivedInternalHomOfUniverses, the already recorded derived internal Hom of def-pur-derived-internal-hom, not the ordinary-module-only specialization of that node's current primary record. Its source and target are the actual module-sheaf derived categories. `ringedPullbackHomComparison l P Q` is defined at RingedPullbackHomEvaluationComparison.lean:90 by X.closed.transpose of pullbackHomTensorator followed by l.edge.left.map of Y.closed.evaluation P Q. This is verbatim the right-tensor adjunction and t-inverse composite of the item. No fresh comparison map or unspecified isomorphism was introduced.

The first conjunct quantifies P in Y.D, assumes precisely IsPerfectOnRingedSiteOfUniverses Y.A P, and then quantifies every Q in Y.D and asserts IsIso of this canonical map. The existing perfectness predicate uses covering sieves and bounded complexes of finite-free retracts; it does not require a single global representative or uniform global bounds. The second conjunct restricts P and P' to this perfect subcategory and asserts the contravariant/covariant naturality square for every a : P' -> P and b : Q -> Q'. The composition order is Lean's left-to-right order, agreeing with the node's right-to-left formula. Together the conjuncts give the requested natural isomorphism in the derived category itself. There is no boundedness hypothesis on Q or Q', no flatness hypothesis on f, no point assumption, and no coefficient-field or constant-sheaf restriction.

### Dependency declarations

- def-weil-size-convention: explicit universes u,w, a metatheoretic convention.
- def-weil-sheaf-of-modules-category: CategoryTheory.ringedSiteModules in
  Sheaf.CategoryTheory.RingedSiteModules.
- def-weil-abstract-derived-category: DerivedCategory and HasDerivedCategory in
  Mathlib.Algebra.Homology.DerivedCategory.Basic.
- def-weil-pbc-ringed-topos-morphism: CategoryTheory.RingedToposMorphism in
  Sheaf.CategoryTheory.RingedToposMorphism; Morphism reuses it without alteration.
- lem-sfb-ringed-derived-monoidal-comparisons: ringedDerivedMonoidalComparisons in
  Sheaf.SixFunctors.RingedDerivedMonoidalComparisons. The fixed Site, its D and closed
  structures are publicly re-exported from RingedDerivedComparisonData.
- def-pur-derived-internal-hom: CategoryTheory.derivedInternalHomOfUniverses,
  re-exported by Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom. The actual
  generic ringed-site bifunctor is used, not its ordinary ModuleCat specialization.
- def-weil-pbc-strict-perfect-coefficient-package:
  SheafOfModules.IsPerfectOnRingedSiteOfUniverses in
  Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses.
- lem-sf-ringed-derived-closed-symmetric-monoidal:
  CategoryTheory.ringedDerived_closed_symmetric_monoidal in
  Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal; the Site.closed
  evaluation and transpose are the structures whose witnesses it supplies.
- def-sf-ringed-derived-adjoint-lift-data: AdjointLift as specified above.
- def-sfb-ringed-pullback-hom-comparison: the four existing definitions as above.

Read every dependency statement and record, and the full signatures and docstrings
of the actual definitions, including AdjointLift, Site, Morphism, Site.D,
derivedInternalHomOfUniverses, IsPerfectOnRingedSiteOfUniverses, and all four
comparison definitions. The new node depends on the existing presentation-data,
adjoint-lift-data and derived-internal-Hom definition nodes.

### Edge cases

P=0 gives a comparison between zero derived objects; P=R in degree zero gives the unit comparison and is valid for the non-flat coefficient map Z -> Z/2; shifts use the existing signed tensor and Hom conventions; arbitrary unbounded Q is still allowed since the first variable has finite local bounded models. Ranks and bounds may vary with the covering member. No empty-cover, zero-ring or empty-site case is excluded by an extra nonemptiness assumption. Naturality uses two perfect first variables but arbitrary target variables, exactly the stated restricted natural isomorphism. 

### Searches

All searches used the required msearch.py and are logged in searches.jsonl. LeanFinder queries were “For a morphism of ringed topoi derived pullback commutes with derived internal Hom from a locally perfect complex” and “Strong monoidal pullback of sheaf modules preserves the derived internal hom when its source is a bounded complex of finite projectives”. Both returned underived SheafOfModules pullback/composition/free-module comparisons, not this unbounded derived comparison. LeanSearch “Derived pullback preserves internal Hom with a perfect first argument on ringed topoi” returned underived SheafOfModules and scheme module pullback declarations. The Loogle queries “CategoryTheory.Functor.LaxMonoidal.ihomComparison” and “MonoidalClosed, Functor.Monoidal” reported unknown identifiers and no hits; these are not evidence that those concepts are absent. The required Mathlib grep for “ihomComparison|perfect.*pullback|pullback.*perfect” returned no hits. No exact Mathlib match was found.

Project searches used the blueprint id and perfect/internal-Hom/pullback keywords in lean/WeilConjectures and lean/Sheaf, and blueprint_refs.py search “internal Hom”. Read WeilConjectures.SixFunctors.Etale.Derived.Perfect.Pullback: its existing theorem concerns scheme étale pullback, assumes dualizability directly, and concludes existence of an object isomorphism; it does not state the general ringed-topos result or invertibility of this map. Read WeilConjectures.AlgebraicGeometry.PerfectInternalHomPullbackIsIso: that theorem is for scheme structure sheaves and Scheme.IsPerfect, not arbitrary ringed topoi. Neither is an attachment. The existing generic monoidal exact-pairing comparison is the accepted proof tool, not an exact statement of the current item. The existing ringedPullbackHomEvaluationComparison supplies naturality and normalization but explicitly does not supply invertibility. No duplicate notion was defined.


Repair searches, recorded verbatim as structured tool output in the new node:
LeanSearch query "Canonical derived internal Hom pullback comparison defined as
transpose of pulled back evaluation" returned categorical pullbackComparison,
ihom.ev and exponentiable-morphism currying, no ringed derived comparison.
LeanFinder query "Derived ringed topos pullback internal Hom comparison is
transpose of evaluation after inverse tensor comparison" returned ordinary module
pullback comparisons. Loogle "SheafOfModules.pullback, SheafOfModules.homObj"
returned no hits and unknown identifier homObj. Mathlib grep for the four exact
names returned zero hits. Project and DAG rg found the existing four definitions
only in RingedPullbackHomEvaluationComparison and as auxiliary declarations of
the theorem node; no definition node owns their notion. blueprint_refs.py search
"pullback Hom" returned zero blueprint nodes. Thus reuse the existing declarations
through a new node, exactly as the return requests.

## New nodes

**def-sfb-ringed-pullback-hom-comparison** names the existing evaluation-transpose
construction, its RHom abbreviation, the restriction of the fixed tensor model to
flat-term K-flat representatives and the inverse canonical tensorator. Its source
is Stacks cohomology.tex, remark-prepare-fancy-base-change, the canonical map used
in 0GM7(1), with ringed-site conventions 07A4/08J9. I read the remark: adjunction
identifies the required map with a map LH(P,Q) tensor LP to LQ; tensor pullback
identifies its source with L(H(P,Q) tensor P); apply L to evaluation. This is exactly
the existing body X.closed.transpose of pullbackHomTensorator followed by L(ev).
The definition is valid for arbitrary unbounded P,Q and f. It adds no perfectness,
flatness, or assertion that beta is invertible. Search results above rule out a
second definition node, and no module or datum is duplicated. Its blueprint
ancestor is null, as printed by blueprint_refs.py ancestor for the item; its via
list is the item followed by the current inherited via list.

## Validation

The unchanged theorem module is compiled using the required scompile.py server
wrapper. The dry run and delivery also probe all four declarations of the
existing:true new node and run the server preflight. Results follow below.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and
the maintainer's independent review is the only review.

The first dry run compiled both the theorem and existing-declaration probe, then
requested the current schema field import_flags on the new node; added the empty
list and reran. The mathematical statement is unchanged, so no statement_change record is
introduced.

Final dry run: deliver2.py --no-push exited 0 and printed OK for commit
007a6c0a430: the server preflight passes and both the theorem module and the
existing-declaration probe compile cleanly. The standalone scompile.py also
exited 0. Only the intentional theorem sorry remains; no Lean lines exceed
100 characters, and both recorded signatures are verbatim from their sources.


## Validation of the immutable-head repair

The required standalone scompile.py exited 0 for the retained theorem module.
The self-check verified proof_deps equals the union of every proof step's uses,
without duplicates, and equals the accepted current-main list. Only lean and
the authorized definition additions to stmt_deps differ from current main.
The mathematical statement and all five proof steps match main verbatim.
The recorded Lean signature matches the file verbatim; autoImplicit is false,
all universes and variables are bound, every Lean line is at most 100 characters,
and the only sorry is the intentional theorem proof. The existing:true new
node still owns the four existing comparison definitions without duplicating
any Lean construction. The repaired packet is checked again with deliver2.py
--no-push before the authorized delivery.
