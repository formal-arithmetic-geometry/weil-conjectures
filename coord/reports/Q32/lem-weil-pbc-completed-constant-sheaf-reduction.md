## Worker report

The primary module is `Sheaf.Paper.CompletedConstantSheafReduction`, in namespace
`AlgebraicGeometry.Scheme.CompletedConstantReduction`. Its two main theorems are
`completed_constant_sheaf_reduction` and `finite_coefficient_identification`.
No proofs are supplied. Every postponed assertion is a named theorem with a source,
owning blueprint tag, and natural-language proof; constructed data contain no `sorry`.
The target's statement, dependencies, proof and other fields are unchanged.

Hypotheses and clauses of the item:

- `T : Scheme.{u}` is arbitrary. `A : Type (u+1)`, `CommRing A`,
  `IsNoetherianRing A`, and `I : Ideal A` are precisely the coefficient assumptions.
  There is no completeness, principal-ideal, regularity, finiteness, or nonempty-site
  assumption. Site objects have universe u+1 and morphisms universe u.
- Positive exponent a is encoded bijectively as `n+1`, for `n : ℕ`.
  `adicLisseConstantRing` and `adicLisseConstantModules` are the recorded constant
  sheafifications. `adicLisseCompletedRing T I` is the limit of the constant quotient
  ring sheaves. `base_exists` fixes the base homomorphism by every projection equation;
  `base` selects this unique map and `completedModule` retains its constant A action.
- Flatness is `SheafOfModules.IsFlatOnSite (completedModule T I)`, meaning the actual
  sheaf tensor functor is exact. This is the first conjunct of the main theorem.
- `reduction_exists` fixes the ordinary map uniquely by the formula
  b tensor x maps to pi_n(b) times the constant image of x, at every site object.
  `residue` is the quotient sheaf with its B action through pi_n. The second conjunct
  says this very map is invertible, rather than merely asserting existence of an iso.
- `reductionComplex` is extension applied to the augmentation, followed by the
  degree-zero comparison and that ordinary reduction. The third conjunct says that
  for every K-flat quotient resolution this map is a quasi-isomorphism. Thus it
  states the canonical derived isomorphism on all K-flat representatives, retaining
  the augmentation and target; it does not replace it by an arbitrary isomorphism.
- The last conjunct quantifies over a complex F, augmentation f, and integer bounds
  a,b. `QuasiIso f` expresses the resolution; `Module.Finite` and
  `Module.Projective` express each finite-projective term. `IsZero (F.X i)` outside
  the interval gives boundedness without assuming positive degrees or a nonzero term.
  `constantComplex` and `constantAugmentation` are termwise constant sheafification
  and its canonical single-degree comparison. The conclusion says its tensor
  extension, with the specified augmentation, represents the same reduction.
  `IsFiniteRetract` explicitly gives inclusion and retraction into a finite coproduct
  of copies of B, with inclusion followed by retraction equal to identity. The final
  clause retains the two original bounds after extension.
- The finite clause has only the additional `hf : ∀ n, Finite (A ⧸ I^(n+1))`.
  `systemComparison` sheafifies the constant-function map and its naturality is stated
  for every transition. `finite_coefficient_identification` says all these component
  maps and their induced limit map `completedComparison` are invertible.
  The target ring is the finite continuous-on-connected-components construction in
  `AdicCoefficients.coefficientRing`; its actual inverse limit is `completedRing`.
  `finiteReduction_exists` fixes the transported reduction by pi_n times the image
  of the quotient constant in this finite coefficient sheaf. Both its invertibility
  and the quasi-isomorphism for every K-flat quotient resolution are asserted.
  This is the finite-coefficient interpretation of the canonical derived reduction.

Dependency declarations used:

- `Sheaf.Paper.AdicLisseModule`: `adicLisseConstantRing`, `adicLisseConstantModules`,
  `adicLisseConstantUnit`, `adicLisseRingSystem`, `adicLisseCompletedRing`,
  `adicLisseForget`; these retain the existing constant/limit constructions.
- `Sheaf.Paper.CompletedConstantFiniteComplexRealization`:
  `completedConstantModules`, `completedConstantExtension`, `completedConstantQ`,
  `completedConstantDerived`, `completedConstantGenerator`. In particular scalar
  extension uses the existing specified sheafified tensor construction, not another
  coefficient convention.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientPresheaf`; the coefficient ring
  presentation lifts this very presheaf to CommRingCat so scalar extension retains
  commutative coefficients. Its sections and restrictions are unchanged.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`; `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlat`; `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` for the dependency datum's perfect quotients.
- Mathlib: `constantSheaf`, `Ideal.Quotient.mk`, `Ideal.Quotient.factorPowSucc`,
  `Module.Projective`, `Module.Finite`, `IsNoetherianRing`, `SheafOfModules.restrictScalars`,
  `CochainComplex.singleFunctor`, `Functor.mapCochainComplexSingleFunctor`,
  `CategoryTheory.Abelian.functorCategoryAbelian`, exact evaluation of functor
  categories, and `Functor.mapDerivedCategory`.

The added dependency module uses `Datum` for the Noetherian/torsion/finite/perfect
hypotheses. `Towers`, `Derived`, `DerivedTowers` and `derivedEvaluation` fix the actual
categories and exact evaluation. `residueSystem` is uniquely specified on objects and
all transition sections. `tensorTower` and `complexTower` are the actual tensor
construction. `ReductionTower` retains a universal derived counit and invertibility
on every K-flat complex; this universal property determines the selected construction
up to its unique compatible isomorphism. `DerivedExtension` retains the same data
for quotient scalar extension and `quotientReduction` retains quotient coefficients.
`balancing_exists` specifies the ordinary chain map on all local pure tensors;
`normalization_exists` specifies the derived map by its equation with the K-flat
counits. Its selected isomorphism is `normalization`. `normalization_cocycle` states
triple compatibility and naturality is part of the natural isomorphism.
`quotientMap`, `projection_quotientMap`, and `quotientNormalization` specialize it to
all ordered quotient indices, including equal indices. These are universal-property
choices with specified data, never arbitrary chosen maps or unconstrained isomorphisms.

Edge cases checked mathematically before stating: I=0 gives the constant coefficient
limit; I=top gives zero quotient rings and the zero completed coefficient ring.
Nilpotent and nonprincipal ideals require no change. The zero ring is allowed.
For an empty scheme the empty covering identifies sections as required, and the
finite comparison still holds. Zero complexes, rank-zero retracts, empty support
intervals and repeated quotient indices are included. No assumption that the
completion map A to its completion is injective or that A is complete is introduced.

Searches for existing declarations:

- msearch.py leanfinder, "inverse limit sheaf of constant quotient rings is flat and
  derived tensor with quotient is quotient": eight ingredient-level hits; no match.
- msearch.py loogle, "SheafOfModules.IsFlatOnSite, DerivedCategory, constantSheaf":
  no hits (project declaration not indexed there).
- msearch.py grep, "completed|coefficientDatum|inverse.*limit", RingTheory:
  four unrelated ingredient hits; no target theorem.
- msearch.py grep, "completed.*[Cc]onstant|[Cc]onstant.*completed|completion.*flat",
  CategoryTheory: no hits.
- msearch.py leansearch for adic completed coefficient ring sheaf strict reductions:
  the service returned Internal Server Error, so repository and Mathlib searches
  were used as well.
- rg in Mathlib, upstream WeilConjectures and side-project Sheaf for completed,
  constant, reduction, normalization, balancing and derived tensor declarations;
  no existing statement of this item. Found and reused the NY finite-complex
  realization module and the finite coefficient presheaf interface.
- Search for the node id in upstream WeilConjectures: no existing theorem.
  `scompile.py --source Sheaf.Paper.AdicCoefficientDatum` returned unavailable on
  repeated checks; read-only server delivery-branch searches found none for that node.

Sources read: the node and all its statement dependency records, recorded signatures
and docstrings; the coefficient-datum node; Stacks Tags 093J and 093M at
https://stacks.math.columbia.edu/tag/093J and
https://stacks.math.columbia.edu/tag/093M; the existing finite-function and completed
constant modules. No disputed item statement or source correction was needed.

## Dependency modules

`def-weil-pbc-adic-coefficient-datum` had no Lean record and its server module source
was unavailable. As required by the human's unstated-dependency rule, this delivery
supplies `Sheaf.Paper.AdicCoefficientDatum` and changes only this existing node's
`lean` field. It gives the adic datum, actual finite function coefficient ring system
and completed limit, strict tower and derived coefficient categories, the universal
K-flat tower and quotient scalar extensions, and the explicitly normalized balancing
maps with naturality and cocycle. Its construction deliberately retains the small
pro-etale site's different object and morphism universes. No new DAG node is added.


Repair and completion of the earlier sandbox attempt: fixed the missing tensor notation
scope and malformed term type in `sameTensorSection`, and removed all long lines.
Added the dependency's explicit derived evaluation identification: `evaluationComplex`
and `restrictionComplex` apply the exact functors termwise;
`complexEvaluationComparison_exists` fixes the ordinary chain comparison in each degree
by the already specified pure-tensor comparison. `evaluationCounit` and
`restrictionCounit` use Mathlib's exact-functor localization comparison.
`evaluationComparison_exists` specifies the unique derived natural isomorphism by the
commuting equation with both counits on every K-flat representative.
`evaluationComparison` selects precisely this isomorphism. Thus the dependency states
that evaluation of the strict derived tower is restriction of the quotient-coefficient
reduction, with its canonical computation retained.

Fresh searches in this repair used msearch.py LeanFinder with “The inverse limit of
constant quotient sheaves of a Noetherian ring is flat and its derived tensor with each
quotient is that quotient” (eight ordinary adic-completion ingredient hits, no sheaf
statement), Loogle `AdicCompletion.flat_of_isNoetherian` (one ordinary-module theorem),
and grep `completion.*flat|constantSheaf.*[Tt]ensor` in CategoryTheory (zero hits).
LeanSearch “completed adic coefficient sheaf tower evaluation and quotient normalization”
returned Internal Server Error. Direct rg searches for the item id, its theorem names,
`AdicCoefficients`, and `constantComparison` in the upstream and side libraries found no
existing statement to reuse. `scompile.py --source Sheaf.Paper.AdicCoefficientDatum`
again reported “Module source unavailable”. Stacks source pages 093J, 093M and 099M
were opened directly in this repair; no change to the node statement is needed.

The recorded `derivedTensor` is specialized to a lifted constant coefficient ring;
the statement here is given on every K-flat representative using the recorded
independent-universe scalar extension and `CochainComplex.IsKFlat`. This is the same
derived tensor with the completed first factor, expressed by resolving its quotient
factor, with the canonical augmentation map retained. Its quasi-isomorphism statement
is equivalent to invertibility in the derived category. The specialized definition
module remains a proof import; no duplicate derived-tensor notion is introduced.

## Earlier second reading (a previous round; superseded)

I independently read the item node, all nine statement-dependency records, the
sandbox's two modules, the actual constant/module/flatness/tensor/K-flat/derived
change-of-rings interfaces, and the finite-function coefficient interface. I read
Stacks `sites-modules.tex`, Section `section-constant`, especially
`lemma-constant-exact` (093J) and `lemma-completion-flat` (093M), directly from
Stacks' source, and `proetale.tex` Section `section-derived-completion-noetherian`
(099L/099M). The repository's literature checkout is absent on this machine, so
these source copies are in this item's scratchpad. The source assumes an arbitrary
site, a Noetherian ring and an ideal; it does not assume that the ring is complete
or that the ideal is principal. Applying the quotient assertion to I^a and using
its cofinal power filtration gives every positive reduction in the node.

Object, hypothesis and conclusion checklist (H3):

1. Arbitrary scheme T and its small pro-etale site: `T : Scheme.{u}` and
   `ProEt.topology T`, with objects `T.ProEt : Type (u+1)` and morphisms in u.
   I opened `ProEtaleDerivedCategory` and the Mathlib pro-etale interface. PASS.
2. Commutative Noetherian A and arbitrary ideal I: `[CommRing A]`,
   `[IsNoetherianRing A]`, `I : Ideal A`. These are the recorded Mathlib notions.
   The main theorem takes neither `Datum` nor its torsion/finite/perfect fields;
   those fields therefore impose no hidden hypotheses on this item. PASS.
3. Constant ring and modules: `adicLisseConstantRing` is exactly
   `constantSheaf ... CommRingCat`, and `adicLisseConstantModules` is associated
   module sheafification of the constant module presheaf. I opened their bodies,
   not only their names, and `completedConstantGenerator`'s sheafification unit.
   These are the node's underline A and underline M. PASS.
4. B and its canonical algebra structure: `adicLisseCompletedRing T I` is
   `limit (adicLisseRingSystem T I)` with actual quotient transitions.
   `base_exists` characterizes the constant-to-limit map by every projection;
   `base` selects that unique map. `completedModule` restricts the unit B-module
   along this map. There is no arbitrary algebra map assumption. PASS.
5. Positive exponents: `n : ℕ` represents the positive exponent `n+1` throughout
   both diagrams and both main theorems. This is an order-preserving bijective
   reindexing of the positive integers, not the omission of exponent one. PASS.
6. Flatness: the first conjunct is `SheafOfModules.IsFlatOnSite
   (completedModule T I)`. I opened `FlatOnSite`: its `siteSheafTensorRight` is
   the actual sheafified sectionwise tensor, and exactness means preservation
   of finite limits and colimits. This is the required flatness over underline A,
   rather than an unjustified claim about sections over underline A(U). PASS.
7. Canonical ordinary/derived reduction: `residue T I n` retains B's action via
   the nth projection. `reduction_exists` uniquely specifies reduction by
   b tensor x mapping to pi_n(b) times the constant image of x, on every U.
   Constants locally generate the quotient sheaf, so this determines the full
   sheaf map. The second conjunct makes that very map invertible. The third
   quantifies over each K-flat P with quasi-isomorphic augmentation to the
   quotient in degree zero, and makes `reductionComplex ... P f` a quasi-iso.
   Its body applies the recorded scalar extension to f, then the degree-zero
   comparison and the specified reduction. Thus it states the derived reduction
   on every representative with its canonical augmentation, not an unrelated iso.
   K-flat resolutions exist through the imported recorded resolution interface.
   The older `derivedTensor` specializes to a lifted constant ring; using the
   recorded general scalar-extension functor here supplies the same derived
   tensor with B while retaining the B-module action. PASS.
8. Conditional finite-projective resolution: the final conjunct quantifies over
   F, its augmentation f, and arbitrary integer bounds a,b; its hypotheses are
   `QuasiIso f`, termwise `Module.Finite` and `Module.Projective`, and `IsZero`
   outside [a,b]. `constantComplex` applies the recorded constant functor
   termwise, and `constantAugmentation` includes its actual degree-zero
   comparison. The conclusion is the canonical reduction quasi-iso,
   `IsFiniteRetract` for every extended term, and vanishing outside the same
   bounds. `IsFiniteRetract` supplies both splitting arrows into a coproduct
   indexed by `Fin r`, with composite identity; it says exactly direct summand
   of a finite sum of B. I checked the parenthesis scope: the bounds remain
   under the F/f/a/b quantifiers. PASS.
9. Finite-coefficient clause: `hf : ∀ n, Finite (A ⧸ I^(n+1))` is the only
   additional assumption in `finite_coefficient_identification`.
   `systemComparison` sheafifies constants-to-functions, with all transitions
   respected by `systemComparison_naturality`; `completedComparison` is its
   actual limit map. The theorem asserts invertibility at every level and on
   the limit, then invertibility of the specified finite reduction and its
   quasi-isomorphism on every K-flat quotient resolution. `finiteReduction_exists`
   fixes the transported map by the same projection/multiplication formula.
   These are the stated identifications with (P_n)_T and A_T. PASS.

Dependency-module audit (H12/H13): a freshness check after the first successful
dry run found Q39's now-landed `Sheaf.Paper.CompletedAdicCoefficientDatum`.
I retrieved its current source with `scompile.py --source`, read its entire
487 lines and its inherited `CompleteCoefficientDatum`, and repaired this
delivery to reuse it by public import. The original sandbox's independent
`Datum`, strict/derived tower, scalar-extension, balancing, normalization and
evaluation declarations were removed. The retained `tensorSection` is an
abbreviation of the landed `completedAdicChangeTensor`, whose ordinary witness
is definitionally the same as `completedConstantExtension`.

The landed finite-ring system requires a full `AdicCoefficientDatum` (including
perfect quotients) and ties its A and T to universe t, lifting quotients to t+1.
It cannot state this item's comparison for arbitrary A in Type (u+1), T in
Scheme.{u}, and finite quotients without perfectness. Under §1(B), the sibling
module therefore retains only the generalized finite-function commutative-ring
presentation, its quotient system/limit, the restricted quotient unit module,
and constants-to-functions map. Its restrictions reuse the recorded
`ProEtale.finiteCoefficientPresheaf`; `finiteRingComparison_exists` fixes the
canonical isomorphism with the existing RingCat sheaf by the sheafification
units. There is no independent datum or second derived tower in this delivery.
The dependency's primary record is now `coefficientRing`, with a note explaining
the precise unusable specialization and reuse of the landed datum. The node's
mathematical statement is unchanged. No new nodes or statement corrections were
introduced.

Edge cases: n=0 is exponent one. I=0, I=top, nilpotent/nonprincipal ideals and
the zero ring are allowed. The zero complex and empty support interval (a>b)
are allowed, and rank r=0 is included in the retract. No index-set nonemptiness
is imposed. The limit index itself is the fixed nonempty positive tower. Empty
schemes and empty site objects are covered; the finite-comparison proof uses
the empty covering. No reducedness, characteristic, invertibility or torsion
assumption is imposed on the main theorem. The coefficient/module size u+1 is
the recorded small-site convention, with site morphisms still of size u;
there are no unbound extra universe variables or equality of site sizes.

Independent H4 searches in this reading:

- LeanFinder: "The completed locally constant ring sheaf is flat and tensoring
  with its quotient is the constant quotient sheaf": eight condensed/locally
  constant module ingredient hits, no matching statement on this site.
- Loogle: `"AdicCompletion", "Flat"`: one result,
  `AdicCompletion.flat_of_isNoetherian`; opened its ordinary completion context,
  which does not state sheaf flatness or the canonical reduction comparison.
- msearch grep in CategoryTheory: `constantSheaf.*[Tt]ensor|completion.*flat`:
  no hits.
- LeanSearch: "Flat completion of a constant sheaf of rings and canonical finite
  quotient reduction on a pro-etale site": unavailable (Internal Server Error).
- Direct rg in Mathlib, upstream WeilConjectures and project Sheaf for completion,
  constant sheaves, `CompletedConstantReduction`, `AdicCoefficients`,
  `IsFiniteRetract`, `ReductionTower`, and normalization names. Read the existing
  `CompletedConstantFiniteComplexRealization`, its `completedConstantBaseMap`,
  and the integral/adic reduction tower interfaces. The base map there additionally
  takes an ordinary-completion comparison; those tower interfaces use different
  coefficients or a diagram of derived categories. None supplies this theorem.
  The now-landed completed adic datum is reused,
  with only its finite coefficient presentation generalized as explained above.

No mismatch in the item's mathematical statement was found. The second reading
repaired H4 freshness: the dependency now reuses the landed datum and its derived
towers, discards duplicate constructions, and retains only the needed general
finite coefficient interface. Definitions have actual data or uniquely specified
canonical maps; every postponed assertion has its source, blueprint and proof
plan. The main theorem statement remains unchanged and its `lean.statement`
matches the entire file signature verbatim. The dependency record was updated
to the exact generalized `coefficientRing` signature. All theorem proofs remain
`sorry`, with no unbound universe variables or file-local notation.

Verification before the freshness repair: the required scompile.py packet
compiled both original siblings without errors or warnings (46.4 and 10.2
seconds), and deliver2.py --no-push printed OK. After the freshness repair, both reduced/reused siblings again compiled
cleanly through scompile.py: the dependency took 12.7 seconds and the main
module 8.7 seconds. The final delivery is preflighted again after the repair. No direct compiler or global build was run.

The final preflight caught imported Q39 declarations mistakenly included in the
sibling's `lean.declarations`; those imported names were removed from this
file-local declaration list. The public import still reuses all their code.

Final validation: deliver2.py --no-push printed OK for commit cffc6c6910,
confirming the repaired packet compiles and passes the server preflight.


## Returned delivery repair

The immutable-head return named three elaboration errors inside the imported
`Sheaf.Paper.CompletedConstantFiniteComplexRealization`: the retired names
`SheafOfModules.isMonoidal_W_independentCoefficients` and
`CochainComplex.IsKFlatIndependentCoefficients`, followed by the cascading missing
`CompletedConstantDerivedTower`. I retrieved the current module with
`scompile.py --source`, read its declarations and imports, and compared them with
`Sheaf.Algebra.Homology.KFlat` and
`Sheaf.Paper.CompletedAdicCoefficientDatum`. The current K-flat interface is
`CochainComplex.IsKFlat` with independent site/coefficient universes and the tensor
localization theorem is `isMonoidal_W_separateHomUniverse`.

This delivery needs none of that later realization theorem's quotient tensor tower.
Its import was only supplying abbreviations for the module category, scalar
extension and the constant-sheafification unit. Therefore the repair removes
`CompletedConstantFiniteComplexRealization` from the sibling's public imports and
imports `Sheaf.Paper.AdicLisseModule` directly. Both delivered files now use
Mathlib's `SheafOfModules.{u + 1} ((adicLisseForget T).obj R)` and the landed
`completedAdicChange T φ`. The latter unfolds to the same specified ordinary
scalar-extension witness as the former `completedConstantExtension`; its additive
instance is already landed. `tensorSection` uses `completedAdicChangeTensor`
directly. The two occurrences of the constant module generator are written as
the existing `toSheafify` unit on the constant abelian-group presheaf, exactly the
body of the old generator. No replacement tensor, K-flat predicate, arbitrary
comparison, or copied tower is introduced. The three reported identifiers are
no longer needed by this delivery's import closure.

The hypothesis/clause checklist in the worker report still applies with these
exact substitutions: module categories are written out using Mathlib, and all
ordinary/complex reduction maps use `completedAdicChange`. The base ring, canonical
algebra structure, flatness predicate, all positive exponents, every K-flat
resolution, bounded finite-projective representatives, finite retracts and the
finite-function coefficient comparisons are unchanged. The actual canonical
projection/multiplication and sheafification-unit formulas are retained.
The small site's object universe remains u+1 and its morphism universe u; no
additional smallness or ring hypothesis is added. The item node's mathematical
statement, statement dependencies and proof are unchanged. Its `lean.statement`
is refreshed verbatim from the repaired signature. The dependency node changes
only in `lean`, retaining its §1(B) explanation and imported completed-adic datum.

The earlier report's references to `completedConstantModules`,
`completedConstantExtension` and `completedConstantGenerator` describe the
previous spelling and are superseded by this repair. There is no new node or
statement correction. Checks still include n=0 (exponent one), the zero ring,
I=0, I=top, empty schemes, empty support intervals and rank-zero retracts.
The previous second reading is preserved as history; the second reader must
review these changes before delivery.

Final repair validation: `scompile.py Q32
lem-weil-pbc-completed-constant-sheaf-reduction` compiled both delivered modules
without errors or warnings. The final library checks took 7.2 seconds for
`AdicCoefficientDatum` and 23.7 seconds for `CompletedConstantSheafReduction`.
All lines are at most 100 characters, and both node copies differ from the
current shared nodes only in `lean`. The older dependency's newly added review
metadata was refreshed from the shared node rather than overwritten.

The first repair dry run compiled the packet and then found a truncated
`lean.statement`: extracting at the first `:=` had stopped inside `(R := ...)`.
The record now contains the entire theorem signature up to its final `:= by`,
including all derived-reduction and finite-projective-resolution clauses.
No Lean source change was needed for this metadata correction.

## Second reading by Q32

I reread the current item node, its Stacks source place (Modules on Sites,
Tags 093J and 093M), the dependency records and both delivered modules. The
node's objects and hypotheses match the Lean as follows.

1. The arbitrary scheme `T` and its small pro-etale site are rendered by
   `T : Scheme.{u}`, `T.ProEt`, `ProEt.topology T`, and the recorded
   `adicLisse*` declarations. The site objects have universe `u+1` and its
   morphisms have universe `u`; no extra site or nonemptiness hypothesis is
   present. PASS.
2. The coefficient data are the arbitrary `A : Type (u+1)` with
   `[CommRing A]`, `[IsNoetherianRing A]`, and arbitrary `I : Ideal A` in
   `completed_constant_sheaf_reduction`. No completeness, principality,
   regularity, characteristic, torsion, or finiteness assumption is added to
   the main clause. PASS.
3. The constant sheaves and completion are rendered by
   `adicLisseConstantRing`, `adicLisseConstantModules`,
   `adicLisseRingSystem`, and `adicLisseCompletedRing`; `base_exists` and
   `base` specify the unique map to the limit by every quotient projection,
   and `completedModule` is its canonical restricted unit module. This is the
   node's `B` with its canonical underline-`A` algebra structure. PASS.
4. Flatness is exactly the first conjunct
   `SheafOfModules.IsFlatOnSite (completedModule T I)`, whose definition is
   exactness of the sheaf tensor functor. PASS.
5. The node's positive exponent `a >= 1` is represented bijectively by
   `n : Nat` and `n+1` in `residue`, `reduction`, and every finite clause;
   `n = 0` therefore includes exponent one. PASS.
6. The ordinary canonical reduction is `reduction`, selected only after
   `reduction_exists` fixes its projection-and-multiplication formula on all
   site objects and constant generators. The second conjunct makes this
   specified map an isomorphism. PASS.
7. The derived reduction clause is rendered on every K-flat complex `P` and
   quasi-isomorphic augmentation `f` by
   `QuasiIso (reductionComplex T I n P f)`. `reductionComplex` is the recorded
   scalar extension, its degree-zero comparison, and the specified ordinary
   reduction, so this is the canonical representative of the node's derived
   map rather than an arbitrary isomorphism. PASS.
8. The bounded finite-projective hypothesis is rendered by an arbitrary
   complex `F`, augmentation `f`, `QuasiIso f`, termwise
   `Module.Finite` and `Module.Projective`, and explicit bounds `a b` with
   `IsZero` outside the interval. The conclusion gives the canonical
   reduction quasi-isomorphism, `IsFiniteRetract` into a finite coproduct of
   copies of the completed ring (including `Fin 0`), and the same bounds after
   extension. PASS.
9. Under exactly the extra hypothesis
   `hf : forall n, Finite (A ⧸ I ^ (n+1))`, the finite interpretation is
   rendered by `functionPresheaf`, `coefficientRing`, `ringSystem`,
   `completedRing`, and `finiteResidue`. `systemComparison` and
   `completedComparison` are the canonical constants-to-functions maps, and
   `finite_coefficient_identification` asserts their levelwise/limit
   isomorphisms, the specified finite reduction isomorphism, and its K-flat
   representative quasi-isomorphisms. This is precisely the node's
   identification with `(P_n)_T` and `A_T`. PASS.

The edge cases were checked directly against these binders and definitions:
`I = 0`, `I = top`, nilpotent and nonprincipal ideals, the zero ring, empty
schemes and empty site objects, zero complexes, empty support intervals,
rank-zero finite retracts, repeated quotient levels, and arbitrary
characteristic are all admitted. No index nonemptiness or hidden universe
equality is imposed.

For H4 I searched Mathlib, the upstream `WeilConjectures` tree, and the side
`Sheaf` tree with LeanFinder/Loogle/LeanSearch and direct `rg` queries for
completed constant sheaves, adic completion flatness, reduction, coefficient
comparison, normalization, and `IsFiniteRetract`. The only relevant Mathlib
hit was ordinary `AdicCompletion.flat_of_isNoetherian`; it does not state this
site-level theorem. LeanSearch was unavailable, and no exact declaration was
found. I also reread the delivered dependency module. Its prior duplicate
adic tower was removed and it now reuses the landed completed-adic datum while
providing only the generalized finite-function coefficient presentation needed
for arbitrary finite quotients; its node record carries the required H13 note.

No mismatch in the item's statement or Lean signature was found. The only
report defect was the missing required heading, which this section supplies.
The repaired dependency and primary modules were already compiled with
`scompile.py` without errors or warnings; no Lean source or node statement was
changed in this second reading.
