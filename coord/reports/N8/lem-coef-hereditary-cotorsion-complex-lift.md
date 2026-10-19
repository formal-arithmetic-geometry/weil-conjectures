## Worker report

The draft module `lean/Sheaf/Algebra/Homology/HereditaryCotorsionComplexLift.lean`
states `CategoryTheory.Cotorsion.hereditary_cotorsion_complex_lift`, with its sole proof
`sorry`. Its three genuine definitions `acyclicCycles`, `dgLeft`, and `dgRight` are
exactly the three classes expressly introduced in this node. They have full data and
are listed in `lean.declarations`; no independent DAG node is restated. The node copy
changes only `lean`, and its signature is copied verbatim from the module.

The file is NOT yet compiler-validated: the mandatory compiler wrapper fails before
reaching the submitted file, including on an import-free probe (details below).
No second reading or delivery has been performed.

### Hypothesis and clause correspondence

| Node text | Lean rendering |
| --- | --- |
| Grothendieck abelian category A | `{A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]`; this is the exact Mathlib match recorded by `def-sp-grothendieck-abelian`. |
| Object classes F and T | `(F T : ObjectProperty A)`. |
| F and T are each other's Ext-one orthogonals | `hpair : IsCotorsionPair F T`, the shared predicate; it unfolds to both orthogonal equivalences. |
| Ext means Yoneda, with Ext-one vanishing meaning split extensions | Shared `ExtOneOrthogonal` quantifies over every short exact extension and requires `IsSplitEpi` of its quotient. Higher degrees use `Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) U V n)`, the canonical derived model of Yoneda Ext; the DAG's comparison node is a proof dependency, not a hypothesis or prerequisite needed to form the statement. This is the same higher-Ext representation already used by `flat_cotorsion_foundation`. |
| Heredity in every degree at least one | `hhereditary : ∀ (n : ℕ), 1 ≤ n → ∀ U V : A, F U → T V → Subsingleton (...)`. There is no degree-zero vanishing assumption. |
| F contains the specified generator G | `(G : A) (hG : F G)`. |
| Every object is an epimorphic image of a small coproduct of copies of G | `hgen : ∀ X : A, ∃ (I : Type v) (p : (∐ fun _ : I ↦ G) ⟶ X), Epi p`. Small means the same `v` as the recorded Grothendieck-category convention; no projectivity of G is assumed. |
| A small set S contained in F | `{ι : Type v} (S : ι → A) (hS : ∀ s : ι, F (S s))`; repetitions in this enumerated family do not affect its orthogonal. |
| T = S-perp-one | `hT : ∀ V : A, T V ↔ ∀ s : ι, ExtOneOrthogonal (S s) V`. |
| Unbounded integer cochain complexes, d squared zero | `CochainComplex A ℤ`; the differential and square-zero law are the built-in data. No boundedness instance is required. |
| W consists of complexes with zero cohomology | `P.Acyclic` or `U.Acyclic`; Mathlib defines this as exactness in every degree, equivalent in this abelian category to zero homology in every degree. |
| Tilde-F and tilde-T are acyclic with cycles in F and T | `acyclicCycles F` and `acyclicCycles T`, defined by `P.Acyclic ∧ ∀ n : ℤ, F (P.cycles n)`. The cycles are Mathlib's actual kernel objects, not additional arbitrary objects. |
| Hom degree r is the product of Hom(P^n,T^(n+r)), with the prescribed sign | Mathlib's `CochainComplex.HomComplex P U`; its cochains are families on triples `p,q,p+r=q`, canonically the displayed product. Its `δ` at `m=r+1` uses `m.negOnePow`, giving precisely the negative of `(-1)^r` on the source-differential term. |
| dg-F: F terms and Hom into every tilde-T complex acyclic | `dgLeft F T`, defined by `(∀ n, F (P.X n)) ∧ ∀ U, acyclicCycles T U → (HomComplex P U).Acyclic`. |
| dg-T: T terms and Hom from every tilde-F complex acyclic | `dgRight F T`, defined by `(∀ n, T (U.X n)) ∧ ∀ P, acyclicCycles F P → (HomComplex P U).Acyclic`. |
| First induced cotorsion pair | Conclusion conjunct 1: `IsCotorsionPair (dgLeft F T) (acyclicCycles T)`. |
| Second induced cotorsion pair | Conclusion conjunct 2: `IsCotorsionPair (acyclicCycles F) (dgRight F T)`. |
| Both pairs hereditary in all positive Ext degrees | Conclusion conjuncts 3 and 4 quantify all `n ≥ 1`, with the respective left and right classes and `Subsingleton` of the standard Ext in the abelian category of complexes. |
| Left classes closed under kernels of epimorphisms between their objects | Conjuncts 5 and 6, with `Epi p`, test `dgLeft F T` and `acyclicCycles F` on both endpoints and on `kernel p`. |
| Right classes closed under cokernels of monomorphisms between their objects | Conjuncts 7 and 8, with `Mono i`, test `acyclicCycles T` and `dgRight F T` on both endpoints and on `cokernel i`. Closure is written explicitly, rather than copying the already existing closure-only `CoefficientFlatCotorsion.IsHereditary` definition from the downstream flat-complex theorem. |
| dg-F intersect W = tilde-F | Conjunct 9: `∀ P, (dgLeft F T P ∧ P.Acyclic) ↔ acyclicCycles F P`. Extensional class equality is expressed pointwise. |
| dg-T intersect W = tilde-T | Conjunct 10: the same equivalence for `dgRight F T` and `acyclicCycles T`. |
| Sphere S^n A is A in degree n and zero elsewhere | `(CochainComplex.singleFunctor A n).obj A`, Mathlib's single-degree complex. |
| Tilde-T is the Ext-one right orthogonal of all spheres on S union {G} | Final conjunct: membership in `acyclicCycles T` iff for every integer n the sphere on G is Ext-one orthogonal to U and every sphere on `S s` is Ext-one orthogonal to U. This is exactly the union, including the generator when S is empty. |
| No enough-projectives assumption; no second-pair set cogeneration assertion | The signature contains neither an enough-projectives instance nor a completeness/smallness/cogeneration conclusion for the second pair. |

### Reused declarations and imports

The single statement dependency `def-sp-grothendieck-abelian` is a Mathlib leaf:
`CategoryTheory.IsGrothendieckAbelian` in
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` (read its entire class
signature and docstring, including its relative size convention and colimit instance).

Shared splitting orthogonality and cotorsion pairs use
`CategoryTheory.Cotorsion.ExtOneOrthogonal` and `CategoryTheory.Cotorsion.IsCotorsionPair`
from `Sheaf.CategoryTheory.SmallCotorsionModelRecognition`. Both definitions were read
in full. Mathlib supplies `CochainComplex.HomComplex`, its `Cochain` and `δ`,
`HomologicalComplex.cycles` and `HomologicalComplex.Acyclic`,
`CochainComplex.singleFunctor`, `CategoryTheory.HasExt.standard`, and
`CategoryTheory.Abelian.Ext`. Their data and full signatures were read in source.

Every already stated proof dependency is imported non-publicly in its owning module:
`HomologicalComplex.isGrothendieckAbelian` (`Mathlib.Algebra.Homology.GrothendieckAbelian`),
`IsGrothendieckAbelian.enoughInjectives`
(`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`),
`Abelian.Ext.covariantSequence_exact` and `contravariantSequence_exact`
(`Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`),
`cotorsion_orthogonality_calculus` (`Sheaf.CategoryTheory.CotorsionOrthogonalityCalculus`),
`Cotorsion.complete_small_of_set_cogenerated`
(`Sheaf.CategoryTheory.GeneratingSetCotorsionSmallness`),
`DerivedCategory.instFullSingleFunctor` and `instFaithfulSingleFunctor`
(`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`), and
`ShortComplex.ShortExact.homology_exact₂` (`Mathlib.Algebra.Homology.HomologySequence`).
Their signatures/docstrings were read; the latter two Mathlib signatures were read with
surrounding variables and related sequence maps.

The following proof dependencies have no recorded declaration yet and are therefore
not imported or restated: `lem-coef-yoneda-derived-ext-comparison`,
`lem-coef-complex-ext-disk-sphere`, `lem-coef-acyclic-cycle-orthogonal-splitting`, and
`lem-coef-augmented-injective-cycle-test`. They remain named in the thirteen-step proof
docstring. None is a statement dependency of this item.

### Edge cases and source reading

Checked the zero category and zero complexes; the defining acyclicity conditions and
cycle conditions have their expected values. No nonzero-generator hypothesis is added,
so the zero generator in the zero category is allowed. Empty S is allowed (`ι` need
not be inhabited): then T is the full class and the final sphere test still retains G.
Empty coproduct index types are permitted, as required for the zero object. Integers
cover negative sphere degrees and fully unbounded complexes. Degree one is included;
degree zero is excluded from all hereditary vanishing conditions. The object universe u
and Hom universe v are independent; all coproduct/set sizes use the recorded
Grothendieck size v. The Hom complex consists of actual global Hom groups, not internal
sheaf Hom. Higher Ext groups are shrunk using the always available standard model,
without an extra `HasExt` assumption.

Read all thirteen node proof steps and the recorded master blueprint paragraph 2.
Also located and read the current snapshot's relocated unit in
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/`
`prop-coef-integral-exceptional-adjoint.md` and its separate `.proof.md`; the derived
coefficient-adjunction paragraph agrees. The precise abstract lifting statement and
agent-formulated proof are this DAG node's explicit expansion of that paragraph.
No statement correction or mathematical dispute was found.

### Searches

All service searches used the mandated `msearch.py N8` wrapper with this item id; raw
results are retained in `searches.jsonl` in this sandbox.

- LeanFinder: `Hereditary cotorsion pair lifts to unbounded cochain complexes dg flat dg cotorsion sphere cogeneration`. Eight hits: K-projective/K-injective predicates, CM5b factorization, and derived t-structure facts; no cotorsion lifting theorem or generic dg-cycle classes.
- Loogle: `CochainComplex, HomComplex, IsAcyclic, Ext`. Zero hits; service reported unknown identifier `HomComplex`.
- Mathlib grep: `cotorsion|dgCotorsion|dgFlat`. Zero hits.
- LeanSearch: `Hereditary cotorsion pairs on unbounded cochain complexes dg classes acyclic cycles`. Eight hits: acyclicity and K-projective/K-injective orthogonality; none states this theorem.
- `rg -n -i 'cotorsion|dgFlat|dgCotorsion'` in project Sheaf and upstream WeilConjectures: upstream has no match; Sheaf has shared splitting/cotorsion definitions and the downstream flat-sheaf-complex specialization, not the present general theorem.
- Blueprint-id search in upstream WeilConjectures: no match.
- Generic-name search `IsHereditaryPair|acyclicCycles|dgLeft|dgRight|hereditary_cotorsion_complex_lift` over Mathlib, upstream and project Sheaf: no match.
- Inspected DAG cotorsion/Hom-complex nodes and the existing flat-complex specialization before introducing the three classes owned by this node. No new independent definition node is needed.

### Compilation tool failure

The mandatory `scompile.py` initially failed before elaborating this module.
Local overlay and server confirmation both report:

```
WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.lean:119:18:
error: `AlgebraicGeometry.ProEt.overPullbackId` has already been declared
```

The submitted file has no pro-etale or K-flat import. Reading the wrapper implementation
shows that it unconditionally ensures every entry of `source-overrides.json` before
processing the submitted file's imports. That manifest contains `Sheaf.Algebra.Homology.KFlat`,
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, and the offending
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
Thus narrowing this file's imports cannot fix the reported collision. An import-free
probe containing only `module` and `#check Nat` was submitted through the same wrapper
to distinguish the tool's forced overlay failure from this statement's imports.
The import-free probe also failed with the identical duplicate, locally and on server
confirmation. The required delivery dry run was then invoked; compiler success is not claimed.
Only the sandbox has been edited; no live/shared source, tool or artifact was changed
by this worker, and no direct git/global build command was used.

The required `deliver2.py N8 lem-coef-hereditary-cotorsion-complex-lift --no-push`
finished with exit 1 and `COMPILE FAILED on the server, nothing pushed`, reproducing
the identical unconditional-overlay duplicate locally and in server confirmation.
The import-free probe and the actual delivery both fail before the item can be
elaborated; the failure is in the wrapper-selected overlay, not an import selected
by this delivery. No tool or live-source repair is authorized to this worker.

Static checks passed: the recorded signature is verbatim, only `lean` changed in the
node, there are no lines over 100 characters, all universes and variables are bound
with `autoImplicit false`, and there is precisely one theorem with `sorry`.

### Dispatcher retry, 2026-10-16 11:36 UTC

Re-read the current item and its sole statement dependency, the shared cotorsion
predicates, the Lean module, and the current stage-2 contract. The statement and
recorded dependency interface remain unchanged. Static validation again confirms
that only `lean` differs from the shared node, the recorded signature is verbatim,
all lines are at most 100 characters, and the sole theorem has proof `sorry`.
Repeated the Mathlib grep `cotorsion|dgCotorsion|dgFlat`: zero hits.

Retried the actual module with `scompile.py`, then the import-free `CompilerProbe.lean`
with the same wrapper. Both again fail locally and in server confirmation with the
identical duplicate `AlgebraicGeometry.ProEt.overPullbackId` at forced overlay
`UpperLowerStar/Defs.lean:119:18`. Read `nt_local_compile.py`: its manifest loop
calls `ensure(module)` for every source override before it visits any submitted
file's imports. The current manifest still forces this pro-etale module alongside
the two K-flat replacements. Thus an import change in this delivery cannot repair
this failure. No compiler/tool source or shared source was changed. The prescribed
delivery dry run was retried as well; its result is recorded below.

Retry searches additionally used LeanFinder with
`Hereditary cotorsion pair lifts to unbounded cochain complexes dg classes acyclic cycles sphere cogeneration`:
eight hits, consisting of K-injective/K-projective predicates and orthogonality,
CM5b, and derived t-structure results; none is this theorem. Loogle with
`"Ext", "CochainComplex"` returned twelve hits, all indexing and Hom-complex
extensionality facts, not a lifting theorem. Direct blueprint-id and exact-name
searches in upstream WeilConjectures, Mathlib and project Sheaf again found no
existing copy of the statement or the three owned class definitions.

The delivery dry-run retry waited for a shared worktree slot in
`sharedrepo.worktree` (its slot-acquisition sleep), before compilation or preflight.
It was interrupted after several minutes because the mandatory actual-file and
import-free compiler retries had already independently confirmed the unchanged
forced-overlay failure both locally and on the server. This retry did not print OK,
create a delivery commit, or push. The earlier attempt's completed dry run remains
the recorded `COMPILE FAILED` result above. The current tool blocker is still the
duplicate declaration in the mandatory source override; no compiler validation or
successful preflight is claimed.

### Repair validation (2026-10-16)

The forced pro-etale overlay was repaired in the validated maintenance checkout
`weil-newtargets-maint-NF-vector-purity-1792139145`: its finite-coefficient
`UpperLowerStar.Defs` is the compatibility re-export and does not redeclare the
ordinary pro-etale functors. I reran the prescribed `scompile.py` wrapper against
that checkout; the overlay, sandbox, and library compilation of this module all
completed without errors or warnings. The module itself has no pro-etale imports;
the earlier duplicate was an unconditional overlay preparation failure.

The required dry run was then run as
`deliver2.py N8 lem-coef-hereditary-cotorsion-complex-lift --no-push` with the same
validated checkout. It printed:

```
OK (dry run): the delivery commit compiles and passes the preflight except for the
second reading, which the second reader writes; nothing pushed.
```

Thus the earlier overlay failure is resolved by the prescribed source-interface
repair, and this delivery is ready for the independent second reading.

## Earlier second reading (a previous round; superseded)

Independent second reading, 2026-10-16. I opened the shared node, the sandbox node
and full Lean module together; read the sole statement dependency
`def-sp-grothendieck-abelian` and its exact Mathlib class; and opened the shared
cotorsion predicates rather than inferring their meaning from their names.
There is no repair note for this item, no `statement_change`, no new definition
node, and no dependency module in this delivery.

The source is an agent-formulated abstract tool, not a Stacks lemma. I read the
named master blueprint file, especially proof paragraph 2 (derived coefficient
adjunction), and independently checked the mathematical references:
[Recktenwald, Section 2.2](https://d-nb.info/1211326829/34), Definition 2.2.4,
Proposition 2.2.7, Lemmas 2.2.9--10 and Theorem 2.2.13, and
[Gillespie, Proposition 3.7 and Corollary 3.8](https://arxiv.org/html/math/0607769).
These sources support the exact-cycle/dg classes, both induced pairs and their
compatibility under the stated generator and set-cogeneration assumptions.
The generator spheres in Proposition 3.7 are essential and are retained. The
Grothendieck hypothesis supplies enough injectives; enough projectives is not
an implicit assumption to add. The source's chain grading is reindexed to the
node's cochain grading; all sphere degrees are quantified over integers.

My object/hypothesis/conclusion checklist, made directly from the node, is:

| Node object or clause | Exact Lean rendering and verdict |
| --- | --- |
| Grothendieck abelian category A | `{A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]`: exact at the dependency node's fixed size v. The class has AB5, a separator and inferred small colimits; no Noetherian, ring, field or projectivity assumption. |
| Two classes of objects F,T | `(F T : ObjectProperty A)`: arbitrary predicates on this same category, exact. |
| Both Ext-one orthogonal equalities | `hpair : IsCotorsionPair F T`: exact. I read both equivalences at SmallCotorsionModelRecognition.lean:74--77. |
| Yoneda Ext-one vanishing means every extension splits | `ExtOneOrthogonal U V` quantifies over E, the inclusion V → E, quotient E → U and every short-exactness proof, and concludes `IsSplitEpi p`: exact splitting condition, in the correct variable order. The same predicate serves both induced pairs and spheres. |
| All positive higher Ext groups vanish between F and T | `hhereditary`, all `n : ℕ` with `1 ≤ n`, all U,V satisfying F U,T V, and `Subsingleton (@Abelian.Ext ... (HasExt.standard _) U V n)`: exact derived representation of Yoneda Ext in an abelian category with enough injectives. The existing comparison proof dependency identifies the models; it adds no hypothesis. |
| A specified generator G belongs to F | `(G : A) (hG : F G)`: exact, not just existence of an unrelated generator. |
| Every object is a quotient of a small coproduct of G | `hgen : ∀ X, ∃ (I : Type v) (p : (∐ fun _ : I ↦ G) ⟶ X), Epi p`: exact. Neither the map nor index is fixed in advance. |
| A small set S contained in F | `{ι : Type v} (S : ι → A) (hS : ∀ s, F (S s))`: exact set presentation. An injectivity condition would be unnecessary; repetitions do not change its right orthogonal. |
| T is exactly S-perp-one | `hT : ∀ V, T V ↔ ∀ s, ExtOneOrthogonal (S s) V`: both directions, exact. |
| Unbounded integer cochain complexes and d squared zero | `CochainComplex A ℤ`: Mathlib's shape is `.up ℤ`, with the square-zero law in the complex data; no boundedness restriction. |
| W is zero cohomology | `P.Acyclic`: `∀ i, P.ExactAt i`. I read `exactAt_iff_isZero_homology` and `Acyclic` in ShortComplex/HomologicalComplex.lean:670--681; this is precisely zero cohomology here. |
| Tilde-F and tilde-T have cycles in their respective classes | `acyclicCycles F` and `acyclicCycles T`: each is acyclicity conjoined with its class on every `P.cycles n`, exact. The cycles are the actual kernel objects (`cyclesIsKernel`), not terms or homology objects. |
| Global Hom complex, product in each degree, prescribed sign | `CochainComplex.HomComplex P U`: I read `Triplet`, `Cochain`, `δ` and `HomComplex`. Triples p,q,p+r=q parametrize the displayed product. For target degree m=r+1, `m.negOnePow` gives minus (-1)^r on the source differential; composition order gives d_U h minus (-1)^r h d_P. Exact. |
| dg-F has F terms and Hom into all tilde-T acyclic | `dgLeft F T`: both conjuncts and all target test complexes are present, exact. |
| dg-T has T terms and Hom from all tilde-F acyclic | `dgRight F T`: both conjuncts and all source test complexes are present, exact. |
| First induced cotorsion pair | Conjunct 1, `IsCotorsionPair (dgLeft F T) (acyclicCycles T)`: exact. |
| Second induced cotorsion pair | Conjunct 2, `IsCotorsionPair (acyclicCycles F) (dgRight F T)`: exact. |
| First induced pair hereditary in all positive degrees | Conjunct 3, all n ≥ 1 and P,U in the first pair with standard Ext vanishing: exact. |
| Second induced pair hereditary in all positive degrees | Conjunct 4, all n ≥ 1 and P,U in the second pair with standard Ext vanishing: exact. |
| First left class closed under epi kernels | Conjunct 5, all p:P → Q, `Epi p`, both dgLeft memberships imply dgLeft of `kernel p`: exact. |
| Second left class closed under epi kernels | Conjunct 6, same test for `acyclicCycles F`: exact. |
| First right class closed under mono cokernels | Conjunct 7, all i:U → V, `Mono i`, both acyclicCycles T memberships imply that of `cokernel i`: exact. |
| Second right class closed under mono cokernels | Conjunct 8, same test for `dgRight F T`: exact. |
| dg-F intersect W equals tilde-F | Conjunct 9, pointwise iff `(dgLeft F T P ∧ P.Acyclic) ↔ acyclicCycles F P`: exact equality of classes. |
| dg-T intersect W equals tilde-T | Conjunct 10, corresponding pointwise iff for dgRight and acyclicCycles T: exact. |
| Sphere S^n A | `(CochainComplex.singleFunctor A n).obj ...`: I read its source definition and docstring; the object is in degree n and zero elsewhere, exact. |
| Tilde-T is right orthogonal of all spheres on S union {G} | Final conjunct, for each U, iff for every integer n both the G-sphere test and all S-sphere tests hold: exact union, with the correct Ext-one orientation. |
| No enough-projectives assumption or set-cogeneration assertion for second pair | Neither occurs in the binders or conclusion; exact scope. |

Edge cases checked independently: `ι` and every coproduct index may be empty;
the final conjunct still tests G even when S is empty. The zero category and zero
complex are included, and G is allowed to be zero when it generates that category.
No positivity/nonzero or inhabitedness instance was added. Integers include zero,
negative degrees and unbounded complexes. Heredity includes n=1 and excludes n=0,
where ordinary Hom need not vanish. No coefficient ring/characteristic or scheme
appears, so there is no characteristic or nonempty-scheme restriction. Object and
Hom universes u,v remain independent; all small sets and coproducts use the v of
the recorded Grothendieck convention. `HasExt.standard` is always available in
`max u v`, including for the category of complexes; it introduces no extra size
hypothesis or universe equality.

Independent duplicate searches (through `msearch.py N8` with this item id):

- LeanFinder, `cotorsion pair hereditary unbounded complexes exact cycles differential graded orthogonal`: eight hits, principally K-injective/K-projective orthogonality and exactness results; no general cotorsion lifting statement or these classes.
- Loogle, `CochainComplex, "Acyclic"`: five hits, acyclicity/truncation/opposite facts; none is this statement or its three class definitions.
- LeanSearch, `cotorsion hereditary pair cochain complexes cycle class and degreewise orthogonality`: eight hits, including the canonical Hom complex and cycles kernel theorem. These are reused, and K-injective/K-projective predicates are different special cases.
- Service grep, `cotorsion|dgLeft|dgRight|acyclicCycles`: zero Mathlib hits.
- Direct `rg -n -i 'cotorsion|dgleft|dgright|acycliccycles|dg.?flat|dg.?injective|hereditary_cotorsion_complex_lift'` over Mathlib, upstream WeilConjectures and project Sheaf: no general lifting theorem or duplicate of the three generic class definitions. I opened FlatComplexCotorsionPairs.lean: its flat-sheaf-specific classes are different notions; its generic `IsHereditary` contains only the closure clauses, which are written out here rather than defined again. Shared cotorsion/splitting predicates are imported unchanged. DAG searches likewise found no separate existing node owning the three classes introduced in this item's own statement. No extra definition node or dependency repair is needed.

H5/H6/H8/H9 checks: the three definitions contain real data, with no proof holes;
the sole theorem has exactly `by sorry`. All four declarations have source and
blueprint docstrings; the theorem docstring carries all thirteen node proof steps
and their named dependencies. All recorded proof-dependency modules currently
available are imported, with unavailable proof-only nodes left in the proof plan.
There are no unbound variables (`autoImplicit false`), file-local notation or
instances, duplicate declaration names, or lines over 100 characters.

Mismatches found: none. I have not rewritten correct Lean or changed the node.
A static comparison confirms that the sandbox node differs from the shared node
only in `lean`, and `lean.statement` is verbatim the theorem signature, from
`theorem` up to `:=`. The second reading adds this independent audit only.

Validation: the prescribed `scompile.py N8 lem-coef-hereditary-cotorsion-complex-lift`
compiled the single delivered module successfully, including the sandbox and
library passes, with no errors and no warnings. The default current overlay now
works without the earlier worker's maintenance-checkout override.

Second-reader delivery result: the prescribed `deliver2.py N8
lem-coef-hereditary-cotorsion-complex-lift --no-push` made no progress for more
than twenty minutes while acquiring a shared temporary-worktree slot. A read-only
`/proc/locks` inspection confirmed all 48 slots considered by this process were
occupied (71 worktree slots were occupied overall). The process remained in the
slot retry sleep and never reached worktree creation, compilation or preflight.
I stopped only my own pending dry-run process with SIGINT after confirming its
command line and sleep state. Its traceback confirms
`sharedrepo.py:85`, `if _SLOT is None: _t.sleep(3)`, called by
`deliver2.py:26`, `clone = sharedrepo.worktree(...)`.
No tool, shared source or live artifact was edited, no worktree/delivery commit was
created by this attempt, and nothing was pushed. The dry run did not print OK,
so the final delivery command was not run. This is a delivery capacity/tool
blocker; the module's independent clean `scompile.py` result and completed second
reading above stand. Retry the prescribed dry run and delivery when worktree
capacity is available.


## Retry verification, 2026-10-16

Reopened the full module and node and the sole statement dependency. There is no
maintenance repair note for this item. The dependency still binds exactly to
`CategoryTheory.IsGrothendieckAbelian.{v}`; its Mathlib class and the full shared
`Cotorsion.ExtOneOrthogonal` and `Cotorsion.IsCotorsionPair` definitions were read.
The latest main-20261015 blueprint unit and its separate proof were read; the
coefficient-adjunction paragraph is the source of this abstract auxiliary tool.
No mathematical or interface change was needed. The independent second reading
above is preserved; this retry does not claim to be another independent reader.

The prescribed default `scompile.py N8
lem-coef-hereditary-cotorsion-complex-lift` completed both sandbox and library
passes successfully (3.9 s and 3.0 s), with no errors or warnings. Static checks
confirm that only `lean` differs from the shared node, the recorded signature is
verbatim, the date is the current UTC date, no line exceeds 100 characters, and
exactly the intended theorem has a `sorry` proof. Every currently recorded
proof-dependency module is already imported; four proof-only prerequisites still
lack declarations and are not restated here.

Repeated the mandated searches: LeanFinder, `Hereditary cotorsion pairs lift to
unbounded cochain complexes with acyclic cycles and differential graded orthogonal
classes`, returned eight K-injective/K-projective, CM5b and t-structure hits,
none this theorem; Loogle, `CochainComplex, "Acyclic"`, returned five
acyclicity/truncation/opposite facts; service grep,
`cotorsion|dgLeft|dgRight|acyclicCycles`, returned zero hits. Direct searches in
Mathlib, the upstream project and project Sheaf still find no duplicate generic
lifting theorem or any duplicate of the three classes. The refreshed upstream
now has citation-only mentions of cotorsion-pair papers in SerpeCardinal and
SerpeGeneratingSet; these do not define the notions or state this lifting theorem.
The source of HomComplex, its signed differential, cycles, acyclicity, and the
standard Ext representation was rechecked.

The prescribed dry run was retried. Several silent attempts were inspected and
only this item's retry processes were stopped; no other group's processes were
touched. One attempt using the wrapper's exposed `SHAREDREPO_WT_SLOTS=100`
configuration passed compilation and reached the per-group delivery lock, held
by another active N8 delivery. That attempt was stopped without a delivery
result; the final retry uses the unmodified default configuration. All retry
output is retained under scratch when available. No tool source, shared source,
Lean live artifact, or direct Git command was changed or run by this worker.


Final retry result (2026-10-16 12:44 UTC): the default dry run spent five more
minutes entirely in the slot-allocation sleep; all 48 default worktree slots
were occupied by other delivery wrappers. Read-only `/proc/locks` inspection
confirmed that the default pool was full. The process had no worktree and had
not reached preflight. Only this item's pending retry was stopped with SIGINT.
Its captured traceback again identifies `sharedrepo.py:85`,
`if _SLOT is None: _t.sleep(3)`, called from `deliver2.py:26`,
`clone = sharedrepo.worktree("weil-newtargets")`. The traceback is retained in
`scratch/dry-run-current.log`. No retry printed OK, and nothing was pushed.
The module remains cleanly compiled and the independent second reading complete;
the remaining blocker is delivery-tool capacity before any statement check.

## Second reading by N8

Independent fresh reading, 2026-10-16 12:54 UTC. I opened the node, the entire
Lean module, the Grothendieck dependency node and its Mathlib declaration,
the shared splitting/cotorsion predicates, and the master blueprint source
(and the relocated main-20261015 statement and proof). No repair note exists.
The abstract tool has no Stacks source tag. I also checked the cited literature:
[Recktenwald, Section 2.2](https://d-nb.info/1211326829/34), especially
Definition 2.2.4 and Theorem 2.2.13, and
[Gillespie, Proposition 3.7](https://arxiv.org/html/math/0607769).
The sources' exact-cycle and dg conditions agree with the node; requiring Hom
acyclicity is equivalent to null homotopy of every test map because the test
classes are closed under every integer shift. The generator and set hypotheses
supply the requisite quotient condition; Grothendieck supplies enough injectives.
No enough-projectives hypothesis is needed. The sphere set includes G.

The checklist below was made from the node, then matched against the file.
Every row has verdict **exact**.

| Node object, hypothesis or conclusion | Lean rendering |
| --- | --- |
| Grothendieck abelian A | `{A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]`; same size convention as def-sp-grothendieck-abelian. |
| Classes F and T of objects of A | `(F T : ObjectProperty A)`. |
| Each class is the other's Ext-one orthogonal | `hpair : IsCotorsionPair F T`; both equivalences are in the shared definition. |
| Ext-one vanishing means every short exact extension splits | Shared `ExtOneOrthogonal U V` tests every E, inclusion V to E, quotient E to U and short-exactness proof, concluding `IsSplitEpi p`. |
| Higher heredity for every positive degree | `hhereditary`, all `n : ℕ`, `1 ≤ n`, U,V with F U and T V, then `Subsingleton (@Abelian.Ext ... (HasExt.standard _) U V n)`. This is the derived model of Yoneda Ext, without an additional smallness instance. |
| Generator G belongs to F | `(G : A) (hG : F G)`. |
| Every object is a quotient of a small coproduct of G | `hgen`, all X, existential `I : Type v` and `p : (∐ fun _ : I ↦ G) ⟶ X` with `Epi p`. |
| Small set S contained in F | `{ι : Type v} (S : ι → A) (hS : ∀ s, F (S s))`; repetitions do not change the class or its orthogonal. |
| T equals the right orthogonal of S | `hT : ∀ V, T V ↔ ∀ s, ExtOneOrthogonal (S s) V`. |
| Integer-indexed unbounded cochain complexes with square-zero differentials | `CochainComplex A ℤ`, with no boundedness instance. |
| W is zero cohomology | `P.Acyclic`; Mathlib's exactness in every degree is equivalent to zero homology. |
| Both tilde classes are acyclic with the specified cycles | `acyclicCycles F` and `acyclicCycles T`, each `P.Acyclic ∧ ∀ n, ... (P.cycles n)`. Mathlib supplies the genuine kernel objects. |
| Product global Hom complex and signed differential | `CochainComplex.HomComplex P U`; `Triplet r` records p,q,p+r=q, and `δ r (r+1)` has coefficient `(-1)^(r+1)` on source differential composition. |
| dg-F has F terms and Hom acyclic into every tilde-T | Definition `dgLeft F T`, both conjuncts and all test U. |
| dg-T has T terms and Hom acyclic from every tilde-F | Definition `dgRight F T`, both conjuncts and all test P. |
| First and second induced cotorsion pairs | Conclusion conjuncts 1 and 2: `IsCotorsionPair (dgLeft F T) (acyclicCycles T)` and `IsCotorsionPair (acyclicCycles F) (dgRight F T)`. |
| Positive-degree Ext vanishing for each induced pair | Conjuncts 3 and 4 quantify all n at least one and every member of each pair in the category of complexes. |
| Both left classes closed under kernels of epis between members | Conjuncts 5 and 6 quantify p, `Epi p`, membership of both endpoints, and membership of `kernel p`. |
| Both right classes closed under cokernels of monos between members | Conjuncts 7 and 8 quantify i, `Mono i`, membership of both endpoints, and membership of `cokernel i`. |
| dg-F intersect W equals tilde-F | Conjunct 9, the pointwise iff `(dgLeft F T P ∧ P.Acyclic) ↔ acyclicCycles F P`. |
| dg-T intersect W equals tilde-T | Conjunct 10, the analogous pointwise iff. |
| Sphere is A in degree n and zero elsewhere | `(CochainComplex.singleFunctor A n).obj ...`. |
| Tilde-T is the right orthogonal of spheres on S union G | Final conjunct, all U, iff for every integer n both the G-sphere test and every S-sphere test hold. |
| No projectives assumption or second-pair set-cogeneration conclusion | Neither appears in the signature. |

I read the source definitions of `HomComplex.Cochain`, `HomComplex.δ`,
`HomComplex`, `cyclesIsKernel`, `Acyclic`, `exactAt_iff_isZero_homology`,
`HasExt.standard`, and `Abelian.Ext`; thus the sign, actual kernel objects,
zero-cohomology condition, and Ext universes are checked beyond their names.
I rechecked the currently recorded proof dependencies and their available
signatures: all eight available module imports are present. The four unrecorded
proof-only prerequisites remain in the thirteen-step docstring and are not
required to type this statement. There are no new or repaired dependency nodes,
and no statement_change to audit.

Edge cases: empty S is admitted and leaves the generator-sphere test intact;
empty coproducts and zero complexes are admitted; G may be zero in the zero
category. All sphere degrees, including zero and negative degrees, are covered.
Hereditary Ext assumptions and conclusions include n=1 and exclude n=0. No ring,
field, characteristic, scheme, or nonemptiness hypothesis is introduced.
Independent object universe u and Hom universe v remain independent; small sets
and coproducts use v, exactly as the recorded Grothendieck category does.
`HasExt.standard` uses the always available max-universe representation and
adds no hypothesis.

Fresh searches through `msearch.py N8` for this item:

- LeanFinder: `Ext orthogonality of acyclic cycle complexes and differential graded classes in a Grothendieck category`: eight hits, consisting of K-injective/K-projective orthogonality and generic Ext APIs; no generic cotorsion lift or these cycle/dg classes.
- Loogle: `"HomComplex", "Acyclic"`: zero hits.
- LeanSearch: `Exact cycle classes and induced hereditary cotorsion pairs on unbounded complexes`: eight exactness/cycles APIs, not this theorem.
- Direct rg over Mathlib, upstream WeilConjectures and project Sheaf with `cotorsion|dgleft|dgright|acycliccycles|dg.?projective|dg.?injective`: shared splitting predicates and flat-sheaf-specific classes only; upstream cotorsion mentions are bibliography. Opened FlatComplexCotorsionPairs to verify its specialized notions are not the generic classes here. No match in dag/lean_names_upstream.json. No separate DAG definition node owns these three classes introduced by this node itself.

Mismatches found: none. No Lean or node change was made. The three definitions
have genuine data; exactly one theorem has `by sorry`. Module and declaration
docstrings name source places and the blueprint id, and the theorem docstring
carries all thirteen proof steps. No file-local notation or instances are used.
Static comparison confirms the node differs from the base only in `lean`, its
recorded statement is verbatim, every Lean line is at most 100 characters, and
`autoImplicit false` plus successful elaboration leaves no unbound variables.

Fresh mandatory `scompile.py` validation passed the sandbox (3.0 s) and library
(2.8 s) passes with no errors or warnings. Delivery dry-run outcome is recorded
below when the current pending wrapper completes; earlier capacity failures are
historical and are not compilation failures of this module.

Current second-reader delivery validation: the unmodified prescribed
`deliver2.py N8 lem-coef-hereditary-cotorsion-complex-lift --no-push`
completed successfully and printed `OK (dry run): commit dbfd669fd4 passes the
preflight and compiles; nothing pushed`. The temporary-worktree capacity and
fetch-lock waits cleared without any tool or shared-source modification.
