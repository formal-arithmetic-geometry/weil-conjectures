## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace` states
`DerivedCategory.chain_supertrace`. Its sole theorem has proof `sorry`.
The six auxiliary definitions have real data: the degree-zero unit coordinate,
a frame functional embedded in the recorded total Hom, its total-tensor summand,
the ordinary frame trace, the finite alternating sum, and the canonical derived
unit comparison. They belong to the explicit construction asserted by this node;
there is no new independent notion, new node, dependency repair, or statement change.
Every helper and the theorem is recorded in `lean.declarations`.

Hypotheses and conventions:

- The commutative ring is `{A : Type u} [CommRing A]`, with no nontriviality,
  freeness, field, Noetherian, or constant-rank assumption.
- `P : CochainComplex (ModuleCat.{u} A) ℤ` has the actual complex differentials
  and square-zero identities, and `v : P ⟶ P` is an actual degree-zero chain map.
  The theorem quantifies over every such `v` in the relevant clauses.
- `[P.IsStrictlyGE a] [P.IsStrictlyLE b]` express boundedness on any supporting
  integer interval. There is no assumption `a ≤ b`. `hfinite` and `hprojective`
  assert exactly finite generation and projectivity of every term, using the
  two recorded Mathlib predicates.
- Tensor, associator, left unitor, and right unitor are the existing total-complex
  monoidal structure. `CochainComplex.Monoidal.braiding` is the existing Koszul
  symmetry. Its source says its summand sign is `(-1)^(p*q)`, and the tensor is
  the recorded `CochainComplex.mapBifunctor` for `curriedTensor`, with second
  differential sign `(-1)^p`.
- `perfectTraceModelDual P` is reused, not reconstructed. It is exactly
  `CochainComplex.moduleHomComplex P A[0]`, with differential `d_M z - (-1)^j z d_P`.
  Its degree `j` cochains have only the component from `P^(-j)` into `A` nonzero,
  so this is the canonical total-Hom encoding of the displayed dual. The dual
  differential consequently has sign `(-1)^(j+1)`. The existing cochain `single`
  embeds a frame functional in degree `-i`, zero in all other components.
- `ModuleCat.StrictPerfectCoefficientPackage P`, already used and imported by
  `def-trf-categorical-trace`, encodes exactly a finite dual frame: `p` supplies
  its columns, `i` its coordinate functionals, and `i ≫ p = 1` is the frame identity.
  Conversely any frame gives those two maps, so packages impose no extra restriction.
  The first conclusion supplies such a package with `N i = 0` on zero terms.
- `[HasDerivedCategory.{u} (ModuleCat.{u} A)]` uses the same chosen localization
  universe as the recorded categorical trace interface. All variables and universes
  are explicitly declared; no file-local instance or notation changes a statement.

Clause-by-clause conclusion:

- (a), evaluation: `ev : perfectTraceModelDual P ⊗ P ⟶ 𝟙_ _` is a chain map.
  Its first conjunct evaluates every pure tensor in degrees `(-i,i)` by applying
  the cochain component to the vector. `chainTraceUnitCoordinate` explicitly
  identifies its value with `A`. The second conjunct says `ev.f n = 0` for `n ≠ 0`.
- (a), coevaluation: `coev : 𝟙_ _ ⟶ P ⊗ perfectTraceModelDual P` is a chain map.
  Its value at one is the sum over `Finset.Icc a b` of the existing frame vectors
  tensored with their functionals in degree `-i`, through the canonical summand
  injection. This assertion holds for EVERY package with empty frames on zero
  terms, using the SAME `coev`; it is precisely frame independence. Evaluation
  has no frame input. The displayed pure-tensor and unit formulas determine the
  maps, rather than leaving arbitrary morphisms as hypotheses.
- (b): the next two conjuncts are the two triangle composites on the dual and on
  `P`, respectively, with `ρ`, `λ`, and `α` inserted in their typed order.
- (c): for every frame package and chain endomorphism the literal composite
  `coev ≫ v ▷ dual ≫ braiding.hom ≫ ev` equals the degree-zero single-complex
  image of multiplication by `chainSupertrace s a b v`. This is the composite
  of `CategoryTheory.MonoidalCategory.trace` with the asserted right duality.
- Ordinary projective trace: `chainTraceTerm s i t` is exactly
  `∑ r, ε_r (t e_r)` with no basis assumption. The following quantified conjunct
  says it is independent of the package. The basis clause gives the diagonal
  sum `∑ r, e.repr (v (e r)) r`, agrees with `LinearMap.trace` in this free case,
  and gives `(n : A)` for the identity in rank `n`. Any finite projective module
  can occur as a term of a single complex, so this also covers the node's
  ordinary-module trace convention.
- Euler scalar: `perfectCategoricalTrace (Q.obj P) hP (𝟙 _)` equals the alternating
  sum of `chainTraceTerm s i (𝟙 _)`. These terms ARE the rank scalars defined in
  the node. No integer rank is assigned to a nonfree projective.
- Homotopy invariance: `Nonempty (Homotopy v w)` implies equality of the two
  finite alternating sums, for all chain maps `v,w` and every frame package.
- Derived maps: the theorem supplies `hP : IsPerfectRingComplex (Q.obj P)` and
  proves K-flatness of `P` as a conclusion, rather than assuming it. The dual
  comparison `δ` identifies the total-Hom model with the EXISTING derived internal
  dual, and both evaluation and coevaluation are identified with their recorded
  canonical maps using `QObjTensorQObjIsoOfKFlatRight/Left` and `chainTraceUnitIso`.
  Thus the comparison cannot select an unrelated duality datum.
- Derived scalar: `perfectCategoricalTrace (Q.obj P) hP (Q.map v)` is the same
  alternating sum. For EVERY derived endomorphism another conjunct supplies a
  chain representative and the same formula. Consequently the existing function
  on all derived endomorphisms is the required descended function, with scalar
  identification by the inverse fully faithful single-functor Hom map at one.
- Representative invariance and transport: for EVERY perfect `T` and EVERY
  isomorphism `e : Q.obj P ≅ T`, the final conjunct explicitly transports
  coevaluation by `e.hom ⊗ dualMap e.inv`, evaluation by `dualMap e.hom ⊗ e.inv`,
  and proves trace invariance under `e.inv ≫ v ≫ e.hom`. This includes identity
  changes of representative and arbitrary representative isomorphisms.
- Finite coefficients: `WeilConjectures.finiteCoefficientCategoricalTrace` is
  definitionally `perfectCategoricalTrace` at `A = coefficientExtensionRing ...`.
  Hence specializing the already quantified ring gives exactly that function,
  its scalar identification and, by the two transport equalities, its transported
  duality maps. No replacement trace function is introduced.

Dependency declarations read and reused:

- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `singleFunctorIsoCompQ`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  as used by `HomologicalComplex.tensorObj` / `ιTensorObj`.
- `Sheaf.Algebra.Homology.ModuleHomComplex`: `CochainComplex.moduleHomComplex`.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`:
  `CategoryTheory.MonoidalCategory.trace` and its defining composite.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace`: the model dual,
  frame vector and functional, derived dual and its map, evaluation, coevaluation,
  unit scalar identification, `perfectCategoricalTrace`, and its exact finite
  coefficient specialization. This public import supplies the statement interfaces.
- Proof dependencies already supplied by the public trace import include
  `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat` (BoundedFlatKFlat),
  `Module.Flat.of_projective` (Mathlib Flat.Basic), the fully faithful single
  functor (Mathlib DerivedCategory.FullyFaithful), and
  `CochainComplex.IsKProjective.Qh_map_bijective` (Mathlib DerivedCategory.KProjective).
  `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor` is additionally imported
  nonpublicly for `exists_derivedTensor_second_factor_functor`, as the proof plan requires.
- Further existing infrastructure is `CochainComplex.HomComplex.Cochain.single`,
  `HomologicalComplex.singleObjXSelf`, the upstream Koszul complex braiding, and
  `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft/Right` and `singleFunctorObjUnitIso`
  from upstream DerivedCategory.FlatModel. No declaration duplicates these.

Edge cases checked before/following drafting: the zero ring is allowed; zero
complexes and empty supporting intervals give empty sums; an isolated degree-zero
term gives the ordinary frame trace; an isolated term in either degree 1 or -1
gives its negative, using integer `negOnePow`; the contractible identity complex
has cancelling adjacent traces; characteristic two identifies the two signs
without changing the formula. For `A = k × k`, `M = k × 0`, the identity frame trace
is `(1,0)`, not an assumed integer multiple of one; the statement preserves this
case. Empty frames on zero terms are asserted to exist and used in the coevaluation
formula. Identity representative changes and arbitrary derived endomorphisms
are retained. There is no remaining STATEMENT-DISPUTED issue: the stage-1 record's
historical issue with bases was already corrected to dual frames in the node.

Searches made for this delivery (2026-10-17; machine output also in searches.jsonl):

- `msearch.py` LeanFinder, "The categorical trace of an endomorphism of a bounded
  complex of finite projective modules is the alternating sum of its projective
  module traces": eight hits, all ordinary module trace results, including
  `LinearMap.IsProj.trace`, `trace_comp_cycle`, `trace_comp_comm`, `trace_id`,
  `trace_eq_contract`. None states this complex/derived theorem. These ordinary
  Mathlib trace results need finite free modules and cannot replace the frame trace.
- `msearch.py` Loogle, `"trace", "HomologicalComplex"`: zero hits.
- `msearch.py` LeanSearch, "supertrace of a bounded projective cochain complex
  invariant under homotopy": eight homotopy infrastructure hits, notably
  `δ_ofHomotopy`, `Cochain.ofHomotopy`, and `HomotopyEquiv.isKProjective`; no trace theorem.
- `msearch.py` grep, `supertrace|superTrace|trace.*homotop|trace.*cochain|trace.*projective`
  in Mathlib/LinearAlgebra: zero hits.
- `rg` with `supertrace|superTrace|chain-supertrace|categoricalTrace` in the named
  upstream WeilConjectures tree, shared `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  only the recorded PerfectCategoricalTrace module's explanatory supertrace mention;
  no theorem for the item. Subsequent candidate-name searches `chainTrace|chain_supertrace`
  in upstream, shared Sheaf, upstream names, and Mathlib homology/linear algebra found none.
  The upstream monoidal search did find the canonical Koszul braiding and the K-flat
  tensor comparisons, which were read and used.

Validation: scompile.py compiled the sandbox and the library-shaped file cleanly
in successive runs, each about five seconds, with no warnings or errors. The
delivery dry run printed `OK (dry run): commit 435a556d09 compiles and passes
the preflight except for the second reading, which the second reader writes;
nothing pushed.` The independent second reading remains with the designated
second worker; no second-reading section was written here. No global build or
direct git command was run, and only the authorized sandbox was written.

## Second reading by Q61

The node introduces a commutative ring `A`; a bounded cochain complex `P` of finitely
generated projective `A`-modules; bounds `a,b`; a degree-zero chain endomorphism `v`;
the total tensor, Koszul braiding, unit, dual total Hom, evaluation, coevaluation,
finite dual frames, and ordinary projective traces; and the derived category object
`Q(P)`. Its conclusions were checked in order:

1. `chain_supertrace` takes `A`, `P`, `a`, `b`, the strict boundedness instances,
   `hfinite`, and `hprojective`; these render exactly the ring, boundedness, finite
   generation, projectivity, and chain-map hypotheses. `chainTraceUnitCoordinate`,
   `perfectTraceModelDual`, `chainTraceFrameDual`, and `chainTraceFrameTensor` render
   the unit, total Hom dual, degree `-i` functionals, and frame tensors. The first
   existential supplies a package with empty frames on zero terms.
2. The evaluation conjunct gives the displayed homogeneous evaluation and the next
   conjunct gives zero in every nonzero total degree. The coevaluation conjunct gives
   the finite frame sum over `Finset.Icc a b`; boundedness makes this equal to the
   all-degree sum in the node, and its quantifier is restricted exactly to the stated
   empty-frame convention. The next two conjuncts are the two triangle identities
   with canonical associators and unitors inserted, which is the typed rendering of
   the source's suppressed strict coherence maps.
3. The trace conjunct is precisely `coev ≫ (v ▷ dual) ≫ braiding.hom ≫ ev` and equals
   `chainSupertrace`; `chainTraceTerm` is the finite dual-frame projective trace, with
   the basis and `LinearMap.trace` clauses and the identity rank scalar. The Euler
   scalar conjunct, homotopy-invariance conjunct, and the derived representative
   conjuncts render the corresponding clauses of (c) and the derived paragraph.
4. The `hflat`/`δ` conjunct identifies the explicit model maps with the canonical
   derived evaluation and coevaluation; the next conjunct identifies the canonical
   derived trace with the alternating sum, and the representative clause supplies a
   chain representative for every derived endomorphism. The final conjunct transports
   both duality maps and the trace across every perfect representative isomorphism.
   `finiteCoefficientCategoricalTrace` is the recorded specialization used by the
   final node clause. No hypothesis is added beyond the node's bounded model and the
   chosen derived-category localization interface, and no conclusion is weakened.

Edge cases checked: zero ring; zero complex; empty support interval; `a>b` for the
zero complex; an isolated degree-zero term; isolated degrees `1` and `-1`; a
contractible adjacent-pair complex; characteristic two; a nonfree projective summand
`k × 0` over `k × k`; empty frames on zero terms; identity representative changes;
and arbitrary derived endomorphisms. All are covered by the explicit finite sums and
the `negOnePow` convention.

Searches were repeated with `msearch.py` LeanFinder/Loogle/LeanSearch and `rg` over
the named Mathlib, `WeilConjectures`, and project `lean/Sheaf` trees for
`supertrace`, `chainSupertrace`, `chain_supertrace`, and categorical trace names.
The existing upstream `CochainComplex.trace_f_zero` and homotopy lemmas cover only
termwise right-dual/free cases; no declaration states this finite-projective,
frame-based derived theorem. The dependency declarations and the source proof were
read, including `PerfectCategoricalTrace`, `ModuleHomComplex`, the total tensor, and
the derived-category predicate.

No mismatch was found, so no Lean or node statement was changed. The sandbox module
recompiled cleanly with `scompile.py` and retains only the named theorem's `sorry`.
