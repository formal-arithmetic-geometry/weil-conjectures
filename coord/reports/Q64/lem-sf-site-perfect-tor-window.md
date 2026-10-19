## Worker report

The module `Sheaf.Algebra.Homology.SitePerfectTorWindow` states
`SheafOfModules.exists_strictPerfect_model_in_tor_window`. Its only theorem proof is
`sorry`, as required in stage 2. No definitions, instances, auxiliary theorems, dependency
repairs, or new DAG nodes are introduced. The natural-language proof in the docstring
includes all eight steps of the DAG proof.

Clause-by-clause correspondence:

- A ringed site small in the chosen universe: `{C : Type u} [Category.{v} C]` and
  `J : GrothendieckTopology C`. Object and morphism universes remain independent.
  Coefficients and module sections use the common chosen bound `max u v`, exactly
  the recorded tensor-descent interface. No `SmallCategory C` assumption is made.
- Commutative coefficient ring sheaf: `R : Sheaf J CommRingCat.{max u v}`.
  The expression `(sheafCompose J (forget₂ CommRingCat RingCat)).obj R`
  is its underlying ring sheaf, as in the dependency declarations.
- Module sheaves: Mathlib `SheafOfModules` (the transparent category reexported
  as `CategoryTheory.ringedSiteModules`), never a replacement category.
- Unbounded derived categories: `HasDerivedCategory.{w}` on the original site and
  `HasDerivedCategory.{w'}` on every slice, and `E : DerivedCategory …`.
  The global and slice localization morphism universes are independent.
  The `HasSheafify` and `WEqualsLocallyBijective` binders, globally and on slices,
  expose the standard abelian-sheaf infrastructure relative to the chosen bound;
  these are the hypotheses of the recorded perfectness/restriction interfaces.
- E is locally perfect: `_hperfect : IsPerfectOnRingedSiteOfUniverses.{u,v,0} R E`.
  This recorded predicate chooses a representative with, over every object,
  covering-sieve quasi-isomorphisms from bounded finite-free-retract complexes.
  The degree bounds and ranks vary with the cover member, as the node permits.
  The final universe parameter `0` contributes nothing to `max u v 0`.
- Integers a ≤ b: `(a b : ℤ) (_hab : a ≤ b)`.
- Every degree-zero test module F: `_hTor` quantifies over all `F : SheafOfModules …`,
  and uses `(DerivedCategory.singleFunctor _ 0).obj F`.
- K-flat derived tensor: `(wfSiteDerivedTensor J R).obj` is the existing canonical
  construction from `Sheaf.Paper.WeilTensorProduct`, recorded among the declarations
  of `def-wf-tensor-product`. Its definition selects precisely the tensor clause of
  `wf_site_derived_tensor_descent J R`, including its natural total-tensor comparison.
  It unfolds to the former inline choice expression with the same universe arguments.
  The descent comparison fixes the tensor up to its unique compatible isomorphism.
  The existing node is added to `stmt_deps`; no new notion or declaration is introduced.
- All cohomology outside [a,b] vanishes: `_hTor` quantifies `r : ℤ`, with premise
  `r < a ∨ b < r`, and concludes `IsZero ((DerivedCategory.homologyFunctor _ r).obj …)`.
  This is vanishing in the module-sheaf category, not vanishing of global sections.
- For every U, a covering: `∀ U : C, ∃ S : Sieve U, S ∈ J U ∧ …`.
  A covering sieve is the intrinsic Grothendieck-topology encoding of a covering
  family; its arrows index a covering family and cover every domain required below.
- Each member V → U carries a model: `∀ (V : C) (f : V ⟶ U), S f → ∃ P : …`.
- Localization and restriction E|V: the already landed
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses` applied to the underlying
  ring sheaf, V, E. It restricts the canonical representative and localizes, on the
  actual slice site `J.over V`, without assuming the existence of points.
- A bounded cochain complex P with finite free retract terms and a derived isomorphism:
  `StrictPerfectCoefficientRepresentationOfUniverses R V (… E)` has fields `F`,
  `bounded`, `represents`, `package`. The last field is exactly the recorded
  `StrictPerfectCoefficientPackageOnSite`, with finite ranks, inclusion/retraction
  sheaf maps, and `i r ≫ p r = 𝟙 _` in each degree. These are degreewise splittings;
  no chain-map splittings or globally projective sheaves are assumed.
- Terms zero outside the prescribed interval: `∀ r : ℤ, r < a ∨ b < r → IsZero (P.F.X r)`.
  The package's existential boundedness is redundant once this window is given,
  and carries no additional mathematical requirement.

Dependencies read and reused:

- `def-weil-size-convention`: the recorded metatheoretic convention, rendered as
  explicit universe levels and sheafification/localization infrastructure.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules` = Mathlib `SheafOfModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `def-pur-localized-ringed-site`: Mathlib
  `Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, `SheafOfModules.over`,
  `overFunctor`, `overMap`; the ring restriction is `Sheaf.over`, topology `J.over`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlat`,
  `CochainComplex.IsKFlatIndependentCoefficients`; reused transitively through the
  recorded tensor-descent theorem, which has the specialized `IsKFlat` interface.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`,
  `CochainComplex.mapBifunctor`, appearing in the descent comparison.
- `lem-weil-pbc-site-derived-tensor-descent`:
  `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`,
  `SheafOfModules.wf_site_derived_tensor_descent` (also read using `scompile.py --source`).
- `def-weil-pbc-strict-perfect-coefficient-package`:
  `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`,
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`,
  `StrictPerfectCoefficientRepresentationOfUniverses`, and the imported
  `StrictPerfectCoefficientPackageOnSite`.
- `def-pc-cochain-complex-modules`: Mathlib
  `Algebra.Homology.HomologicalComplex`, `CochainComplex … ℤ`.
- `def-weil-derived-cohomology-sheaves`: Mathlib
  `Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`.
- Added the already landed `def-weil-pbc-ringed-site-derived-restriction` to
  `stmt_deps`, as permitted for landed notions: its actual recorded module is
  `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses` and its declaration
  is `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`. This supplies the
  exact canonical derived restriction used in the conclusion; its full source was read.

Every proof dependency with a recorded module is imported without `public`, except
modules already publicly required by the statement. The two proof dependencies with
no Lean declaration yet (`lem-sf-site-tor-interval-restriction` and
`lem-sf-site-flat-fp-finite-retract`) are not imported or restated. They are not
statement prerequisites. Mathlib leaves for slice restriction and locally surjective
sheaf epimorphisms need no newly written module.

Sources and edge cases:

Read Stacks `sites-cohomology.tex`, `lemma-perfect-precise` (08G7), including the
final displayed model in degrees a through b, and `lemma-tor-amplitude-pullback`
(08H5). The DAG's expanded proof supplies the upper shortening left implicit in
that display. No source correction or STATEMENT-DISPUTED issue was found.
For a = b, the conclusion permits a single nonzero term. For E = 0 or the zero
coefficient ring, zero terms and rank zero are allowed. Empty sites and empty
covering sieves are permitted: there is no `Nonempty` binder on sites, covers,
or test sheaves. A nonempty interval need not have nonzero terms. No stalk,
enough-points, constant-coefficient, finite-type, Noetherian, or connectedness
hypothesis has been added. All universes and variables are explicitly bound.

Searches (2026-10-16):

- `msearch.py leanfinder`: "A perfect complex on a ringed site with Tor amplitude in
  an interval has local finite projective models in that interval". Eight hits:
  cohomological bounded representatives, K-projective complexes, projective
  dimensions and Tor for projective objects. No finite-free-retract local-window theorem.
- `msearch.py loogle`: `"Perfect", "Projective"`. Zero hits.
- `msearch.py grep`: `tor.amplitude|strictlyPerfect|perfect.*complex`. Zero hits.
- `msearch.py leansearch`: "A perfect complex on a ringed site admits finite projective
  representatives in its Tor amplitude interval". Eight hits; the closest is
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, which supplies bounded terms
  without any finite-free-retract property. Ordinary ring/module/projective and
  quasicoherent finite-presentation results do not state the arbitrary-site theorem.
- `rg` in the upstream source and `lean/Sheaf`, patterns
  `finite.*projective.*complex|complex.*finite.*projective|tor.amplitude|strictlyPerfect`,
  found the ring-perfect API, pro-etale/etale site-perfect definitions, and existing
  Tor predicates. None is this theorem. An exact search for this node id found only
  its use in the proof docstring of `EtaleHomFiniteTorAmplitude`; no declaration.
- Read existing strict-perfect packages, tensor descent, and derived restriction,
  instead of duplicating any of these notions.

Original validation (before the returned repair): server compilation accepted the inline
selection, while the local library pass exceeded 60 seconds. That result was insufficient:
the independent immutable-head check returned the timeout. Current validation is recorded
in the repair section below.

## Earlier second reading (a previous round; superseded)

This retained section records the original second reading before the compile-time repair.
The next reader must check the repair below before delivery.

I independently opened the item node, its Stacks source place (Cohomology on Sites,
Tags 08G7 and 08H5), the worker module, and every declaration used in the statement.
The item statement reads as follows, clause by clause:

- The ambient object is a ringed site `(C,O)` with the chosen size convention. In Lean,
  `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)` supplies the site and
  explicit independent object and morphism universes; `R : Sheaf J CommRingCat.{max u v}`
  supplies the commutative ring sheaf. The size-convention dependency is rendered by
  these explicit universe binders, with no extra smallness, finiteness, Noetherian,
  separatedness, or connectedness assumption.
- The module-sheaf category is the existing Mathlib `SheafOfModules` category over the
  underlying `RingCat` sheaf, exactly as supplied by
  `def-weil-sheaf-of-modules-category`; no private module category is introduced.
- The unbounded derived category is rendered by `E : DerivedCategory (SheafOfModules
  ...)` and its `[HasDerivedCategory.{w} ...]` instance. Slice derived categories are
  separately supplied by `[∀ U, HasDerivedCategory.{w'} ...]`, matching the localized
  sites and preserving independent localization universe levels.
- The global and slice sheafification and locally-bijective infrastructure is explicitly
  bound at `AddCommGrpCat.{max u v}`. These are the required hypotheses of the existing
  derived and perfectness interfaces, and no stronger site hypothesis is added.
- Localization and restriction use the recorded canonical declaration
  `ringedSiteDerivedRestrictionOfUniverses`, applied to the underlying ring sheaf, an
  object `V`, and `E`. This is the dependency's actual construction, rather than an
  arbitrary restriction map or a second definition.
- The original K-flat derived tensor was the inline choice from the recorded descent
  theorem. The compilation repair below replaces that expression by the already
  defined `wfSiteDerivedTensor J R`, whose body is that same expression; its arguments
  remain `E` and `(DerivedCategory.singleFunctor _ 0).obj F`. Thus the degree-zero
  test sheaves and canonical descent tensor are unchanged.
- The Tor-window hypothesis is rendered as `(a b : ℤ) (_hab : a ≤ b)` and, for every
  module sheaf `F` and integer `r`, `r < a ∨ b < r → IsZero (...)`. The `IsZero` target is
  the module-sheaf homology object in degree `r`, so this is the node's cohomology-sheaf
  vanishing and does not accidentally assert vanishing only after global sections.
- The conclusion is `∀ U : C, ∃ S : Sieve U, S ∈ J U ∧ ...`, the intrinsic sieve form of
  a covering family. For every `V` and arrow `f : V ⟶ U` in the sieve, Lean produces
  `P : StrictPerfectCoefficientRepresentationOfUniverses ...` of the canonical derived
  restriction. Its `F` field is the bounded cochain complex of module sheaves, its
  `package` field gives the degreewise finite-free retracts, and its `represents` field
  gives the derived isomorphism to `E|V`. The final conjunct
  `∀ r, r < a ∨ b < r → IsZero (P.F.X r)` is exactly the prescribed-window condition;
  `P.bounded` supplies boundedness. This is equivalent to the node's covering family
  `{V_j → U}` and `P_j ≅ E|_{V_j}` wording under the existing package declaration.

Edge cases were checked against both the node and the file. The interval may have
`a = b`; the single allowed degree is retained. The empty/zero complex and zero ring or
zero object are admitted (rank zero and zero terms are allowed). Empty sites and empty
covering sieves are not excluded by an unstated `Nonempty` hypothesis. The disjunction
covers all integers outside the interval, including the `a = b` boundary case. No
characteristic, stalk, enough-points, constant-coefficient, finite-type, or Noetherian
condition is introduced, and all universe parameters are explicitly bound.

I repeated the existing-declaration searches: `msearch.py` LeanFinder, Loogle, and
LeanSearch queries for a locally finite-projective/strict-perfect Tor-window theorem;
`rg` over Mathlib, the upstream `WeilConjectures` tree, and this project's `lean/Sheaf`;
and an exact search for the node id. The searches found only general bounded derived
representative/K-projective results and the existing package/restriction infrastructure,
not this statement. The package, tensor-descent theorem, and derived-restriction theorem
were opened and confirmed as the declarations actually used by the module.

No mismatch was found, so no Lean or node repair was necessary. The worker's node copy
already adds the landed canonical derived-restriction dependency and its `lean.statement`
is verbatim the theorem signature. The module compiles cleanly with the required
`scompile.py` command; the only permitted proof placeholder is the theorem's `sorry`.

## Repair of returned delivery (2026-10-16)

Return L, immutable head `c6913b751be8`, reported that the library compilation timed
out after 60 seconds. Reproduced with the prescribed `scompile.py`: the sandbox
elaboration finished in 7.2 seconds, whereas the library pass exceeded 60 seconds.
Server confirmation of the old file took 47.5 seconds; the previous server success
did not resolve the independent local failure.

Replaced only the inline, deeply nested existential choice of the derived tensor
by the existing `SheafOfModules.wfSiteDerivedTensor J R`. Read its full signature,
docstring and defining body in `Sheaf.Paper.WeilTensorProduct`: the body is exactly
`(wf_site_derived_tensor_descent.{u, v, w, 0, 0} J R).choose_spec.2.2.1.choose_spec.2.choose`.
Thus the replacement is definitionally the same functor and introduces no arbitrary
choice, extra hypothesis, weakened conclusion or size restriction. Imported that
module publicly, added the already landed `def-wf-tensor-product` to `stmt_deps`,
and refreshed the verbatim `lean.statement`. There is no DAG dependency path from
that node back to this item, even traversing both statement and proof dependencies.
No additional node or declaration is stated. All other sandbox fields agree with
current main except the previously added canonical restriction dependency and `lean`.
The delivery wrapper rebases the repaired packet on current `newtargets-dag`.

Validation: the prescribed `scompile.py` now succeeds locally with no errors or
warnings: sandbox elaboration 2.9 seconds, library artifact compilation 5.0 seconds.
The required newly reached overlays also compiled within their unchanged limits
(`PbcWeilCategory`: 30.4 seconds; `WeilTensorProduct`: 47.3 seconds). The 60-second
limit, two threads and nice 19 were unchanged. The theorem still has exactly one
`sorry`; its signature matches `lean.statement` verbatim, all universes are bound,
and every Lean line is at most 100 characters. Server confirmation of the repaired
module also passed in 2.2 seconds.

`deliver2.py Q64 lem-sf-site-perfect-tor-window --no-push` printed:
`OK (dry run): commit 346ceb728c passes the preflight and compiles; nothing pushed`.
This includes current-main rebasing, preflight and per-file compilation. The next
reader reviews and delivers; this worker has not pushed.

## Second reading by Q64

I independently read the current node and its sandbox copy, Stacks
`sites-cohomology.tex` at `lemma-perfect-precise` (08G7) and
`lemma-tor-amplitude-pullback` (08H5), and the delivered Lean file. The source has
an arbitrary ringed site, commutative coefficient sheaf, derived object and
integers a <= b; it does not impose enough points or a geometric finiteness
condition. Its final displayed complex has exactly the prescribed degrees.
The node specializes the source argument to an already locally perfect object
and spells out the upper shortening. Its statement has not been corrected in
this delivery, so no statement_change or citer audit is required.

Object/hypothesis/conclusion checklist, in the node's order:

1. Ringed site, small in the chosen bound: `{C : Type u} [Category.{v} C]`,
   `J : GrothendieckTopology C`, and `R : Sheaf J CommRingCat.{max u v}`.
   Verdict: same arbitrary site and commutative sheaf; u and v are independent.
   The common bound max u v is the tensor dependency's recorded convention,
   not a restriction to sites with equal object and Hom universes. The explicit
   global/slice `HasSheafify` and `WEqualsLocallyBijective` instances provide the
   standard abelian sheaf infrastructure on sites small in that bound.
2. Module category and unbounded derived object: `SheafOfModules` over the
   underlying RingCat sheaf and `E : DerivedCategory (...)`, with
   `HasDerivedCategory.{w}` globally and `HasDerivedCategory.{w'}` on slices.
   Verdict: exactly Mathlib's categories. I opened `ringedSiteModules`,
   Mathlib's derived-category definition, Q, singleFunctor, homologyFunctor,
   and the slice over/overFunctor/overMap signatures; no substitute category
   or bounded derived category appears. The localization sizes remain separate.
3. Local perfectness: `_hperfect : IsPerfectOnRingedSiteOfUniverses.{u,v,0} R E`.
   Verdict: matches the recorded dependency, whose definition I opened.
   It chooses an isomorphic global representative with local bounded models
   mapping quasi-isomorphically to its restriction. Bounds and finite ranks
   may vary between members. The coefficient parameter 0 leaves max u v
   unchanged. No globally categorical-projective or chain-splitting assumption
   is hidden here.
4. Integers and ordering: `(a b : ℤ) (_hab : a ≤ b)`.
   Verdict: exactly the node's interval, including coincident endpoints.
5. Every degree-zero module and derived tensor: `_hTor` quantifies over every
   module sheaf F and uses `(DerivedCategory.singleFunctor _ 0).obj F` as the
   second argument of `(wfSiteDerivedTensor J R).obj`.
   Verdict: the recorded K-flat derived tensor against exactly the required
   tests, with no flatness, constructibility or finite-presentation restriction
   on F. I read the full tensor-descent statement and the actual definition of
   wfSiteDerivedTensor: its body is the identical nested choice expression
   described in the returned-delivery repair. Its natural comparison with total
   tensor on flat K-flat representatives fixes the intended construction.
6. Tor vanishing: for every r, `r < a ∨ b < r → IsZero
   ((DerivedCategory.homologyFunctor _ r).obj ...)`.
   Verdict: exactly all cohomology sheaves outside [a,b], in the module-sheaf
   category. There is no global-sections functor and no homological sign reversal.
7. Every site object and a covering: `∀ U : C, ∃ S : Sieve U, S ∈ J U ∧ ...`.
   Verdict: the covering-family conclusion in intrinsic covering-sieve form.
   Its arrows give the covering family, and closure under pullback/refinement
   does not strengthen the mathematical assertion, since restriction preserves
   the finite-free retractions and the prescribed zero terms.
8. A model on each covering member: `∀ (V : C) (f : V ⟶ U), S f → ∃ P :
   StrictPerfectCoefficientRepresentationOfUniverses ... R V (...)`.
   Verdict: correct quantifier order and localization. The argument is the
   canonical `ringedSiteDerivedRestrictionOfUniverses ... V E`, whose defining
   body restricts Q.objPreimage E and localizes on J.over V. I opened that
   declaration and its original exact-restriction interface.
9. Boundedness, finite-free summands and representation: P.F is the cochain
   complex, P.bounded gives termwise boundedness, P.represents identifies its
   localization with E restricted to V, and P.package supplies degreewise ranks,
   inclusion and projection with `i n ≫ p n = 𝟙 _`.
   Verdict: all three clauses match. I opened both the representation structure
   and StrictPerfectCoefficientPackageOnSite. Its finite product of copies of
   the module unit is the finite free sheaf; no splitting of complexes is asked.
10. Prescribed support: `∀ r : ℤ, r < a ∨ b < r → IsZero (P.F.X r)`.
    Verdict: exact termwise support [a,b], stronger than mere cohomological
    boundedness exactly as the node requires. The additional stored existential
    bound follows from this very interval and is mathematically redundant.

Edge cases: a=b and a=b=0 permit a single nonzero degree. Zero E, the zero ring,
and the zero complex are allowed, including rank zero in the package. Empty
sites and empty covering sieves are not excluded by any Nonempty assumption.
There is no scheme binder, so empty schemes are included whenever such a site
is specialized to them. No characteristic or enough-points restriction occurs.
All universes and variables are bound explicitly; no equality u=v or w=w' is
assumed. I checked the coefficient/module bound against the node's chosen-bound
convention and the actual tensor interface.

Independent duplicate searches used different wording from the worker:

- msearch LeanFinder: "For a perfect derived sheaf with Tor dimension between two
  integers, there are local finite free summand complexes supported in those
  degrees". Eight hits, all ordinary derived bounds or projective vanishing.
- msearch Loogle: `"Tor", "IsZero"`. Twelve hits about zero functors, Tor of
  categorical projectives and unrelated homology; no local perfect-window result.
- msearch LeanSearch: "A locally perfect complex of sheaves of modules with tensor
  cohomology vanishing outside an interval admits bounded finite projective local
  representatives in that interval". Eight hits; the closest is
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`. I opened its actual type:
  its representative has no finite-free-retract property, so it is not a match.
- rg in Mathlib, upstream WeilConjectures and project lean/Sheaf with patterns
  for perfect/Tor in either order, strict-perfect windows/intervals and finite
  free retracts. I opened the upstream Noetherian-ring finite-Tor theorem and
  the pro-etale perfectness module: these are different statements/settings.
  The exact node id/declaration search found only its downstream proof reference.

No new definition nodes or dependency modules are in this delivery. The two
added statement dependencies already carry the actual canonical restriction and
wf tensor definitions, which are reused without copies. I compared all statement
prerequisite node signatures against the declarations used in the file.
The module contains only this theorem with sorry, no hollow definition or extra
proved result. Its source/blueprint docstrings and all eight proof steps match
the node. The stored lean.statement equals the file signature verbatim; every
Lean line is within 100 characters.

No mathematical or Lean mismatch was found in this repaired packet. I retained
the worker's repair unchanged and appended this independent reading only.

Second-reader validation: the prescribed scompile.py accepted the unchanged
module in both locations with no diagnostics (sandbox 26.0 s; library 41.2 s).
The signature/metadata comparison returned true, and the line-width check found
no overlong Lean line. deliver2.py --no-push then printed
`OK (dry run): commit 66e0e2970c passes the preflight and compiles; nothing pushed`.
