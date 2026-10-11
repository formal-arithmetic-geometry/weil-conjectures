## Worker report

`Sheaf.Paper.GradedFinitenessCohomology` states
`AlgebraicGeometry.gradedFinitenessCohomology`, with proof `sorry`. It is the
explicit-action formulation of Stacks 0897(1) in the node. The source was opened
at https://stacks.math.columbia.edu/tag/0897 because the referenced local
`literature/stacks-project/coherent.tex` is absent on this machine. No statement
correction, new definition, or dependency replacement is needed. All structures
and conditions are expressed through existing Mathlib/project notions.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `A B : Type u`, `CommRing A`, `CommRing B`, and `Algebra A B` give the two
  commutative rings and the structure map. `IsNoetherianRing A` and
  `Algebra.FiniteType A B` are precisely Noetherianity and finite algebra type.
- `graded : ℕ → Submodule A B` is the family of homogeneous A-submodules.
  `hgrading : DirectSum.IsInternal graded` asserts that the natural summation
  map from their direct sum is bijective. Thus B is the direct sum, rather than
  merely a filtered algebra or a family of submodules.
- `hunit`, `hmul`, and `hscalar` assert respectively 1 in degree zero, the
  product-degree rule, and the structure map landing in degree zero. The
  multiplication and scalar closure of each component are already in
  `Submodule A B`.
- `f : X ⟶ Spec (.of A)` and `IsProper f` are the named proper morphism.
- `G : ℕ → SheafOfModules (moduleRings X.toRingedSpace)` gives the O_X-modules.
  `hG` says each is quasi-coherent, using Mathlib's notion recorded by the
  `pqf-def-coherent` dependency.
- `mu m k : graded k → (G m ⟶ G (m+k))` gives exactly the O_X-linear morphisms
  indexed by homogeneous b, with no unspecified values at nonhomogeneous b.
- Clause (i) is `hmu_add`, for two elements of the same degree.
- Clause (ii) is `hmu_mul`: first `mu m l b'`, then `mu (m+l) k b`, compared
  with the product action. `HEq` transports the target through
  `(m+l)+k = m+(k+l)`; it does not add a mathematical condition.
- Clause (iii) is `hmu_scalar`, on every open U and every section t. The scalar
  is `((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a`, restricted from top
  to U by `X.presheaf.map`. This is f-sharp(a), not a separately supplied
  arbitrary ring map. `HEq` accounts for `m+0=m` in the target sheaf.
- Clause (iv) is `hfinite`: every point x has an open U containing it and
  finitely many generators `s i`, indexed by `Fin r`, of degrees `d i`.
  Every section t on every V≤U, and every point y of V, has a neighbourhood
  W≤V containing y where its restriction lies in the O_X(W)-linear span of
  the restricted images `mu (d i) (m-d i) b (s i)`, for `d i≤m` and
  `b : graded (m-d i)`. Membership in `Submodule.span` means a finite sum
  with arbitrary O_X(W) coefficients, exactly the two finite sums of the
  node. The action is applied after restricting s to W; naturality of the
  sheaf morphism equates this with restricting its image from U.
  The heterogeneous equality in the generating set accounts for
  `d i+(m-d i)=m` under the displayed inequality.
- `p : ℕ` permits every nonnegative cohomological degree. Each degree carrier
  is `(RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)`.
- The conclusion supplies `mod : Module B (DirectSum ℕ ...)`, so the action
  is a conclusion, not an assumed module structure. `@Module.Finite ... mod`
  asserts its finite generation. The remaining conjunct says that b in
  degree k times `DirectSum.of ... m x` is `DirectSum.of ... (m+k)` of the
  cohomology map of `mu m k b` applied to x. Additivity in both arguments,
  together with the internal decomposition of B and the finite-support
  direct sum, expands this homogeneous identity into precisely the node's
  displayed convolution formula for arbitrary b and x. Conversely, that
  formula implies the identity. No action on other elements is left free.

Dependency declarations and files read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with the ideals-FG
  characterization.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  universally closed supplies quasi-compactness, so its locally finite-type
  clause agrees with the node's finite-type properness.
- `Sheaf.AlgebraicGeometry.Coherent`: its docstring records
  `SheafOfModules.IsQuasicoherent`, and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` supplies that class.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`:
  `AlgebraicGeometry.Scheme.Modules`, definitionally the moduleRings carrier;
  the more general recorded `SheafOfModules` and its morphisms are used here.
- `Sheaf.Paper.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, whose signature
  and docstring specify the shared `RingedSpace.moduleCohomology` carrier;
  its defining module `Sheaf.Topology.RingedSpaceModuleCohomology` was read.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.

Edge cases checked: the zero ring is allowed (no domain or nontriviality
hypothesis); the empty scheme makes the pointwise generation requirement
vacuous and the cohomology sum zero; r=0 means span of an empty set, so it
correctly generates only zero locally. At m=0 only degree-zero generators can
occur. Degrees d_i>m are excluded by the inequality, including the truncated
subtraction boundary. Degree k=0, p=0, zero homogeneous elements, and elements
with empty support remain allowed. The universe u is arbitrary and shared
with schemes and their module carriers; no independent universe of test
objects can make a hypothesis vacuous. No statement dispute was found.

Searches performed in this session (all msearch results are in searches.jsonl):

- LeanFinder: “Cohomology of a finite type graded module on a proper scheme
  is a finite module over the graded algebra”. Eight hits: Proj finite-type
  and properness, finite type generating sections, finite affine sections,
  and cotangent finiteness. No match to this cohomology statement.
- Loogle: `DirectSum.IsInternal, Module.Finite`. Seven hits concerning traces
  and torsion decompositions, no graded sheaf cohomology statement.
- msearch grep: `graded.*cohomology|cohomology.*graded|gradedFiniteness` in
  `Mathlib/AlgebraicGeometry`: zero hits.
- LeanSearch: “sheaf cohomology of a finite type graded module over a graded
  algebra on a proper scheme is finitely generated”. Service unavailable
  (Internal Server Error), recorded as unavailable rather than as no match.
- `rg` in WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  the node id, declaration name, and graded/cohomology combinations: only
  unrelated homological/trace-series statements, no duplicate declaration.
  Inspection of DirectSum.Module, module sheaf morphisms, and the dependency
  files supplied all notions needed, without a new definition.

Validation: scompile compiled the full statement without errors or warnings
in 2.6 seconds. The dry run reported OK, with the second reading intentionally
left to the separate reader; nothing has been pushed.

## Second reading by R1

I independently opened the sandbox node and complete Lean module, all seven
statement-dependency nodes and their recorded declarations, and the source.
The local Stacks .tex is absent; I read the upstream coherent.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
lines 5246–5300, and https://stacks.math.columbia.edu/tag/0897.
The source assumes a Noetherian base, finite algebra type, properness, and a
quasi-coherent graded pulled-back algebra module of finite type. Part (1)
is the finiteness assertion used here; the ample-twist assertion belongs to
part (2), outside this node. There is no extra standing field, nontriviality,
or characteristic assumption. No corrected statement or extra delivery node
is present, so the new-node and correction/citer checks are inapplicable.

The node's objects, hypotheses and conclusions, matched individually:

1. Commutative rings A and B and the A-algebra structure: `A B : Type u`,
   `[CommRing A] [CommRing B] [Algebra A B]`. Exact. The source has a ring,
   not a field. No injectivity of the structure map is assumed.
2. A Noetherian: `[IsNoetherianRing A]`. Exact; I read its abbreviation and
   `isNoetherianRing_iff_ideal_fg` in Mathlib.Noetherian.Defs.
3. Internal nonnegative grading by A-submodules: `graded : ℕ → Submodule A B`
   and `hgrading : DirectSum.IsInternal graded`. Exact: Basic.lean defines
   IsInternal as bijectivity of the canonical sum homomorphism, so every
   element has a unique finite homogeneous decomposition.
4. Unit in degree zero, product in the sum degree, scalars in degree zero:
   `hunit`, `hmul`, `hscalar`. Exact, with precisely the node's quantifiers.
   The A-submodule carrier already encodes additive and A-scalar closure.
5. Finite algebra type of B over A: `[Algebra.FiniteType A B]`. Exact;
   its field is finite generation of the top A-subalgebra, equivalent to
   the polynomial-surjection formulation in the dependency node.
6. Scheme X and named proper f to Spec A: `{X : Scheme.{u}}`,
   `(f : X ⟶ Spec (.of A)) [IsProper f]`. Exact; the recorded Mathlib
   definition uses separated, universally closed, locally finite type.
   Universally closed implies quasi-compact, recovering finite type.
7. Nonnegative family of O_X-modules: `G : ℕ → SheafOfModules.{u}
   (moduleRings X.toRingedSpace)`. Exact. I read Scheme.Modules and the
   SheafOfModules/Hom definitions: these are the established module-sheaf
   carrier and sectionwise linear natural transformations, not abelian
   sheaves supplied with an arbitrary action.
8. Quasi-coherence of each summand: `hG : ∀ m, (G m).IsQuasicoherent`.
   Exact. Coherent.lean expressly uses Mathlib's local-cokernel notion for
   this clause of pqf-def-coherent; on schemes it is equivalent to the
   node's affine tilde-module formulation. Coherence or finite type of
   each G m is not assumed separately.
9. Homogeneous O_X-linear action maps: `mu m k : graded k →
   (G m ⟶ G (m+k))`. Exact; m and k range over all natural numbers.
10. Additivity in b: `hmu_add`. Exact equality of sheaf morphisms for b,b'
    in the same homogeneous component.
11. Multiplicative compatibility: `hmu_mul`. Exact: categorical composition
    acts first by b' of degree l and then b of degree k. The product is
    b*b'; HEq identifies the target indices (m+l)+k and m+(k+l), which
    are equal. It does not relate unrelated sheaves.
12. A-action through f-sharp: `hmu_scalar`. Exact on every open and section.
    I checked ΓSpecIso's signature; its inverse sends A into sections on
    Spec A, `f.appTop` pulls to X, and the presheaf map restricts to U.
    HEq only identifies m+0 with m. Taking a=1 includes the unital law.
13. Cover by opens carrying finitely many homogeneous generators:
    `hfinite` first quantifies over every point x and supplies U, x∈U,
    r, d : Fin r → ℕ, and sections s on U. Exact; pointwise existence
    is equivalent to the stated open cover and permits r=0.
14. Local generation of every degree over every subopen and at every point:
    the remaining `hfinite` quantifiers supply m,V,hVU,t,y,y∈V,W,hWV,y∈W.
    Exact, including the order of choices: U,d,s precede all tested sections.
    The final membership in `Submodule.span` over O_X(W) is exactly a
    finite sum with coefficients c_ij and b_ij in graded(m-d_i), restricted
    to d_i≤m. The set allows repeated indices and arbitrary finitely many
    b's; it does not demand a single b per generator. HEq transports
    d_i+(m-d_i)=m using that inequality. Applying the morphism to s_i
    restricted to W equals restricting its image, by naturality.
15. Fixed nonnegative cohomological p and M_m=H^p(X,G_m): `(p : ℕ)` and
    `(RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)`.
    Exact. I read PQFCohomology and RingedSpaceModuleCohomology:
    the latter is the right derived functor of module-valued global
    sections; no different Ext/underlying-abelian-sheaf carrier is used.
16. Direct sum M and the prescribed B-module structure: the conclusion
    existentially supplies `mod : Module B (DirectSum ℕ ...)`, followed
    by its action on `DirectSum.of ... m x` for every homogeneous b.
    Exact: additivity in B and in M extends this identity to finite sums.
    Internal decomposition of B and the finite-support direct sum then
    give the node's convolution formula in every component n. Conversely
    the convolution formula implies this identity. Thus the existential
    action is fully prescribed, not merely an unrelated finite module.
17. Finitely generated for that same action: `@Module.Finite B _ _ _ mod`.
    Exact, explicitly using the existential module instance. I read the
    class field asserting finite generation of the top submodule.

Edge cases: r=0 gives the empty generating set and zero span. X empty
makes the cover condition vacuous and all cohomology zero. Zero rings and
zero sheaves are allowed; no Nontrivial, field, or characteristic instance
appears. Degree m=0 admits only d_i=0; d_i>m is explicitly excluded rather
than mistakenly enabled by truncated subtraction. k=0, p=0, empty supports,
and zero homogeneous b or x are all covered. Universe u is arbitrary;
rings, schemes and modules share the standard scheme/module universe,
which can be raised to encompass any collection of the specified objects.
There is no independent test-object universe or hidden finiteness instance.

Independent searches (additional queries recorded in searches.jsonl):

- LeanFinder: “Proper pushforward finiteness of direct sum of cohomology of
  homogeneous module sheaves”: eight results on Proj finite type, graded
  algebra generators/localizations and finite-type sheaf generators;
  none states this graded cohomology finiteness theorem.
- Loogle: `AlgebraicGeometry.IsProper, DirectSum`: no hits.
- LeanSearch: “finite generation of graded cohomology under a proper
  morphism over a noetherian algebra”: unavailable (Internal Server Error),
  not treated as a no-match result.
- Independent rg on Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf
  for `graded.{0,60}(finit|cohom)|cohom.{0,60}graded`, the exact name and
  0897 found no duplicate. I also opened GradedSheafStructures.lean:
  its graded algebra/module structures concern arbitrary sheaf algebras,
  and its generation predicate requires degree-zero generators. Neither
  states the present theorem or its arbitrary-degree generation condition.
  The Rees cohomology theorem is a specialization citing this node.

No mismatch was found. I preserved the Lean module and lean.statement
verbatim; the only change is this independent second-reading report.
The sole declaration has proof `sorry`; there are no definitions, private
copies, file-local notation/instances, or hidden proof holes. Its docstring
contains the source, blueprint id and all five proof steps with dependencies.
The module imports supply the notions used. All variables and the universe
are explicitly bound; the clean single-file compile is checked below.

Second-reader validation: scompile compiled the unchanged 136-line module
in 2.7 seconds, exit code 0, with no errors or warnings.
