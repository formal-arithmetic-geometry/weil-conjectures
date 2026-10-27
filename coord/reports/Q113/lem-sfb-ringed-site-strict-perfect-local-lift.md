## Worker report

The module `Sheaf.Algebra.Homology.RingedSiteStrictPerfectLocalLift` states
`SheafOfModules.exists_strictPerfect_local_lift`, with its entire proof `sorry`.
There are no new definitions, helper theorems, dependency repairs, or statement changes.
The node's source was read directly in `literature/stacks-project/sites-cohomology.tex`,
lemma-lift-through-quasi-isomorphism (Tag 08FQ), together with the preceding local
null-homotopy lemma (Tag 08FP). The declaration docstring contains all three accepted
DAG proof steps: cone cohomology vanishing, local null homotopy, and the two cone
components giving the chain lift and homotopy with the specified sign.

Clause-by-clause rendering:

- The site is `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`. Object and
  morphism universes remain independent. `R : Sheaf J CommRingCat.{max c v r}` is the
  sheaf of commutative rings. `sheafCompose ... (forget₂ CommRingCat RingCat)` is its
  canonical underlying ring sheaf, which Mathlib's module-sheaf API requires.
- `U : C` and `.over U` specify precisely the localized ringed site. The complexes
  `E F G : CochainComplex (ringedSiteModules ... (.over U)) ℤ` have the same coefficient
  ring sheaf, and `a : ℤ` is arbitrary. `u : E ⟶ F` and `v : G ⟶ F` are chain maps.
- The coefficient and module universe is `max c v r`, the standard common universe
  containing the site. This is a size convention, with no equality between `c` and
  `v`. The two slice sheafification class binders supply Mathlib's canonical abelian
  module-sheaf instance, exactly the smallness convention already stated in
  def-weil-sheaf-of-modules-category. They impose no geometric condition on the site.
- `hbounded` says that E is zero outside an arbitrary finite integer interval. This
  is equivalent to finite support, and permits the zero complex and an empty interval.
- `hfinite` says, separately in every degree j, that there are a natural number n,
  an inclusion i into the finite product of n copies of `SheafOfModules.unit`, and
  a retraction p with `i ≫ p = 𝟙 (E.X j)`. In the abelian module-sheaf category this
  finite product is the finite direct sum, hence exactly a finite free module.
  There is no chain compatibility imposed on these degreewise splittings, and no
  uniform rank condition. Rank zero is allowed.
- `hbelow : ∀ j, j < a → IsZero (E.X j)` is exactly the lower bound at a.
- `hiso` uses `IsIso (HomologicalComplex.homologyMap v j)` only for `a < j`.
  `hepi` is `Epi (HomologicalComplex.homologyMap v a)`, namely surjectivity as a
  morphism of sheaves at the boundary degree. This is not sectionwise surjectivity.
  There is no condition on the cohomology map below a.
- The conclusion is `∃ S : Sieve U, S ∈ J U ∧ ...`: a covering sieve, hence the
  covering family consisting of all arrows f in S. Conversely any covering family
  generates such a covering sieve, and restrictions of its local lifts give lifts
  on that sieve. No choice of a restricted index universe or a nonempty cover is used.
- For every `V`, `f : V ⟶ U`, and proof `S f`, the existential t is a chain map
  from the restriction of E to the restriction of G. Restriction is
  `(SheafOfModules.overFunctor (O.over U) (Over.mk f)).mapHomologicalComplex (.up ℤ)`.
  This works directly on the iterated slice `(C/U)/(V/U)`. The canonical
  relocalization in def-pur-localized-ringed-site identifies it with C/V; its section
  at W → V → U is the original section at W. Thus these are exactly E|_V, F|_V,
  G|_V, without an arbitrary replacement map or a pullback hypothesis on C.
- `Nonempty (Homotopy (res.map u) (t ≫ res.map v))` supplies the homotopy with the
  correct orientation. Its component `s^j = h.hom j (j - 1)` has type
  E^j|_V → F^(j-1)|_V. Mathlib's `Homotopy.comm` says
  u^j|_V = d_E^j|_V ≫ s^(j+1) + s^j ≫ d_F^(j-1)|_V + (t ≫ v|_V)^j;
  subtracting the final term and commuting the two summands is precisely the
  displayed equation in the node. Mathlib's `zero` field sets the other degree
  components to zero; it adds no condition on the s^j. No separate redundant
  homotopy equation or unrecorded custom homotopy notion is introduced.
- F and G have neither a boundedness hypothesis nor a degreewise finiteness or
  projectivity hypothesis. The only bounded complex is E.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the recorded transparent abbreviation of `SheafOfModules`. Its full declaration
  and source docstring were read; no module-sheaf category is reconstructed.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`: recorded abstract complex/cohomology framework, imported
  publicly as required by the dependency node. The statement itself is about
  complexes and needs no chosen derived category.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`, `overFunctorMap`,
  and `Mathlib.CategoryTheory.Sites.Over`, `GrothendieckTopology.over`, `Sheaf.over`:
  their source signatures and sectionwise-restriction docstrings were read.
- `WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal`,
  `CategoryTheory.module_overFunctor_preservesZero`: the existing theorem supplies
  zero preservation for restriction of complexes. Its instance attribute is exposed
  for elaboration, rather than declaring another zero-preservation theorem.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` gives the finite products used
  for the finite free modules. `SheafOfModules.unit` is the existing rank-one module.
- `Mathlib.Algebra.Homology.Homotopy`, `Homotopy`, `dNext`, `prevD`, and
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
  `HomologicalComplex.homologyMap`, give the homotopies and cohomology maps.
- The stated proof dependency `lem-sf-derived-homology-long-exact` is imported
  without `public` through `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`;
  its `DerivedCategory.HomologySequence.exact₂` declaration and signature were read.
  `lem-sfb-ringed-site-strict-perfect-local-null-homotopy` has no Lean record or
  Mathlib match at delivery preparation, so its nonexistent module is not imported.
  It remains the named proof prerequisite in the DAG and the theorem docstring.

Edge cases checked against the mathematical statement before writing: E = 0; a
single nonzero term in degree a (only boundary epimorphy is required); nonzero
cohomology of F and G below a; arbitrary negative a; rank-zero summands; empty
covering sieves when allowed by the topology; and completely unbounded F and G.
None is excluded. Epimorphy is interpreted sheaf-theoretically, so the statement
never incorrectly demands global lifting or projectivity of finite free sheaves.

Searches, all made with the authorized msearch wrapper or read-only rg/grep:

- leanfinder: "A map from a bounded complex of finite free retract module sheaves
  lifts locally up to homotopy through a cohomology approximation". Eight hits,
  including `CochainComplex.mappingCone.liftHomotopy`, K-projective and K-injective
  null homotopies, and `CochainComplex.cm5b`; none states local sheaf lifting with
  the partial cohomology hypothesis.
- loogle: `"SheafOfModules", "Homotopy"`. Zero hits.
- Mathlib grep via msearch: `local.*(homotopy|lift)|[Ss]trictly[Pp]erfect` in
  `Algebra/Homology`. Twenty-one hits, localization and derived-category facts;
  none is this local statement.
- leansearch: "Local homotopy lifting from bounded finite free retract complexes
  of module sheaves through a partial cohomology approximation". Eight hits:
  topological homotopy lifting, projective resolution homotopies, and mapping-cone
  liftHomotopy. No match for the theorem here.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for strict-perfect/local-lift and
  local-null-homotopy variants found the constant-ring specialization
  `CategoryTheory.exists_perfect_constant_local_lift`, its constant-source acyclic
  null-homotopy sibling, and scheme/open-stalk specializations. Their assumptions
  and conclusions differ; none treats the arbitrary ring sheaf with this partial
  cohomology approximation. Full relevant source signatures were read.
- `grep -rn 'lem-sfb-ringed-site-strict-perfect-local-lift' lean/WeilConjectures`
  returned no upstream declaration. A full-name rg search for
  `exists_strictPerfect_local_lift` found no existing declaration.

No STATEMENT-DISPUTED flag or node fault was found. The example module
`Sheaf.CategoryTheory.CompactObject` is now a withdrawn module with no declarations;
its node record and the current module conventions were read.

## Second reading by Q113

This is the dispatcher's single-worker delivery; no additional agent was started.
A separate second pass reopened the source, node statement, and final Lean signature.
It checked each binder and conclusion as listed above, including the surjectivity
at a versus isomorphism above a, the fact that only E is bounded, the degreewise
rather than chainwise finite-free splittings, and the direction and sign of the
homotopy. The explicit equation is contained in `Homotopy.comm`, not omitted.
The iterated-slice realization was checked against the recorded relocalization
convention. No mathematical mismatch was found. Early compiler failures exposed
an unnecessarily small coefficient universe; using `max c v r` fixed the size
constraint without equating the object and morphism universes. A line-width warning
was repaired. The maintainer's independent review remains the independent reading.
