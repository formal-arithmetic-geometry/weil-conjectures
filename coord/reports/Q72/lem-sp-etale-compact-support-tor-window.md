## Worker report

The existing Q148 module already states almost all of this node. This delivery repairs its
fibre-torsion premise, retaining the module and declaration name
`Sheaf.AlgebraicGeometry.EtaleCompactSupportTorWindow`,
`AlgebraicGeometry.Etale.exists_etaleCompactSupport_torWindow`.
The declaration remains a theorem with exactly `sorry` as its proof. No definition is added.
The natural-language statement, dependencies, proof and all other non-Lean node fields are unchanged.

### Existing-interface fault and repair

The previous signature required every section of F over every etale object to be killed
by a nonzero integer. The node says every torsion sheaf, whose sections need only be
locally torsion. This is a real difference: on a geometric point the constant sheaf Q/Z
is locally torsion, but its sections over a countably infinite disjoint union of points
form a product. The section with coordinates 1/ell^n has no common nonzero annihilator.
The existing definition `CategoryTheory.Sheaf.IsTorsion`, in
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, explicitly documents
this distinction. The sole signature repair replaces the sectionwise condition by
`F.IsTorsion`. Thus the theorem now covers exactly the class required by the node.
This repairs the Lean rendering, rather than correcting the mathematical node.

The proof-only dependency `lem-sfb-proper-geometric-fibre-torsion-bound` currently has
the same sectionwise-only limitation in its Lean signature. Its natural-language node
and underlying geometric dimension argument cover locally torsion sheaves. Stage 3
will need that interface generalized, or to use the cited finite-type torsion
cohomological-dimension theorem directly for this first clause. It is not an added
hypothesis of this delivery. No proof is attempted in stage 2.

### Hypotheses and clauses

* Field and characteristic: `(k : Type u) [Field k] (p ℓ : ℕ) [CharP k p]`,
  `hp : 0 < p`, `hℓ : ℓ.Prime`, `hpℓ : p ≠ ℓ`.
* Schemes W,V and later U use `Scheme.{u}` and `.Over (Spec (.of k))`.
  `IsSeparated` of each structure map supplies separatedness;
  `LocallyOfFiniteType` plus `QuasiCompact` of each structure map supplies finite type.
  These are the explicit ordinary-scheme setting of `sk-def-sfb-dc-setting`.
* The maps are `r : W ⟶ V` and `j : U ⟶ W`, with `.IsOver (Spec (.of k))`,
  `[IsProper r]` and `[IsOpenImmersion j]`.
* `∃ e : ℕ` precedes U,j,R,a,b,K,P. The bound is nonnegative and depends on r,
  not on the compactification's open or its coefficients or model.
* The first conjunct quantifies over `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`,
  `v : Spec (.of Ω) ⟶ V`, and every abelian sheaf on `(pullback r v).smallEtaleTopology`.
  Its hypothesis is now `F.IsTorsion`, precisely local torsion. For every `i : ℤ`
  with `2 * (e : ℤ) < i`, `Subsingleton` of the existing ordinary `cohomology` object
  says its abelian group is zero. No finite, constructible, primary-torsion or common
  annihilator restriction is imposed on F.
* `R : Type (u + 1)` with `[CommRing R] [Finite R]` permits every finite commutative
  coefficient ring. `∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : R) = 0` expresses annihilation
  by a power of ℓ. Requiring n>=1 loses no ring: n=0 forces R=0, which also satisfies n=1.
* `a b : ℤ`, `a ≤ b`, `K : DerivedCategoryModule R U`,
  `DerivedCategory.isBoundedConstructible R U K` and
  `DerivedCategory.hasTorAmplitudeIn R U a b K` give the specified input.
* `P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ`
  is an arbitrary model, not a chosen or existential model.
  `Nonempty (DerivedCategory.Q.obj P ≅ K)` says it represents K.
  For every q, `exactFunctor _ _ (MonoidalCategory.tensorRight (P.X q))` is flatness,
  `Scheme.IsConstructibleEtaleModuleSheaf (P.X q)` is constructibility, and
  `q < a ∨ b < q → IsZero (P.X q)` gives termwise support [a,b].
* The first conclusion is a derived-category isomorphism
  `Q(j_!P) ≅ Dj_!K` under `Nonempty`, using `mapHomologicalComplex (.up ℤ)`
  and `mapDerivedCategory` of the recorded `openImmersionLowerShriek`.
* The next three conjuncts assert flatness and constructibility of every extended
  term and zero extended terms outside [a,b], with the same predicates as the input.
* `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (j_!P)` asserts K-flatness for
  quasi-isomorphisms and the usual signed total tensor on module-sheaf complexes.
  The recorded K-flat dependency publicly exposes this exact predicate for the
  ordinary ModuleCat-valued encoding, as its lean.note requires.
* `DerivedCategory.isBoundedConstructible R W (Dj_!K)` and
  `DerivedCategory.hasTorAmplitudeIn R W a b (Dj_!K)` state the open-extension result.
* The last two conjuncts state bounded constructibility on V and Tor interval
  `[a,b+2e]` for `(rightDerivedLowerStar (ModuleCat R) r).obj (Dj_!K)`.
  This is the unfolded composite in `rightDerivedLowerShriekOfCompactification`
  for the supplied open/proper factorization; no independent compactification
  comparison or pro-etale identification is imposed.

### Dependency declarations read and used

* `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`
  publicly imports `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, whose
  `AlgebraicGeometry.Etale.DerivedCategoryModule` is the ordinary module-sheaf derived category.
* `def-weil-pbc-etale-constructible-sheaf`:
  `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
* `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` publicly exposes
  the bounded-interval `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`
  from `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
* `def-pc-cochain-complex-modules`: Mathlib's `CochainComplex`,
  `Mathlib.Algebra.Homology.HomologicalComplex`.
* `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  which exposes `CategoryTheory.exactFunctor`; its lean.note explicitly directs ordinary
  ModuleCat-valued sheaves to this predicate on the canonical tensorRight functor.
* `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  publicly exposing `CategoryTheory.MorphismProperty.kFlat` from
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`. The independent-coefficient
  SheafOfModules predicate is not applied to the different ModuleCat-valued encoding.
* `sk-def-sfb-dc-setting`: read `compactificationOverField` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  Its geometric setting is rendered by the explicit binders above; its condensed
  coefficient category is not used for this ordinary-etale node.
* `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
* `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
* `def-weil-pbc-extension-by-zero`:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
* `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
* `def-weil-pbc-constructible-complexes`:
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.

The existing proof-plan imports are retained. The docstring gives all seven node proof
steps with their dependency ids, including the open tensor calculation, preservation
of constructibility, bounded-flat K-flatness, and the proper Tor estimate with d=2e.

### Edge cases

Checked U empty, j the identity, empty W or V, zero K/P, zero R, a=b, negative a,b,
and e=0. The signature excludes none of these. The support interval includes its
endpoints. The zero ring admits an annihilating positive power. The locally torsion
clause also includes mixed torsion and unbounded local exponents, such as Q/Z above.
All universes and variables are explicitly bound, and autoImplicit is disabled.
No STATEMENT-DISPUTED flag: the source and mathematical node agree.

### Searches

The prescribed msearch.py searches, recorded in searches.jsonl, returned:

* LeanFinder, “Extension by zero of flat constructible etale complexes and proper
  direct image Tor amplitude window”: eight abstract derived-degree-bound hits;
  none states this result.
* Loogle, `"torAmplitude", "Sheaf"`: zero hits.
* Mathlib grep, `torAmplitude|openImmersionLowerShriek`, CategoryTheory: zero hits.
* LeanSearch, “Extension by zero and proper direct image preserve constructible etale
  complexes of finite Tor amplitude”: eight generic exact-functor/homology hits,
  none states the desired result.
* rg of WeilConjectures and Sheaf for the node id and Tor-window names found precisely
  the existing Q148 module. Its full source was read locally and independently fetched
  using `scompile.py --source Sheaf.AlgebraicGeometry.EtaleCompactSupportTorWindow`.
  Direct source inspection of SheafCohomology.Basic found the existing locally torsion
  predicate and its explicit warning about groups of sections. The existing theorem
  therefore needs the single premise repair above instead of an existing:true rebind.

### Validation

The module is compiled with scompile.py and the final delivery dry run runs server
preflight and single-file compilation. Only the expected sorry warning is permitted.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
