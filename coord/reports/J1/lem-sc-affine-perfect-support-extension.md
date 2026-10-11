## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension` states
`AlgebraicGeometry.Scheme.exists_perfect_supported_extension`, with proof `sorry`.
The node statement is unchanged. I read the statement and proof of Stacks Project
[Tag 08EK](https://stacks.math.columbia.edu/tag/08EK), Lemma 36.13.10. The local
literature checkout is absent on this machine, so the official tag was read online.
The docstring carries all four steps of the DAG proof, naming their dependencies.

Hypothesis and conclusion correspondence:

- Affine scheme X: `(X : Scheme.{u}) [IsAffine X]`.
- Closed subset T: `(T : Set X) (hT : IsClosed T)`.
- Quasi-compact complement: `(hTc : IsCompact Tᶜ)`. Mathlib `IsCompact` means
  finite-subcover compactness, with no Hausdorff assumption, hence quasi-compactness.
- Quasi-compact open U: `(U : X.Opens) (hU : IsCompact (U : Set X))`.
- Every object F of D(O_U): `(F : schemeDerivedCategory U.toScheme)`.
  The derived-category binders for X and U and all their opens are exactly the
  infrastructure required by the dependency's perfectness definition; they do not
  impose boundedness, quasi-coherence, or other mathematical hypotheses on F.
- Perfect F: `(hF : IsPerfect U.toScheme F)`, the recorded definition, without a copy.
- Cohomology vanishes on U outside T: `hFT` quantifies over every integer n and
  every point x of U, and says `Subsingleton` of the underlying additive stalk
  of `(DerivedCategory.homologyFunctor ... n).obj F` when `U.ι x ∉ T`.
  Points of U already lie in U, so this is precisely U minus (T intersection U).
- Existence of E in D(O_X): `∃ E : schemeDerivedCategory X`.
- Perfect E: the first conjunct `IsPerfect X E`.
- Cohomology of E vanishes outside T: the second conjunct quantifies over all
  n and x outside T and requires its additive stalk to be `Subsingleton`.
  For a stalk module this means the zero module, without a spurious `IsZero`
  instance on its underlying type.
- E restricted to U is isomorphic to F direct-sum F[1]: the last conjunct is
  `Nonempty (... ≅ biprod F ((shiftFunctor (schemeDerivedCategory U.toScheme)
  (1 : ℤ)).obj F))`. Restriction first uses the recorded
  `SheafOfModules.overFunctor` on the localized open site, then Mathlib's
  `U.sheafOfModulesEquivOver` transports to sheaves on the open subscheme U.
  Both are induced on derived categories by `Functor.mapDerivedCategory`.
  The `show schemeDerivedCategory U.toScheme from ...` annotation fixes the
  already shared carrier before elaborating the isomorphism; it adds no data.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; also Mathlib's `IsAffine` and
  `Scheme.Opens.toScheme` for the affine and open clauses.
- `def-pc-derived-category`: `Sheaf.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`; its module and full signature were read.
- `def-pc-perfect-complex`: `Sheaf.AlgebraicGeometry.PerfectComplex`,
  `AlgebraicGeometry.Scheme.IsPerfect`; its full local strictly-perfect definition,
  open-cover quantification, restriction, and docstrings were read.
- Additional existing interfaces: Mathlib `TopologicalSpace.Opens.sheafOfModulesEquivOver`,
  `TopCat.Presheaf.stalk`, `DerivedCategory.homologyFunctor`, `Limits.biprod`,
  and `CategoryTheory.shiftFunctor`. The canonical equivalence's additivity is
  supplied locally by `Functor.additive_of_preserves_binary_products`.
  The local derived-category instance on the restricted sheaf is
  `inferInstanceAs` of the instance already bound for U, not a new choice of D(O_U).
  No definitions or theorem proofs were added; the two local infrastructure
  instances are terms of existing Mathlib constructions.

Edge cases checked: X empty, U empty, F zero, T empty, T=X, and U=X are all
permitted; no `Nonempty` assumption on schemes/opens and no nonzero assumption
on F is present. When T is empty, hFT forces all stalks of all cohomology to
vanish. When T=X, both support conditions are vacuous, as in the source. Cohomology
is quantified over all integers, and the shift is positive one. Universes u and w
are explicit and shared with the recorded definitions; no independent test-object
universe or auto-bound implicit is used. No source or node fault was found.

Searches for an existing statement (all through the prescribed search tools):

- msearch leanfinder, `perfect complex on affine scheme with closed support extension
  direct sum shift`: eight hits on generic derived-category cohomological bounds
  and injective vanishing, none about perfect extension with closed support.
- msearch loogle, `AlgebraicGeometry.Scheme.IsPerfect, DerivedCategory`: zero hits,
  unknown identifier `AlgebraicGeometry.Scheme.IsPerfect` in the indexed Mathlib.
- msearch grep, `affine.*perfect|perfect.*support|support.*extension`,
  AlgebraicGeometry: zero hits.
- msearch leansearch, `perfect complex affine extension supported closed subset`:
  unavailable, Internal Server Error; no verdict is drawn from this search.
- Local rg for `perfect|Perfect` in upstream WeilConjectures/AlgebraicGeometry
  found perfect-field material and perfect loci of coherent sheaves, not this theorem.
- Local rg for `affine.*perfect|perfect.*support|support.*extension` in Mathlib's
  AlgebraicGeometry, upstream WeilConjectures/AlgebraicGeometry, and lean/Sheaf/
  AlgebraicGeometry found no matching statement.
- rg for `lem-sc-affine-perfect-support-extension` throughout upstream
  WeilConjectures found no declaration.
- rg for `exists_perfect_supported_extension` in dag/lean_names_upstream.json,
  Mathlib, and upstream WeilConjectures found no name collision.

Compiler checking: initial interface errors (underlying presheaf projection,
explicit stalk coefficient category, open-site carrier instance, and isomorphism
carrier annotation) were fixed without changing the mathematical statement.
The final server compile is clean (no errors or warnings). The delivery dry run
printed OK: it compiles and passes preflight except for the independent second
reading, which is intentionally left to the second reader. Nothing was pushed.

## Second reading by J1

I independently compared the node statement with `AlgebraicGeometry.Scheme.exists_perfect_supported_extension` in `lean/Sheaf/AlgebraicGeometry/AffinePerfectSupportExtension.lean` and with Stacks Tag 08EK (Lemma 36.13.10). The correspondence is exact, item by item:

- `X` and `[IsAffine X]` render the affine scheme.
- `T : Set X`, `hT : IsClosed T`, and `hTc : IsCompact Tᶜ` render a closed subset with quasi-compact complement.
- `U : X.Opens` and `hU : IsCompact (U : Set X)` render a quasi-compact open.
- `F : schemeDerivedCategory U.toScheme` and `hF : IsPerfect U.toScheme F` render an arbitrary perfect object of `D(O_U)`.
- `hFT` quantifies over every integer degree and every point of `U.toScheme`, requiring subsingleton stalks whenever `U.ι x ∉ T`; this is support on `T ∩ U`.
- The conclusion introduces `E : schemeDerivedCategory X`, requires `IsPerfect X E`, and requires subsingleton cohomology stalks at every `x ∉ T`.
- The final `Nonempty` is an isomorphism after restriction to `U`, via `SheafOfModules.overFunctor` followed by `U.sheafOfModulesEquivOver`, with target `biprod F ((shiftFunctor ... (1 : ℤ)).obj F)`, exactly `F ⊕ F[1]`.

No hypotheses are stronger than the source and no conclusion clause is weakened or strengthened. The explicit derived-category instance binders are infrastructure required by the recorded `schemeDerivedCategory` and `IsPerfect` declarations; they add no mathematical finiteness, boundedness, or nonzero assumptions. The local additive and carrier instances are ordinary interface instances and do not alter the theorem statement. The source proof's four steps (finite principal description, affine extension and annihilation powers, iterated cones, and the lifted map followed by a cone) are recorded in the theorem docstring.

Edge cases checked: empty `X` or `U`, zero `F`, empty `T`, `T = X`, and `U = X` remain admissible; all integer degrees and positive shift one are explicit; universes `u` and `w` are bound and shared with the dependencies. No statement mismatch was found and no repair was needed.

Searches were reviewed against Mathlib, upstream `WeilConjectures`, and `lean/Sheaf` using concept/name grep plus LeanFinder/Loogle/msearch records in the worker report; no existing declaration states this lemma. The module compiles cleanly with `scompile.py`.
