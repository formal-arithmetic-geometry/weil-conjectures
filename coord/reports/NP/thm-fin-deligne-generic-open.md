## Worker report

The module `Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility` states
`AlgebraicGeometry.Etale.exists_nonempty_open_isBoundedConstructible_derived_open_pushforward`.
Its only theorem has proof `sorry`; no definitions or helper theorems were added.
The node statement and dependencies are unchanged.

Clause-by-clause reading:

- A field k is `(k : Type u) [Field k]`. The integral base is
  `(S : Scheme.{u}) [IsIntegral S]`. Its morphism to the field spectrum is `aS`,
  with `[LocallyOfFiniteType aS] [QuasiCompact aS]`, exactly finite type.
- The prime implicit in the notation F_ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
  `hℓ : ℓ ≠ ringChar k` excludes precisely the characteristic prime.
- Finite-type S-schemes are `X, Y`, their structure maps `aX, aY`, and the
  corresponding locally-of-finite-type and quasi-compact instances.
  `j` has `[IsOpenImmersion j]`; `hj : j ≫ aY = aX` says it is over S.
- `F` is a sheaf on `X.smallEtaleTopology` with values in
  `ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))`. The lift only implements the
  fixed size convention; `ULift.ringEquiv` identifies this ring with F_ell.
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F` is the recorded finite-value
  constructibility notion, rather than the different upstream stalk formulation.
- `∃ U : S.Opens, Nonempty U ∧ ...` is a nonempty open in S, with its actual
  open subscheme `U.toScheme` and inclusion `U.ι`.
- The first conclusion quantifies over Cartesian presentations of the restrictions:
  `IsPullback pY bU aY U.ι` presents `YU = Y ×_S U`, and
  `IsPullback pX jU j pY` presents `XU = X ×_Y YU = X ×_S U`, with `jU = j_U`.
  Quantifying over all such presentations expresses invariance under the canonical
  isomorphism between pullback models; it adds no geometric assumption. Scheme
  pullbacks exist, so this formulation is not vacuous.
- `_root_.DerivedCategory.singleFunctor _ 0` places F in degree zero. Applying
  `L((pX)^*[...])` is restriction to XU, since constant-coefficient inverse image
  is exact. Applying `R((jU)_*[...])` is ordinary derived direct image. The predicate
  `DerivedCategory.isBoundedConstructible ... YU` says all its cohomology sheaves
  are constructible and vanish outside one bounded integer interval, exactly D^b_c.
- The second conclusion is universal in `(T : Scheme.{u}) [IsNoetherian T]` and
  `(t : T ⟶ U.toScheme)`, with no finite-type, separatedness or dominance condition
  on t. `IsPullback qY bT bU t` presents YT, and
  `sq : IsPullback qX jT jU qY` presents XT and jT.
- `IsIso ((derivedBaseChangeMap ... sq.toCommSq).app ...)` tests the canonical
  exchange component at the same restricted F[0]. Its domain is
  `LqY^* RjU_* LpX^* F[0]` and its codomain is
  `RjT_* LqX^* LpX^* F[0]`, the two terms displayed in the node. It asserts
  invertibility of this actual map, not existence of an unspecified isomorphism.
- All categories here are ordinary unbounded derived categories. The first conclusion
  places the resulting object in their bounded constructible full subcategory.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, including its
  full definition in terms of `Scheme.IsConstructibleEtaleModuleSheaf`, `IsZero`,
  and degree bounds. The latter constructibility declaration was also read in
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` / upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and
  `_root_.DerivedCategory.singleFunctor`. The node's torsion predicate is not
  needed: prime-field coefficients already specify the coefficient category.
- `def-weil-pbc-scheme-conventions` is a convention record with no own declaration.
  Used Mathlib `Scheme`, `IsIntegral`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsOpenImmersion`, `IsNoetherian`, `Scheme.Opens`, and `IsPullback` directly.
- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMap`, with its full signature, docstring
  and mate construction read. Here its square has `(g', f', f, g) = (qX, jT, jU, qY)`.
  The standard `L` and `R` functors were checked in the source's
  `Etale.Derived.UpperLowerStar`, including the exact-pullback identification.
- All already recorded modules of proof dependencies are imported without `public`
  unless already a public statement import. Unstated proof nodes do not prevent
  stating the theorem; they remain in the node's existing proof plan.

Edge cases checked: integral S is nonempty by Mathlib's actual definition; empty X
and Y and the zero sheaf are allowed; no nonempty source/target or generic dominance
was imposed. Zero-dimensional bases and characteristic zero are allowed. The prime
condition excludes ℓ = 0, 1, while hℓ excludes exactly the forbidden characteristic.
The identity base change and the empty Noetherian test scheme are included. No
bound, connectedness, finite type or reducedness was imposed on test schemes. All
scheme objects use the same arbitrary universe u and the established coefficient
universe u+1; every variable and universe is explicitly bound. Cartesian presentations
are universally quantified and the required pullbacks exist in Scheme.

Searches for an existing declaration:

- `msearch.py ... leanfinder`: "generic bounded constructibility and base change for an
  open immersion over an integral finite type base" returned eight elementary
  openness/base-change hits, none concerning generic derived constructibility.
- `msearch.py ... loogle`: `"baseChange", "constructible"` returned zero hits.
- `msearch.py ... leansearch`: the generic constructibility / universal Noetherian
  base-change query returned service unavailable (Internal Server Error).
- `msearch.py ... grep`: `generic.*base.?change|constructible.*open.*immersion` in
  AlgebraicGeometry returned zero hits.
- `rg` of upstream WeilConjectures for the item id returned zero hits. Searches for
  Deligne/generic constructibility found `Etale.Derived.Finiteness.DirectImage`,
  which was opened: its open-immersion result has no generic-base/exchange assertion
  and uses the different upstream constructibility predicate, so is not this node.
- `rg` in the project's `lean/Sheaf` for generic open/constructibility and the exchange
  found constituent predicates and exchange lemmas, but no instance of this statement.
- The full chosen theorem name was searched in Mathlib, upstream WeilConjectures,
  project Lean and `dag/lean_names_upstream.json`: zero occurrences.

No statement correction, disputed statement, new node, or dependency repair was needed.
Server `scompile.py` compiled the file cleanly (both sandbox and library-path checks).

## Earlier second reading (a previous round; superseded)

I independently read the node, its eight proof steps, the whole delivered module,
the dependency records and the definitions used by its signature. Verdict: the Lean
states the node exactly. No mathematical mismatch was found, and no Lean, node
statement, dependency, or proof-plan change was needed. Only this second reading and
its validation record were added. There are no new nodes or dependency modules.

Source check: the node's source is the local blueprint
`sec-smooth-purity/sk-prop-sf-cbc/thm-fin-deligne-generic-open.md`, not a Stacks
lemma. I read that file's statement and proof, including its standing Noetherian
base-change convention. It introduces no separatedness, perfectness of k, smoothness
of X, or finite-type condition on T in the theorem. Smoothness and local constancy
occur only in an intermediate proof case. The node's expanded proof correctly keeps
them out of the statement. No statement correction or citer audit is applicable.

Object, hypothesis and conclusion checklist:

- Field k: `(k : Type u) [Field k]`. Correct; it need not be finite, perfect,
  algebraically closed, or of positive characteristic.
- Integral finite-type k-scheme S: `(S : Scheme.{u}) [IsIntegral S]`,
  `(aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]`.
  Correct: these two morphism properties together mean finite type. Mathlib's
  `IsIntegral` includes nonemptiness and integral section rings on nonempty opens.
- Prime coefficient characteristic different from char(k): `(ℓ : ℕ) [Fact ℓ.Prime]`
  and `hℓ : ℓ ≠ ringChar k`. Correct: primality is implicit in the source's F_ell,
  and the inequality adds no invertibility or characteristic hypothesis.
- Finite-type S-schemes X and Y: `X Y : Scheme.{u}`, `aX : X ⟶ S`,
  `aY : Y ⟶ S`, each with `LocallyOfFiniteType` and `QuasiCompact`.
  Correct, without extra quasi-separatedness or separatedness assumptions.
- Open immersion over S: `(j : X ⟶ Y) [IsOpenImmersion j]` and
  `hj : j ≫ aY = aX`. Correct; the structure maps commute in the required direction.
- Constructible F_ell-sheaf F on X: `Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))` and
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`. Correct: prime `ZMod ℓ` is
  F_ell, the lift is its canonical ring-equivalent size lift, and the predicate is
  the dependency's finite locally closed constructible stratification with finite
  locally constant module values. It is not an unrelated stalkwise predicate.
- Existence of a common nonempty base open: `∃ U : S.Opens, Nonempty U ∧ ...`.
  Correct; both conclusions use this same U, chosen after F and before T.
- Restriction schemes and arrows: the universal `XU`, `YU`, `pX`, `pY`, `bU`, `jU`
  satisfy `IsPullback pY bU aY U.ι` and `IsPullback pX jU j pY`. Correct: pasting
  presents X_U and Y_U over U, with the induced open immersion. These are arbitrary
  models of actual existing scheme pullbacks, not additional geometric assumptions.
- First conclusion: `DerivedCategory.isBoundedConstructible ... YU` applied to
  `R(jU)_* (L(pX)^* (singleFunctor _ 0 F))`. Correct: F starts in degree zero,
  exact inverse image implements its restriction, and the recorded predicate demands
  constructibility of every integer cohomology sheaf and vanishing outside one
  finite integer interval. No Tor amplitude or perversity condition occurs.
- Every Noetherian base change: `∀ (T : Scheme.{u}) [IsNoetherian T]
  (t : T ⟶ U.toScheme)`. Correct: arbitrary morphisms, with no dominance,
  finite-type, connectedness, or reducedness requirement.
- Its Cartesian presentations: `IsPullback qY bT bU t` gives Y_T and
  `sq : IsPullback qX jT jU qY` gives X_T and j_T. Correct by pullback pasting.
- Second conclusion: `IsIso ((derivedBaseChangeMap ... sq.toCommSq).app
  (L(pX)^* (singleFunctor _ 0 F)))`. Correct: I read the actual mate definition in
  `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`. Substitution
  `(g', f', f, g) = (qX, jT, jU, qY)` gives precisely
  `LqY^* RjU_* F_U → RjT_* LqX^* F_U`. This is invertibility of the specified
  exchange morphism, not an unspecified isomorphism. Composition of inverse images
  identifies the last restricted sheaf with F restricted to X_T.
- Ordinary derived categories: all the terms lie in unbounded `DerivedCategory`;
  bounded constructibility is an object predicate. Correct; no completed category.

Dependency/interface check: I opened `BoundedConstructibleComplexes`,
`DerivedCategories`, `IsConstructibleEtaleModuleSheaf`, upstream `Coefficients`,
`DerivedUnbounded`, and `Derived.UpperLowerStar`. Their actual signatures support
all the objects above with no extra caller instances. In particular the left derived
inverse image has the canonical comparison to the functor induced by exact inverse
image, and right derived direct image is the unbounded right adjoint. The scheme
conventions node intentionally has no declaration. I read Mathlib's finite-type,
quasi-compact, integral, and Noetherian definitions, and checked the recorded proof
modules against the import list. Unstated proof-only prerequisites are not missing
objects in this signature. All available recorded proof modules are imported.

Edge cases: empty X and Y, the zero coefficient sheaf, empty Noetherian T, and identity
base change remain allowed. Empty S is excluded by integrality in both source and
Lean. No index family or dimension parameter is bound in this theorem, so the empty
generic fibre and n = 0 proof cases are not excluded. Characteristic zero is allowed;
prime ell excludes 0 and 1 and the inequality excludes exactly ell = char(k).
Zero-dimensional S is allowed. All schemes and the field use an arbitrary universe u,
with the established u+1 coefficient convention; the small etale site and coefficient
universes match the dependency interfaces. No free variables, implicit extra universe
constraints, local notation, private definitions, or hollow definitions occur.

Independent searches (different wording from the author's):

- LeanFinder: `dense base open simultaneous finiteness of higher direct images and
  exchange for etale sheaves`: eight hits, only elementary sites/etale algebra and
  covering results; none states this theorem.
- Loogle: `"IsOpenImmersion", "IsIso", "derivedBaseChangeMap"`: no hits.
- LeanSearch: the open-immersion/dense-base-open/Noetherian-base-change query was
  unavailable (Internal Server Error); no conclusion was drawn from that service.
- Direct rg in Mathlib AlgebraicGeometry, project Sheaf and upstream WeilConjectures:
  `generic.{0,45}(constructib|exchange|base.change)`, `deligne.{0,30}generic`, and the
  full chosen theorem name. No existing version was found. The upstream
  `GenericConstancy.IsConstructibleSheaf.exists_dense_open` was opened: it only
  trivializes a sheaf generically on its own scheme, with no derived direct image
  or universal exchange. The upstream Finiteness/DirectImage open-immersion theorem
  was opened: it asserts bounded constructibility, but no simultaneous generic
  base-change clause, and uses the other constructibility predicate. The project's
  generic finite pushforward results concern finite morphisms, not this assertion.
  The full chosen name also has no Mathlib/upstream/name-index collision.

Conventions: the source and blueprint docstrings are present, and the theorem
proof docstring follows all eight node steps. The only proof is the named theorem's
`sorry`; the module contains no new definitions and nothing proved. The node copy
changes only its lean record, whose statement is verbatim the module's signature.

Validation note: the installed scompile command initially selected its local overlay,
contrary to the requested server-only setting. This tooling discrepancy is reported
here for the maintainer. Subsequent validation and delivery explicitly select the
existing `scompile.run_server` entry point (nice 19, standard server limits) without
editing the tools or upstream library. The required server compile and preflight
results are recorded below.

Server validation passed: the delivered module compiled in 4.0 s with nice 19,
two threads and the 60 s per-file limit, without errors or warnings. The node's
lean.statement was also checked verbatim against the file, and every Lean line is
at most 100 characters. The deliver2 server-only dry run printed OK: preflight and
compilation passed with the second-reading section included.

Delivery was attempted three times after the successful dry run. The server closed
SSH connections during one compile connection, a later final Git push (after clean
compile/preflight), and the last preflight connection. No successful delivery was
reported. The completed review and unchanged module remain in this sandbox; this is
a transport/tool failure, not a missing mathematical dependency.

## Second reading by NP

I reread the blueprint node and matched each binder and conclusion against
`Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility`.

- The field, integral base, finite-type structure map, prime `ℓ`, and
  `ℓ ≠ ringChar k` are rendered by `(k : Type u) [Field k]`, `S` with
  `[IsIntegral S]`, `aS` with `[LocallyOfFiniteType] [QuasiCompact]`, and
  `(ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ...)`; verdict: exact.
- The finite-type `S`-schemes `X,Y`, their structure maps and instances, and
  the open immersion over `S` are rendered by `aX`, `aY`, `j`, the six
  finiteness instances, and `hj : j ≫ aY = aX`; verdict: exact.
- The constructible `F_ℓ` sheaf is rendered as a sheaf on
  `X.smallEtaleTopology` with `ModuleCat (ULift (ZMod ℓ))` and
  `Scheme.IsConstructibleEtaleModuleSheaf F`; verdict: exact established
  coefficient-universe convention.
- The common nonempty open is `∃ U : S.Opens, Nonempty U`; verdict: exact.
- The restriction models and arrows are universally quantified `XU,YU,pX,pY,
  bU,jU` with the two required `IsPullback` hypotheses; verdict: exact.
- The first conclusion is `DerivedCategory.isBoundedConstructible` for
  `R(jU)_* (L(pX)^* (singleFunctor ... 0 F))`; verdict: exact ordinary
  derived-category formulation.
- The universal base-change clause quantifies every `T` with `[IsNoetherian T]`,
  every `t : T ⟶ U.toScheme`, and Cartesian `XT,YT,qX,qY,bT,jT`; verdict:
  exact, with no extra dominance, finiteness, or separatedness assumptions.
- Its conclusion is `IsIso` of the actual component of
  `derivedBaseChangeMap ... sq.toCommSq` at the restricted degree-zero object;
  verdict: exact canonical exchange morphism and quantifier order.

Edge cases checked: empty `X` or `Y`, zero `F`, empty Noetherian test scheme,
identity base change, zero-dimensional and characteristic-zero bases remain
included; integrality supplies the nonempty base, and primality excludes
`ℓ = 0,1` while `hℓ` excludes exactly the characteristic. Universes are
explicit and use the established scheme `u` / coefficient `u+1` convention.

I searched Mathlib, the upstream `WeilConjectures` tree, project `lean/Sheaf`,
and the name index with alternate generic-constructibility/base-change queries;
only elementary openness and unrelated finiteness results occurred. LeanFinder
and Loogle gave no matching declaration, and LeanSearch was unavailable.
The blueprint source and all recorded dependency signatures were opened.
No mismatch, statement correction, new definition, dependency repair, or file
change was required. The existing theorem docstring contains the eight proof
steps, and the file has only the permitted theorem `sorry`.
