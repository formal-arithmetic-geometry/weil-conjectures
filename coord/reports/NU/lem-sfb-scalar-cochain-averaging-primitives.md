## Worker report

The module `Sheaf.Analysis.ScalarCochainAveragingPrimitives` states
`WeilConjectures.scalar_cochain_averaging_primitives`, with one `sorry`, and supplies
its two real coordinate helpers `scalarCochainDifferential` and
`scalarCochainLastSlice`. No node statement or dependency list changed. No new nodes
or dependency modules were needed. The source is the node's agent-formulated analytic
expansion of main-20261015 direct-image stability, paragraph (3); the actual blueprint
paragraph was opened and supplies geometric motivation only. Its WANTED exact analytic
reference remains WANTED, as recorded in the source node.

Hypothesis and clause correspondence:

- The prime is `ell : ℕ` with `[Fact ell.Prime]`. The coefficient field is
  `V : Type v` with `[NormedField V]`; `iota : Padic ell →+* V` and
  `hiota : Isometry iota` express the isometric Q_ell embedding. `hultra` is exactly
  the ultrametric triangle inequality. No completeness occurs in the finite assertion.
- The profinite group is `G : Type u` with group, topology, topological-group,
  compactness and Hausdorff instances. `hbasis` gives an open normal subgroup inside
  every open identity neighbourhood. `hprime` asserts coprimality for every open-normal
  quotient; these are finite by compactness and openness and exhaust continuous finite
  quotients up to the quotient by the kernel. No separate finiteness assumption is added.
- Independent explicit universes `u v w` implement the size convention. All parameters
  `P : Profinite.{w}` are compact Hausdorff spaces with clopen basis. No nonemptiness
  assumption is imposed on P, including for continuous changes of parameter.
- `C(P × (Fin r → G), V)` is precisely the full continuous cochain space, with its
  compact-domain supremum norm. The coordinate helper `scalarCochainDifferential`
  uses the trivial coefficient action. Its first term omits g_1; the summands indexed
  by `j.val < r` merge adjacent group entries with exponent j+1; the j=r term drops
  the last entry and has exponent r+1. This is the node's entire displayed formula.
  For r=0 it is c(s,empty)-c(s,empty)=0, exactly d^0=0. No action is left unspecified.
- Positive degree is indexed as n+1, for all `n : ℕ`. `cbar` is the descended cochain
  on P times (G/U)^(n+1). The factorization equation and vanishing differential are
  the two antecedents of the finite clause. Assuming continuity of cbar loses no case:
  the finite discrete quotient permits choosing a lift of each tuple, so each slice
  is continuous in P and the entire descended function is continuous.
- The finite conclusion supplies continuous b and bbar. Its first equation is exactly
  (-1)^(n+1)/|G/U| times the last-variable sum; `Fin.snoc` appends that variable.
  `∑'` is the finite sum on the intrinsically finite quotient, with no chosen Fintype
  instance. Its next equation states factorization through the same U. The last two
  clauses state db=c and the supremum-norm contraction, respectively.
- The complete assertion starts with `∀ [CompleteSpace V]`. It accepts exactly a
  continuous V-linear integral I with the normalization, norm bound, two translation
  invariances and finite-quotient formula of the recorded dependency. This makes no
  arbitrary choice of integral: the assertion holds for every such I, including the
  integral furnished by that dependency. Its continuity is already part of `→L[V]`.
- The conclusion gives a family H of V-linear maps in all positive degrees and for
  every profinite P. The displayed equality determines every value by
  `(-1)^(n+1) * I (scalarCochainLastSlice n c s g)`. The slice helper is the actual
  continuous h ↦ c(s,Fin.snoc g h), constructed directly, without choice or sorry.
  Thus these are exactly the fibrewise maps in the node; a point parameter gives
  h_{V,G}^{n+1} on C(G^(n+1),V). Continuity of outputs is built into their `C` type.
- The next clause is the norm bound for every cochain, not only cocycles. The next
  equality is C(P,V)-linearity through pointwise multiplication and the projection
  to P; addition is already included by `→ₗ[V]`. The next equality is naturality for
  every continuous a : P' → P, using a times the identity on the group tuple.
- The last clause says d(Hc)=c for every cocycle in every parameter family.
  Consequently all asserted unparametrized contractions and parametrized conclusions
  are present. There is no locally constant or finite-quotient restriction in the
  complete part.

Dependency declarations read and used:

- `Mathlib.NumberTheory.Padics.PadicNumbers`, `Padic` (full definition and completion
  docstring), the `mathlib_match` of `def-weil-l-adic-numbers`.
- `Sheaf.Analysis.PrimeToEllCompleteScalarIntegral`,
  `WeilConjectures.primeToEll_completeScalar_integral`: opened its entire signature and
  proof-plan docstring. Imported publicly; its exact integral interface is used in the
  complete clause, including finite-quotient normalization. The helper needs no private
  reconstruction of its integral. The parameter family is characterized pointwise,
  so continuity and linearity follow from the dependency's parameter clause.
- `def-weil-size-convention` is explicitly a metatheoretic convention with no module or
  declaration. Explicit independent universe binders implement it here.
- Proof dependency `lem-sfb-finite-quotient-contractive-average` was read. It has no Lean
  record or Mathlib match at this base, so there is no stated module to import. It is
  cited in the theorem docstring as the finite-averaging proof input. Its notion is not
  used in the statement: the finite primitive is specified by the actual quotient sum.
- `Mathlib.Data.Fin.Tuple.Basic`, `Fin.contractNth` and `Fin.snoc`, give the actual
  coordinate operations. Both definitions and their docstrings were read. The full
  algebraic differential in Mathlib `inhomogeneousCochains.d` was also read: it takes
  bundled algebraic representations and forces group and coefficient into one universe;
  the coordinate helper here applies to arbitrary independent universes and parameters,
  using that same contractNth formula. It adds no second continuous cohomology theory.

Edge cases checked before writing:

- Degree one: the cocycle equation is c(h)-c(gh)+c(g)=0. Averaging cancels the first
  two terms, so c=0. Its primitive is zero and d^0=0, consistent with both clauses.
- Empty P: both continuous function spaces are zero; the norm is zero. P or P' may be
  empty in the naturality assertion as well. No Nonempty instance excludes these cases.
- Trivial group and trivial quotient: quotient order is one, the signed average is the
  signed identity on constants. The differential alternates zero and identity, giving
  the claimed identity for every actual positive-degree cocycle.
- Noncomplete V: the finite formula and finite sum need no limiting operation; `tsum`
  on a finite type is the finite sum even without completeness. Only the second clause
  introduces `[CompleteSpace V]`.
- Nonabelian G: adjacent entries multiply in the specified order and translation in
  the last averaged coordinate is on the left. No commutativity assumption is imposed.

Searches for an existing statement (prescribed msearch wrapper, group NU and this item):

- LeanFinder: "Trivial continuous group cochains admit a norm one contraction by averaging
  the last argument with a normalized invariant nonarchimedean integral". Eight hits,
  including `ContinuousCohomology.const`, `continuousCohomologyZeroIso`,
  `MultiInd.d_zero`, `kerHomogeneousCochainsZeroEquiv`, and `MultiInd.complex`.
  These are cohomology definitions and degree-zero facts, not the averaging statement.
- Loogle: `"ContinuousCohomology", "homotopy"`. Zero hits.
- Mathlib grep: `(averag|integral).*(cocycle|cochain)|(cocycle|cochain).*(averag|integral)`.
  Zero hits.
- LeanSearch: "Averaging over a finite group or a profinite group gives continuous bounded
  primitives for trivial coefficient cocycles with compact parameters". Eight hits:
  `Representation.averageMap`, Haar integral continuity, `groupCohomology.cocycles`,
  continuous-cohomology structures, and finite/profinite-group constructions. None gives
  the signed scalar primitive with these nonarchimedean estimates and parameter clauses.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` with the same averaging/cochain
  pattern and the item id. The parent finite-quotient comparison's proof plan mentions
  averaging, but its theorem states a derived comparison, not this node. Other hits are
  unrelated cohomology or tensor comparison modules. Searched the intended new names
  in both source roots and `dag/lean_names_upstream.json`; no collision was found.
- Opened `Sheaf.CategoryTheory.PrimeToEllCochainFiniteQuotientDescent` and read its
  coordinate presentation and finite-quotient predicate. This is a downstream consumer;
  it is not imported, so no dependency cycle is introduced.

Validation: the prescribed scompile wrapper compiled the module twice (sandbox check and
library module), both clean in 1.7 seconds. Every variable and universe is explicitly
bound; autoImplicit is disabled. Only the main theorem is postponed, with the four-step
natural-language proof plan in its docstring. No STATEMENT-DISPUTED issue or node fault
was found. The independent maintainer review is the review required by the dispatcher.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
