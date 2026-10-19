## Worker report

Repair of L's immutable-head compilation return, 2026-10-16.

`Sheaf.AlgebraicGeometry.InvertibleOrdersColimit` states
`AlgebraicGeometry.Scheme.isTorsionEtaleSheafOfFieldInvertibleOrder_iff_isIso_comparison`.
Its only theorem has proof `sorry`. The diagram, cocone and comparison have real data.
The natural statement is unchanged; no statement correction or new node is needed.

The return identified missing `invertibleTorsionIndices`,
`IsTorsionEtaleSheafOfFieldInvertibleOrder`, and then the failed comparison definition,
with unused/unreachable tactics caused by those errors. The previous dependency copy
is obsolete: the current recorded and published dependency is
`Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`. The repair imports and uses it,
removes the sandbox's obsolete FieldInvertibleTorsion module and dependency node copy,
and uses the direct recorded geometric-stalk predicate. The comparison is constructed
against this current interface, so no sibling preliminary compilation is required.

Clause-by-clause correspondence:

- Field: `(K : Type u) [Field K]`.
- A K-scheme: `{T : Scheme.{u}} [T.Over (Spec (.of K))]`.
  `Over.mk (T ↘ Spec (.of K))` packages exactly this structure for the dependency API.
- Abelian etale sheaf: `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Local torsion: `hF : F.IsTorsion`; no single annihilator is assumed.
- Invertible orders: `Etale.IsTorsionOfInvertibleOrder K
  (Over.mk (T ↘ Spec (.of K))) F`. Its full definition quantifies over every separably
  closed geometric point and stalk element, and requires a positive annihilator nonzero
  in K. Algebraically closed points give the same etale stalk criterion.
- Index: `ObjectProperty.FullSubcategory
  (fun n : PositiveNat ↦ n.val ∈ Etale.invertibleTorsionOrders K)`.
  The recorded `invertibleTorsionOrders K` is `{n : ℕ | 0 < n ∧ (n : K) ≠ 0}`.
  `PositiveNat` already has divisibility order, so the full subcategory has exactly
  one arrow for n dividing m. Positivity in both representations is proof data;
  no extra mathematical restriction occurs. In particular this does not use ℕ's
  ordinary inequality category. No private copy of the allowed-orders predicate is made.
- F[n]: `Etale.etaleNTorsion F n.obj.val`, the recorded definition of
  `kernel (n.obj.val • 𝟙 F)`.
- Transitions: canonical `kernel.lift` of `kernel.ι`, with the existing
  `torsionKernelTransition_condition`, `_id`, and `_comp` providing its laws.
  A full-subcategory arrow's `hom.down.down` is precisely the divisibility proof.
- Cocone: point F, component `kernel.ι (n.obj.val • 𝟙 F)`; naturality is the
  standard kernel lift identity.
- Colimit: `colimit (fieldInvertibleTorsionDiagram K F)` in abelian etale sheaves.
- Canonical comparison: `colimit.desc` of exactly that cocone.
- Iff and displayed equality: `↔ IsIso (fieldInvertibleTorsionComparison K F)`.
  This asserts invertibility of the prescribed comparison rather than an arbitrary map.

Dependency declarations inspected and used:

- `def-kun-torsion-invertible`: `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`,
  `AlgebraicGeometry.Etale.invertibleTorsionOrders`, `etaleNTorsion`,
  `IsTorsionOfInvertibleOrder`. Read their complete definitions and docstrings.
  The recorded derived extension remains in the dependency and is not copied.
- `def-weil-pbc-etale-sheaves`: upstream
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves`; `CategoryTheory.Sheaf.IsTorsion`
  is the existing local torsion predicate.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `Limits.Cocone`, `Limits.colimit`, `Limits.colimit.desc`.
- `def-pur-abelian-sheaf-kernel`: Mathlib `CategoryTheory.sheafIsAbelian`,
  `Limits.kernel`, `kernel.ι`, `kernel.lift`. Sheaf limits are sectionwise.
- Added landed statement dependency `def-weil-pbc-torsion-etale-sheaf` for the
  public import `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`: its `Scheme.PositiveNat`
  and the three kernel-transition lemmas are the exact existing divisibility interface.
- Mathlib `ObjectProperty.FullSubcategory` supplies the restriction of this category.
- Existing proof dependencies remain nonpublic imports:
  `Sheaf.AlgebraicGeometry.GeometricStalkColimits`,
  `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`,
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
  The first theorem uses integer-module coefficients; for the present abelian coefficients,
  `Mathlib.CategoryTheory.Sites.Point.Skyscraper` supplies the general adjunction.
  The theorem docstring retains all five proof steps and the unrestricted torsion union.

Edge cases: I_K contains 1, excludes 0, and is closed under multiplication, giving
common divisibility upper bounds. In characteristic zero all positive integers occur;
in characteristic p exactly integers prime to p occur. The zero sheaf and empty scheme
satisfy both sides. Constant nonzero Z/p in characteristic p fails both sides. Unbounded
prime-to-p torsion exponents are allowed. No finiteness, separatedness or nonemptiness of
T is assumed, nor any common annihilator. The site and geometric-point universe is u;
abelian groups have size u+1 and the fixed countable index is small.

Searches (the sandbox searches.jsonl records the tool outputs):

- Fresh LeanFinder: “A torsion abelian etale sheaf is the colimit of its n torsion kernels
  indexed by positive integers invertible in a field exactly when its stalks have
  invertible torsion orders”. Eight hits about quasicoherent stalks, smooth sheaf units,
  etale algebra loci and rank; none states this equivalence.
- Fresh Loogle: `CategoryTheory.Limits.kernel, CategoryTheory.Limits.colimit`.
  Three hits in generic Grothendieck presentability constructions, not this theorem.
- Fresh Mathlib grep: `annihilat.*colimit|colimit.*annihilat|[Tt]orsion.*[Kk]ernel|
  [Kk]ernel.*[Tt]orsion`; one unrelated number-field hit.
- Earlier LeanSearch returned Internal Server Error, recorded as unavailable.
- Fresh `rg` of upstream WeilConjectures and the project finds the current recorded
  dependency and module-valued torsion predicates. The latter have different coefficient
  categories; their colimit existence result does not give this iff for this diagram.
  The upstream node-id search has no hit.

No STATEMENT-DISPUTED flag or node fault remains. The source statement, every hypothesis,
and the canonical comparison are preserved. The repair changes the obsolete Lean
interface to the now-published recorded interface. A new independent second reader must
review this repair; the previous second-reading text applied to the returned version.

Validation: the repaired single module compiles cleanly through the prescribed
`scompile.py NK lem-kun-invertible-orders-colimit` wrapper, both as an independent
sandbox module and under its library module name. No errors or warnings remain.


## Second reading by NK

Independent reading of the repaired version, 2026-10-16. I did not write the statement.
I opened the node copy, the shared node, all statement-dependency records, the complete
InvertibleTorsionOrders and TorsionEtaleSheaf modules, the existing local-torsion
definition, and the kernel/colimit APIs. No new nodes or dependency modules are in this
delivery. The added statement dependency is already recorded and published.

Source check: the local literature payload is absent, so I read the actual blueprint
Markdown on the project server: lem-kun-invertible-orders-colimit, order 1688, and
def-kun-torsion-invertible, order 1680. The former says exactly the field/torsion-sheaf
iff in the node and specifies in its proof the divisibility subdiagram and canonical
comparison. Its opening invocation of the unrestricted torsion filtered union is retained
in the Lean proof docstring and import. I also read the server Stacks TeX at
lemma-stalk-exact (03PT), theorem-exactness-stalks (03PU), the geometric-point definition
in the stalks section, and lemma-limits-colimits-abelian-sheaves (03CO). These require an
arbitrary scheme/site, not finite type, Noetherian, separated, quasi-compact, or nonempty.
The explicit diagram and interpretation of equality in the node agree with these sources.
There is no statement_change and no source-based correction is needed.

Object, hypothesis and conclusion checklist (each verdict: exact):

- Ground field K: `(K : Type u) [Field K]`. This is a field, not a ring or an
  algebraically closed field, and the characteristic is unrestricted.
- K-scheme T: `{T : Scheme.{u}} [T.Over (Spec (.of K))]`. The term
  `Over.mk (T ↘ Spec (.of K))` passes that same scheme and structural morphism to
  the recorded dependency. It adds no condition on that morphism.
- Abelian sheaf F on the small etale site of T:
  `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`. This is precisely the
  abelian-sheaf category of def-weil-pbc-etale-sheaves, not module-valued or
  set-valued sheaves, and not the Zariski or big etale site.
- Torsion hypothesis: `(hF : F.IsTorsion)`. I read
  `CategoryTheory.Sheaf.IsTorsion` in SheafCohomology/Basic: every section becomes
  finite additive order on a covering sieve. The bound may vary with the cover and
  section. This is the node's local torsion, not torsion of every group F(U), nor a
  global bound on the exponent.
- Allowed orders I_K: the full subcategory of `Scheme.PositiveNat` satisfying
  `n.val ∈ Etale.invertibleTorsionOrders K`. I read the latter definition as
  `0 < n ∧ (n : K) ≠ 0`. In a field this is exactly invertibility of the positive
  integer. PositiveNat's `le n m := n.val ∣ m.val` gives divisibility arrows, with
  no extra arrows from the ordinary inequality ordering. Its extra positivity proof
  is redundant proof data, not an additional mathematical restriction.
- Kernel F[n]: diagram object `Etale.etaleNTorsion F n.obj.val`, whose recorded
  definition is `kernel (n.obj.val • 𝟙 F)`. I read Mathlib's kernel and kernel.ι;
  these are categorical kernels in the specified abelian-sheaf category, hence the
  sectionwise subsheaves killed by n in def-pur-abelian-sheaf-kernel.
- Inclusion for n dividing m: `kernel.lift (m.obj.val • 𝟙 F)
  (kernel.ι (n.obj.val • 𝟙 F)) ...`. The argument `hnm.hom.down.down` is the
  inherited divisibility proof. The recorded transition-condition/id/comp lemmas
  supply exactly the kernel factorization and functor laws. The map followed by
  the m-kernel inclusion is the n-kernel inclusion, so these are canonical inclusions.
- Colimit in abelian etale sheaves: `colimit (fieldInvertibleTorsionDiagram K F)`.
  Its ambient category is the same Sheaf category as F; existence is synthesized
  from the published small-site/Grothendieck colimit infrastructure, not added as
  an extra mathematical hypothesis.
- Prescribed comparison to F: `fieldInvertibleTorsionCocone K F` has point F and
  component `kernel.ι (n.obj.val • 𝟙 F)`; its naturality expresses compatibility
  with the preceding inclusion. `fieldInvertibleTorsionComparison K F` is exactly
  `colimit.desc` applied to this cocone, not an arbitrary chosen morphism.
- Orders invertible in K: the left side is the recorded
  `Etale.IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F`. I read its
  entire definition: for every separably closed geometric point and every element
  of its actual `pointSmallEtale` sheafFiber, there is a positive annihilator n
  nonzero in K. This is the node's stalkwise criterion; no common annihilator occurs.
  Separably closed points give the same small-etale stalks as their algebraic
  closures, so their use covers precisely the source's geometric-point criterion.
- Both implications and meaning of displayed equality: the single conclusion is
  `... ↔ IsIso (fieldInvertibleTorsionComparison K F)`. This is exactly the
  node's stipulated canonical-isomorphism interpretation, with no extra conjunct.

Edge cases: zero is excluded from the index, including in characteristic zero, because
only positive integers occur. One is always an index; products give common divisibility
upper bounds, so this index can never be empty. In characteristic zero all positive
integers occur; in characteristic p precisely the positive integers not divisible by p
occur. Arbitrarily large and varying annihilators remain permitted. For the zero sheaf,
all stalk elements and both conditions are trivial; over the empty scheme there is no
geometric point and the sheaf category has its unique object, so the iff remains valid.
For a nonempty characteristic-p base, a nonzero constant Z/p sheaf fails the allowed
orders condition and the canonical comparison is not an isomorphism. There is no
nonemptiness or finiteness assumption on T. The arbitrary universe u, Scheme.{u},
field Type u, and AddCommGrpCat.{u+1} follow the published small-etale size convention;
the fixed positive-integer index is small in every u. No independent lower universe
for geometric test fields has been introduced.

Independent searches, using words different from the worker's latest query:

- LeanFinder through msearch: "A sheaf of abelian groups is the filtered union of
  its annihilator subsheaves for a multiplicative set precisely when each geometric
  germ has an annihilator in that set". Eight results concern ringed-space germs,
  quasicoherent generators, or sheafification; none is this canonical comparison iff.
- Loogle through msearch: `CategoryTheory.Limits.colimit, CategoryTheory.Limits.kernel`.
  Three results are generic Grothendieck presentability constructions, not this theorem.
- Mathlib grep through msearch:
  `annihilator.*colimit|colimit.*annihilator|invertible.*torsion|torsion.*invertible`.
  Zero hits. The existing worker LeanSearch failure remains recorded as unavailable.
- Direct rg on upstream WeilConjectures and project Sheaf searched those patterns
  and torsion/colimit in both orders. I opened
  `Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit`: it takes ModuleCat
  coefficients and concludes existence of some filtered diagram of bounded-exponent
  sheaves. It does not state this iff for the specific divisibility kernel diagram.
  The current abelian AbTorsionSheaf module gives the local/stalk torsion equivalence,
  not the invertible-order kernel-colimit equivalence. The project occurrences are
  the recorded invertible-order definition and unrestricted torsion constructions.
  Thus no exact existing declaration replaces the delivered module, and all notions
  already present are reused rather than privately copied.

I also inspected the two actual proof citers, lem-kun-0f1h and lem-kun-0f1i. Both use
this canonical filtered decomposition to reduce invertible-order torsion coefficients
to F[n], which the present signature supplies. No citer audit record is required because
the mathematical statement was not changed.

H5/H6/H8/H9: the three helper definitions have real diagram/cocone/colimit data; none
contains sorry or an arbitrary Nonempty choice. The only new theorem ends in sorry.
The cocone's naturality proof is a structure law for that real construction. Every
helper and the theorem has its source and blueprint docstring. The theorem docstring
contains all five node proof steps, including the unrestricted torsion-colimit opening,
exact kernel stalks, subgroup union, preservation of the comparison, and conservativity.
All lines are at most 100 characters, no file-local notation or instance occurs, and
universe u and every variable are explicitly bound. The node's lean.statement was
checked programmatically to equal the theorem signature verbatim.

Mismatches and changes: none found in this repaired version. I preserved the Lean,
node statement, and dependency interface; the only edit is this independent second-reading
report. Validation: scompile.py compiled the sandbox and library module cleanly, with
exit code zero and no errors or warnings (23.9 s and 19.2 s respectively).
