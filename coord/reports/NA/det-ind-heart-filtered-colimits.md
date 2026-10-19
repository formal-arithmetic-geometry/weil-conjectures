## Worker report

Delivered module: `Sheaf.Paper.IndConstructibleFilteredColimits`.
Its two theorems state the filtered-colimit and arbitrary-direct-sum assertions for finite
E and for the condensed algebraic closure, respectively. Both proofs are `sorry`.
There are no new definitions, new nodes, dependency modules, or proved results.
The source's implicit setting is made explicit by the statement correction below.

Hypothesis and clause correspondence, applicable to both declarations:

| Source hypothesis or clause | Lean rendering |
| --- | --- |
| A prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| A field k of positive characteristic p different from ell | `(k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)` |
| A separated scheme X of finite type over k | `(X : Scheme.{u}) [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]` |
| Finite E inside a fixed algebraic closure of the ell-adic field | `(E : PadicAlgCl.FiniteIntermediateField ℓ)` in the first theorem; this upstream subtype includes finite dimensionality |
| Lambda = E | `Profinite.continuousMapRingObj E`, using E's restricted topology |
| Lambda = Qlbar | `Profinite.padicAlgClRingObj ℓ` in the second theorem; this is the finite-subextension-valued sheaf, not all continuous functions into Qlbar |
| Lambda_X pulled back from the point | `condensedRingObj Λ X` |
| Ambient category Mod(X_proet, Lambda) | `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)` |
| Cons with finite constant scalar models | The dependency's `IsConstantModelConstructible Λ X` |
| IndCons = actual small filtered colimits of constructibles, up to isomorphism | `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)` |
| A small filtered diagram (B_lambda) | First conjunct: `∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] (B : I ⥤ ...)` |
| Every B_lambda belongs to IndCons | First conjunct's `∀ i : I, ObjectProperty.ind.{u + 1} ... (B.obj i)` |
| B is its colimit in the ambient module category | `(c : Cocone B), IsColimit c → ...`, with B represented by `c.pt` |
| Its colimit belongs to IndCons | First conjunct's conclusion `ObjectProperty.ind.{u + 1} ... c.pt` |
| Arbitrary small family of ind-constructible objects | Second conjunct: `∀ (S : Type (u + 1)) (B : S → ...)`, and `∀ s : S, ObjectProperty.ind.{u + 1} ... (B s)` |
| Direct sum computed in the ambient module category | `(c : Cofan B), IsColimit c → ...` |
| The direct sum is ind-constructible | Second conjunct's conclusion `ObjectProperty.ind.{u + 1} ... c.pt` |

The cocone/cofan form quantifies over any chosen ambient colimit and makes the statement
independent of implementation choices for colimits. In an abelian module category the
coproduct is the direct sum. No existence or exactness assertion is added to this node.
Index objects and arrows are both small in `u + 1`, the coefficient-sheaf universe,
not an unrelated independent index universe. The small pro-etale site retains its
object/morphism size difference. Every universe and variable is explicitly bound;
`autoImplicit` is disabled. There are no local definitions, local instances, or local notation.

Dependency declarations read and used:

- `sk-def-sfb-constructible`: module `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`. Read the entire module,
  including `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`, and
  `ConstantModelConstructible`. This is the dependency's newly recorded exact
  finite constant-model convention; the older arbitrary-local-matrix predicate is not used.
- `sk-def-sfb-condensed-ring`: its closed upstream audit supplies
  `Profinite.continuousMapRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`; read its
  full signature and surrounding sheaf construction. The finite-subfield condensed
  sheaf is the same continuous-function sheaf, with the induced topology.
- `sk-def-sfb-qlbar-condensed`: its closed upstream audit supplies
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`, module
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. Read the whole
  source using `scompile.py --source` and the side framework source. The subtype
  of finite-subextension-valued maps is essential here.
- `sk-def-sfb-module-objects`: its closed upstream audit names Mathlib's
  `CategoryTheory.ModObj`, `CategoryTheory.Mod`, `CategoryTheory.Mod.regular`, and
  `CategoryTheory.Mod.forget`, in `Mathlib.CategoryTheory.Monoidal.Mod`.
  Read the action, bundled module and module-hom signatures and docstrings.
- The pulled-back ring is the existing
  `AlgebraicGeometry.ProEtale.condensedRingObj` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, read in the side framework.
- Mathlib's `CategoryTheory.ObjectProperty.ind`, module
  `Mathlib.CategoryTheory.ObjectProperty.Ind`, is applied directly. Its definition
  existentially quantifies over a small filtered category and a `ColimitPresentation`
  of the object with all diagram objects satisfying the supplied predicate.
  Its existing isomorphism-closure instance confirms that the replete convention
  is built in. There is no project-specific duplicate IndCons definition.

Both proof dependencies, `det-ind-heart-canonical-presentation` and
`sk-lem-coefficient-heart`, have no Lean record and no upstream closed declarations.
Their statements and source proofs were read. They are only proof inputs, so the
statement needs no missing prerequisite module. Their imports must be added when
those nodes acquire modules. Both theorem docstrings give the full four-step proof:
essential smallness of K, all three filteredness tests (including parallel-arrow
base equalization), the inverse cocone correspondence, and finite-product/finite-subsum
presentations of sums, with the named DAG inputs.

Edge cases checked before writing:

- A filtered category is nonempty by Mathlib's `IsFiltered`; the first assertion
  imposes no extraneous nonempty hypothesis beyond filteredness.
- Empty direct sums are included because `S` has no `Nonempty` binder. The finite-subset
  poset still has the empty subset; the empty finite-product presentation has a
  one-object index and the zero constructible sheaf.
- Zero modules and the empty scheme are not excluded by the binders or membership predicate.
- General filtered categories with parallel arrows are included by `SmallCategory I`;
  no directed-poset specialization was substituted.
- E = Ql is included as the bottom finite intermediate field. Qlbar is handled by a
  separate declaration using its actual condensed coefficient ring.
- Non-Noetherian and non-quasi-compact X are not silently claimed: the explicit
  standing setting is recorded below, including the affected broader consumers.

Searches made, all with the prescribed `msearch.py NA det-ind-heart-filtered-colimits`:

- `leanfinder`, query `Ind-constructible module sheaves are closed under filtered colimits and arbitrary direct sums`:
  generic condensed-module AB5 and colimit instances and sheaf finite-presentation results;
  no theorem about this constructible module predicate.
- `loogle`, query `"isIndObject_colimit"`: `CategoryTheory.Limits.isIndObject_colimit`.
  Its signature concerns presheaf ind-objects, not these internal-module sheaves.
- `grep`, query `IndCons|IndConstructible|isIndObject_colimit`, subdirectory `CategoryTheory`:
  four generic Indization hits, no exact statement.
- `leansearch`, query `Ind constructible sheaves closed under filtered colimits and arbitrary coproducts`:
  generic Ind/presheaf/sheaf-colimit results; no exact node match.
- `leansearch`, query `Objects isomorphic to small filtered colimits of objects satisfying a predicate in a category`:
  found `CategoryTheory.ObjectProperty.ind` and its generic lemmas. Read its full source;
  reused this definition directly instead of adding a notion node.
- `loogle`, query `"ObjectProperty.ind"`: six hits, including the definition and
  `ind_ind`. The latter requires a finite-presentability theorem for the predicate;
  it does not itself state our sheaf theorem or its sum clause.
- `grep`, query `filteredColimitClosure|IndCons|IndConstructible`, subdirectory
  `CategoryTheory/ObjectProperty`: zero hits under these spellings; this was not
  taken as absence evidence after the successful `ind` search.
- `rg` for `IndCons|indCons|IndConstructible|indConstructible` in the upstream
  source, side `lean/Sheaf`, and side `lean/WeilConjectures`: no exact declaration.
  A broader case-insensitive search found unrelated torsion constructible-generation
  theorems. The node-id/declaration-name search in the source and upstream name table
  likewise found no exact existing theorem.
- `tools/blueprint_refs.py search IndCons` found 25 blueprint nodes using the notion,
  principally this unit's details. No separate definition with a usable declaration
  needs to be duplicated. `ancestor` identifies this detail node as its own blueprint ancestor.

Validation: the delivered module passed `scompile.py` both as an isolated sandbox file
and under its library module path with no errors or warnings. The initial compilation
identified the scheme finite-type encoding (`LocallyOfFiniteType` plus `QuasiCompact`)
and the required upstream `CategoryTheory.Obj` scope; both were repaired.
No `STATEMENT-DISPUTED` claim remains about the corrected statement.

## Statement corrected

The old statement was:

> Let $\Lambda=E$ or $\Qlb$. If $(B_\lambda)_{\lambda\in I}$ is a filtered diagram in $\IndCons(X,\Lambda)$,
> then its colimit $B$ in $\Mod(X_{\mathrm{proét}},\Lambda)$ lies in $\IndCons(X,\Lambda)$. Arbitrary direct sums
> of objects of $\IndCons(X,\Lambda)$ lie in $\IndCons(X,\Lambda)$.

The correction introduces X and states the implicit geometric and size conventions,
the condensed coefficient cases, and the parent's actual-colimit definition of IndCons.
It leaves both closure assertions intact. This is a detail node, not the parent unit's
own statement. The source is the current blueprint's
`sec-six-functors-basics/sk-prop-ind-heart/sk-prop-ind-heart-filtered-colimits.md`, both
assertions, together with the parent's `_section.md` definition of IndCons.
The same chapter's `sk-lem-coefficient-heart/_section.md` explicitly says X is a standing
scheme; `sk-def-sfb-dc-setting/_section.md` specifies that setting as separated finite-type
schemes over a positive-characteristic field different from ell. The current
`det-ind-heart-canonical-presentation` statement uses exactly that setting, so the
recorded proof now has matching input hypotheses. This is not a counterexample claim.

A complete parse of all DAG files for `stmt_deps`/`proof_deps` references found exactly
five citers. Each was read, including its use of this result:

- `det-ind-heart-extensions`: **holds false** as presently stated. Its arbitrary
  Noetherian X need not admit the standing finite-type field structure. Its final
  filtered-colimit step cannot invoke the scoped result without a broader interface.
- `sk-lem-proper-heart-bound`: **holds true**. Its explicit standing field setting
  applies on both X and Y; the sum and membership conclusions remain available.
- `det-proper-heart-bound-indcons`: **holds true**. X and Y are explicitly separated
  finite-type schemes over the required field, and its two sum uses match.
- `det-ind-heart-grothendieck`: **holds true in the inherited standing setting**.
  This sibling detail of the same unit retains the implicit setting; the finite and
  arbitrary sum uses keep exactly their conclusions there.
- `det-ambient-ind-derived-sums`: **holds false** as presently stated. It explicitly
  permits any scheme X and lacks the hypotheses of this scoped closure statement.
  Its cohomology-sum membership step therefore needs a broader result or scope repair.

No citer was edited. The node copy changes only `statement`, `statement_change`, and
`lean`; the original proof, proof dependencies and statement dependencies remain intact.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
