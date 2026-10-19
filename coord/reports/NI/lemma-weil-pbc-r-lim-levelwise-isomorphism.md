## Worker report

The module `Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism`
states `CategoryTheory.isIso_derivedLimit_of_levelwise` with `sorry` as its entire proof.
No definitions or proofs are added. The source is blueprint order 1326 and its
Roos-triangle proof, clarified using Stacks Derived Categories 08TC, 0H9J and 014A.

Clause-by-clause reading of the corrected statement:

- The ambient triangulated category is `C : Type u`, `Category.{v} C`,
  `HasZeroObject`, integer `HasShift`, `Preadditive`, additive shifts,
  `Pretriangulated` and `IsTriangulated`. The object and morphism universes are independent.
- The towers are `M N : ℕ → C` and the successive maps `f` and `g`.
  Lean index `n` represents paper index `n+1`, so every positive level is included.
- Only the two products used in the statement are required, by `HasProduct M`
  and `HasProduct N`; no assumption of all countable products is imposed.
- The chosen triples are `L,p,δ` and `L',p',δ'`; `hL` and `hL'` use the
  recorded `IsDerivedLimitTriangle` to say exactly that their Roos triangles
  with middle arrow `1-shift` are distinguished.
- The component maps are `φ`; the commuting transition square is `hφ`.
  Its Lean composition order reverses the written functional order:
  `f n ≫ φ n = φ (n+1) ≫ g n`.
- Every component is invertible by `[∀ n : ℕ, IsIso (φ n)]`.
- `ψ` is any completion. The first and last triangle squares are exactly `hp`
  and `hδ`, using the categorical product map `Limits.Pi.map φ` and the shifted
  map `ψ⟦(1 : ℤ)⟧'`. The middle square follows from `hφ`; it is not an extra
  hypothesis. The conclusion is precisely `IsIso ψ`.

Dependency declarations read and used:

- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle`. The current server source was read with
  `scompile.py --source`; the older source checkout lacks this module.
- `Mathlib.CategoryTheory.Triangulated.Triangulated`: the triangulated structure,
  including `CategoryTheory.Pretriangulated` and `CategoryTheory.IsTriangulated`.
- The proof dependency `lem-weil-derived-limit-levelwise-iso` is the Mathlib leaf
  `CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃`, available through the imports.
  Its full signature and docstring were read in `Pretriangulated.lean`.
- The original dependency `Sheaf.Paper.AdicDerivedInverseLimit` was read in full:
  `AlgebraicGeometry.Scheme.AdicDerivedInverseLimit` supplies `obj,p,δ,distinguished`
  but deliberately no map or functor. Its underlying generic predicate is the one
  used here. The generic tower assertion requires no extra adic coefficient assumptions.

Edge cases: zero towers and zero objects are allowed; transitions need not be
invertible; only component maps must be invertible. No boundedness, exactness of
products or coefficient restriction is imposed. Arbitrary choices of distinguished
Roos triangles and every triangle-compatible completion are covered. Merely commuting
with the projections, without the connecting-map square, is deliberately not asserted
to suffice. Universes and variables are explicitly bound. There is no finite truncation
or omitted initial positive level.

Searches made:

- `msearch.py leanfinder`, query “A morphism of Roos triangles induced by a compatible
  levelwise isomorphism of towers is an isomorphism”: eight hits including
  `Pretriangulated.isIso₁_of_isIso₂₃`, its rotated variants, and generic cone maps;
  no theorem with this tower/derived-limit signature.
- `msearch.py loogle`, query `CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃`:
  one hit, the general distinguished-triangle five lemma, not the exact tower statement.
- `msearch.py grep`, query `IsDerivedLimitTriangle|derivedLimit.*[Ii]so` in
  `CategoryTheory`: no Mathlib hits.
- `msearch.py leansearch`, query “A compatible levelwise isomorphism induces an
  isomorphism on derived inverse limits”: unavailable, Internal Server Error.
- `rg` in the project `lean/Sheaf` and upstream `WeilConjectures` for
  `AdicDerived|adicDerived|derivedInverseLimit|Roos`, then
  `derivedLimit.*[Ii]so|IsDerivedLimitTriangle`: the adic and generic definitions,
  morphism-existence theorem, Milnor sequence material and unrelated adic base-change
  maps occur; no exact statement. Upstream `HomotopyLimit.lean` was read: `of_iso`
  transports a cone property and `exists_iso` provides an isomorphism, whereas the
  present assertion concerns every specified triangle completion.
- Searching the item id in upstream sources yielded no hit. Searching the new
  declaration name in Mathlib, upstream and `lean/Sheaf` yielded no collision.
- `rg -l` for the item id in DAG nodes, followed by JSON membership checks in
  `stmt_deps` and `proof_deps`, found exactly the citer listed below.

Validation: server-only `scompile.py NI lemma-weil-pbc-r-lim-levelwise-isomorphism`
compiled the delivered module cleanly, both sandbox and library-path passes,
with nice 19, two threads and the default 60-second per-file limit. No local compile.

## Statement corrected

Old statement, verbatim:

> If $u_n:M_n\to N_n$ is a compatible map of towers and every $u_n$ is an
> isomorphism, then $R\varprojlim u_n$ is an isomorphism.

The dependency defines a chosen Roos triangle, expressly not a functor or maps
between its choices. Consequently `R lim u_n` is not a defined morphism under the
old hypotheses. Stacks `derived.tex`, Definition `definition-derived-limit` (08TC)
and Remark `remark-functoriality-derived-limit` (0H9J), explicitly describe a
non-unique completion to a morphism of distinguished triangles. The blueprint's
proof likewise takes fibres in the homotopy-limit triangles. The corrected statement
spells out that interpretation and quantifies over every such completion. It does
not choose a completion, assume a functor or claim uniqueness. This is an auxiliary
lemma, not the statement of the blueprint unit `sk-thm-properbasechange`.

The statement dependencies now explicitly name the generic derived-limit notion
and triangulated category in place of the adic specialization. The proof and its
dependencies were adjusted to remove the old claim that the adic definition itself
induces a map; the product-map and triangle five-lemma argument is unchanged.
All old fields are preserved in `statement_change` as required.

Every citer:

- `lemma-weil-pbc-completed-exchange-coherence`: holds true. Its proof uses a specified
  functor on strict derived towers and its compatible reconstruction comparisons;
  the resulting comparison is a morphism of the Roos triangles. The corrected lemma
  applies to this specified map. It does not supply the functoriality that the citer
  already obtains separately from `prop-weil-pbc-rlim-functoriality`.

No citer was edited. No disputed statement remains.

## Second reading by NI

Read the corrected statement first against Stacks `derived.tex`, Definition
`definition-derived-limit` (08TC), Remark `remark-functoriality-derived-limit`
(0H9J), and the original blueprint order 1326 statement and proof. The source
assumes only a triangulated category and existence of the tower products. Its
completion is non-unique. The correction makes the undefined notation for the
map explicit exactly as used by the blueprint's fibre argument; it does not
replace a canonical strict-model map by an arbitrary unrelated map.

Object/hypothesis/conclusion checklist, with Lean counterparts and verdicts:

- Ambient triangulated category: `{C : Type u} [Category.{v} C]`, zero object,
  integer shift, preadditivity, additive shifts, `Pretriangulated` and
  `IsTriangulated`. Read the dependency node's Mathlib match and both structure
  declarations: these give TR1--TR4 and additivity. Exact; no stronger category
  assumption and no relation between object and morphism universes.
- Two sequential towers: `{M N : ℕ → C}`, `f n : M (n+1) ⟶ M n` and
  `g n : N (n+1) ⟶ N n`. Reindex source positive level n+1 by Lean n.
  Exact; all positive levels and every successive transition are present.
- Existence of the two products: `[HasProduct M] [HasProduct N]`. Exact;
  existence of products for unrelated towers is not required.
- Chosen derived limits and their structure: `L L'`, `p p'`, `δ δ'`, `hL hL'`.
  Read the current server `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
  via `scompile.py --source`: `IsDerivedLimitTriangle` is precisely
  `Triangle.mk p (towerTransitionEndomorphism f) δ ∈ distTriang C`.
  Read the transition module by the same server-source mechanism: its real data
  is `𝟙 _ - Pi.lift (fun n => Pi.π K (n+1) ≫ f n)`. Exact object, sign and maps;
  no hollow data or second definition. Also read the original adic dependency:
  its `distinguished` field uses precisely this generic predicate.
- Compatible level maps: `φ : ∀ n, M n ⟶ N n` and
  `hφ : ∀ n, f n ≫ φ n = φ (n+1) ≫ g n`. Exact source equation with Lean's
  left-to-right composition; products therefore commute with `1-shift`.
- All level maps invertible: `[∀ n : ℕ, IsIso (φ n)]`. Exact; no assumption
  on the transitions or on the derived-limit map is introduced here.
- Every specified completion: `(ψ : L ⟶ L')`,
  `hp : ψ ≫ p' = p ≫ Limits.Pi.map φ` and
  `hδ : δ ≫ ψ⟦(1 : ℤ)⟧' = Limits.Pi.map φ ≫ δ'`. Exact outer squares of the
  morphism of Roos triangles. The middle square follows from `hφ`.
  Binders quantify over every completion, not merely some chosen completion.
- Conclusion: `IsIso ψ`. Exact invertibility of that very map, rather than
  existence of an unspecified isomorphism between the objects.

Edge cases: the source index is always the positive integers, so an empty index
set is not among its cases; Lean zero is exactly its first positive level.
Zero towers, zero limits and identity level maps are allowed. Neither boundedness,
coefficient characteristic, schemes, Noetherian hypotheses nor nonempty schemes
occur. The empty scheme can supply a zero category without exclusion. Independent
`u v` remain unrestricted; all variables and universes are explicitly bound.

Independent searches used different words from the worker: `msearch.py leanfinder`
“A homotopy inverse limit triangle map whose tower components are invertible is
invertible” returned eight mapping-cone and triangle-isomorphism results, no exact
signature. `msearch.py loogle` on
`CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃` returned the general triangle
five lemma, whose full local signature and docstring I read. `rg` for
`IsHomotopyLimit`, `isIso.*Limit`, `Limit.*Iso`, and `IsDerivedLimitTriangle` in
Mathlib triangulated files, upstream triangulated files and project modules
found no exact existing assertion. In particular I opened upstream
`HomotopyLimit.lean` and `HomotopyLimit/Basic.lean`: `of_iso` assumes an isomorphism
on cone points, `exists_iso` supplies some isomorphism, and `isIso_of_proIso`
requires shifted inverse data and uses arbitrary limit fans; none is this
levelwise-isomorphism signature. The last is a more general tool, not a duplicate
of the exact statement. The existing DAG proof dependency records the general
Mathlib five lemma as a specialization ingredient, not a separate Lean tower
assertion. The delivered theorem adds no definition. There are no new nodes or
dependency modules to audit.

Independently enumerated all DAG JSON files for membership of the item in
`stmt_deps` or `proof_deps`: exactly one citer exists, so two cannot be opened.
Opened that citer, `lemma-weil-pbc-completed-exchange-coherence`, and read its
statement and full proof, especially steps 3--6. Its step 4 applies the strict
derived-tower Rlim functor to compatible invertible coordinate changes, and
step 5 retains the canonical comparisons on strict models. The resulting map
is a Roos-triangle completion; `holds: true` is correct. No citer was edited.
The node's `statement_change.old_statement` agrees verbatim with the original
node, and its complete one-citer audit is correct.

No mathematical or Lean mismatch found; left the Lean and node unchanged.
Only this independent second-reading section was added. The module/declaration
source and blueprint docstrings contain the product-map commutation, component
inverse and distinguished-triangle five-lemma proof steps. The only proof is
`sorry`; there are no definitions, private abbreviations or local instances.
Verified programmatically that `lean.statement` is verbatim the file signature
and every Lean line has at most 100 characters. Server compilation is performed
with `scompile.py`, default 60 seconds per file, nice 19 and two threads.
