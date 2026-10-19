## Worker report

The module `Sheaf.AlgebraicTopology.TwistedArrowJoinHorn` states exactly
`lem-coef-twisted-arrow-join-horn`. Its only theorem,
`SSet.Enhanced.twistedArrow_join_horn_filtration`, has proof `sorry`, as required
in stage 2. The helper `SSet.Enhanced.twistedArrowJoinHorn` constructs the domain
introduced in this very statement using actual Mathlib faces and lattice unions;
it contains no postponed data or proof. No independent new notion or dependency
repair is needed, and no statement was corrected or disputed.

Source checked: Kerodon, Proposition the project server, proof,
<https://kerodon.net/tag/03JT>. Its parameter is `i = n - k`; its basic subsets
give exactly this initial subcomplex. The seven proof steps of the DAG are
included in the theorem docstring, including the degreewise support argument,
the primary/secondary ordering, the missing-facet arguments, the pushout
universal property and the final weak-saturation argument.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean expression and meaning |
| --- | --- |
| Simplicial sets, standard simplices and horns | `SSet.{u}`, `Δ[d]`, `Λ[d, e]`, from the existing dependency and Mathlib imports. Universe `u` is explicit and unrestricted. |
| `n ≥ 1` | `(n : ℕ) (hn : 1 ≤ n)`. |
| `0 ≤ k < n` | `(k : ℕ) (hk : k < n)`; natural numbers supply the lower bound. |
| Ordered set `bar n < ... < bar 0 < 0 < ... < n`, with nerve identified with the standard simplex | Ambient `Δ[2 * n + 1]`, enumerated increasingly by `bar j ↦ n - j`, `j ↦ n + 1 + j`, as specified in the module and definition docstrings. This is the node's stipulated identification, so no extra nerve equivalence is assumed. |
| Spanned faces `Δ^S` | Existing `SSet.stdSimplex.face`, which contains precisely the monotone maps whose image lies in its finite vertex set. |
| First pure block face | `stdSimplex.face (Finset.univ.filter (fun v : Fin (2 * n + 2) ↦ v.val ≤ n))`. |
| Second pure block face | The same face construction with filter `n < v.val`. |
| Delete the pair `bar j,j` for every `0 ≤ j ≤ n`, `j ≠ k` | Supremum over `(j : Fin (n + 1)) (_ : j.val ≠ k)` of the face filtered by `v.val ≠ n - j.val ∧ v.val ≠ n + 1 + j.val`. |
| Union of those faces, named `H_{n,k}` | `twistedArrowJoinHorn n k`; the two binary suprema and indexed supremum are unions of subcomplexes in all degrees. |
| A finite filtration `A₀,...,Aᵣ` | Existential `(r : ℕ) (A : Fin (r + 1) → (Δ[2 * n + 1] : SSet.{u}).Subcomplex)`. |
| Inclusions in the filtration | `(hA : Monotone A)`; the adjacent inclusion is `Subcomplex.homOfLE (hA (Fin.castSucc_le_succ a))`. |
| Starts at `H_{n,k}` | `A 0 = twistedArrowJoinHorn n k`. |
| Ends at the full nerve | `A (Fin.last r) = ⊤`. The top subcomplex is the full ambient standard simplex. |
| Every adjacent inclusion | `∀ a : Fin r`, with source stage `a.castSucc` and target stage `a.succ`. |
| Is a pushout of one horn inclusion | Existential attaching maps `f : Λ[d,e] ⟶ A a.castSucc`, `g : Δ[d] ⟶ A a.succ`, with `IsPushout f Λ[d,e].ι (Subcomplex.homOfLE ...) g`. Its left vertical map is exactly the canonical horn inclusion and right vertical map is exactly the filtration inclusion. |
| `d_a ≥ 2` and `0 < e_a < d_a` | `(d : ℕ) (e : Fin (d + 1))` with `2 ≤ d ∧ 0 < e.val ∧ e.val < d`. |
| In particular, the specified initial inclusion is inner anodyne | Final conjunct `innerAnodyneExtensions (twistedArrowJoinHorn.{u} n k).ι`. This refers to the canonical inclusion of the constructed domain into the ambient simplex. |

Dependency interfaces read and used:

- `def-cbc-enhanced-diagrams-cones`: module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, recorded main declaration
  `SSet.Enhanced.coneCategory`. Its module explicitly uses the existing Mathlib
  `SSet`, `stdSimplex` and `horn`; those are precisely the portion of this
  dependency needed here. No cone construction is required by the statement.
- `lem-coef-infinity-pushout-join-saturation`: module
  `Sheaf.AlgebraicTopology.PushoutJoinSaturation`, declaration
  `SSet.Enhanced.pushout_join_weak_saturation`. Its definition
  `SSet.Enhanced.WeaklySaturated` and its use of Mathlib's
  `SSet.innerAnodyneExtensions` give the common inner-anodyne convention.
  This statement uses that very Mathlib morphism property. Its proof plan uses
  the saturation closure described by the dependency; no second definition is
  introduced. Both statement/proof dependency modules are imported publicly.
- Mathlib `SSet.stdSimplex.face`, `SSet.Subcomplex.homOfLE`,
  `SSet.Subcomplex.ι`, and `CategoryTheory.IsPushout` were read at their full
  signatures. `IsPushout` is imported explicitly to state the individual cells.

Edge cases checked before finalizing:

- `n = 0` has no allowed `k`; the binders match this without imposing an extra
  condition. Every natural `k < n`, including `k = 0` and `k = n - 1`, is covered.
- For `n = 1, k = 0`, the initial faces form the spine of `Δ[3]`. The four
  attached vertex sets, in one valid order, are `{1,2,3}`, `{0,1,2}`, `{0,1,3}`,
  `{0,1,2,3}`; distinguished vertices are respectively `2,1,1,1`. Thus the
  attachments include all three required triangles and the final tetrahedron.
- An exhaustive finite support calculation for every `1 ≤ n ≤ 4`, `0 ≤ k < n`
  checks inner distinguished vertices, all horn intersections and final
  coverage. Counts are 4, 16, 52 and 160 cells respectively, for each allowed
  `k`. The computation compares every nonempty vertex subset at each stage.
- Degenerate simplices are included by `stdSimplex.face`; no restriction to
  nondegenerate simplices occurs in the Lean statement. The docstring explains
  the section-of-image argument extending the support calculation to all degrees.
- The filtration representation permits `r = 0`, just as a finite filtration
  should; the endpoint requirements still force equality of its endpoints.
  `Fin r` then has no adjacent step. No arbitrary nonemptiness, strictness,
  finite universe restriction, or choice of a noncanonical comparison is added.

Searches for existing statements and constructions:

- `msearch.py` LeanFinder query
  `paired vertex deletion faces of simplex finite filtration pushouts inner horn inclusions twisted arrow join inner anodyne`:
  eight hits, including `SSet.horn.multicoequalizerDiagram`, the three
  two-dimensional horn pushouts, `SSet.horn.faceι`, and `SSet.horn_eq_iSup`.
  These describe ordinary horns, not this paired-face domain or its filtration.
- `msearch.py` Loogle query
  `SSet.innerAnodyneExtensions, SSet.horn, CategoryTheory.IsPushout`: zero hits.
- `msearch.py` LeanSearch query
  `twisted arrow join paired faces inner horn finite filtration`: eight hits on
  filtered comma categories, fibrations, and horn-face composition identities;
  none is the desired statement.
- `msearch.py` grep query
  `paired|twistedArrow|twisted_arrow|join.*horn|horn.*join|Finite.*Filtration`
  in `AlgebraicTopology`: three hits in `AnodyneExtensions/RelativeCellComplex`
  about jointly surjective horn maps; none supplies the required domain or
  finite filtration. The general inner-anodyne property in `Inner/Basic.lean`
  was read and reused.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for the same
  concepts finds `TwistedArrowLeftFibration` citing this item as a proof input,
  but no existing statement of the paired-face filtration. The source's ordinal
  operators belong to that parent theorem and are not needed after the present
  node's explicit identification with `Δ[2*n+1]`.
- `grep -rn` for this node id in upstream `WeilConjectures` finds no declaration.
  Searches for `twistedArrowJoinHorn`, `twistedArrow_join_horn_filtration` and
  `twisted_arrow_join_horn` across Mathlib, upstream `WeilConjectures`,
  project `lean/Sheaf` and `dag/lean_names_upstream.json` find no name collision.

Validation: the required `scompile.py Q28 lem-coef-twisted-arrow-join-horn`
invocation compiled this module separately, with no errors or warnings.
Only the item's `lean` field is changed, and its signature is recorded verbatim.

## Second reading by Q28

I independently opened the sandbox node and Lean module, both dependency nodes
and their recorded modules, and the online Kerodon source at
<https://kerodon.net/tag/03JT>, Proposition the project server, including its complete proof.
This source is Kerodon, not Stacks; there is no Stacks .tex place for this item.
Its combinatorial construction assumes exactly `0 < i ≤ n`. The substitution
`i = n - k` is equivalent to the node's range. The surrounding inner fibration
is used to apply this combinatorial result and is not a hypothesis of it.
There is no maintenance repair note for this item and no `statement_change`.

My object/hypothesis/conclusion checklist, written from the node before
assessing the Lean, is as follows. Each row has verdict **matches**.

| Node item | Lean rendering and independent check |
| --- | --- |
| Simplicial sets and their standard simplices and horns | `SSet.{u}`, `Δ[d]`, and `Λ[d,e]` are the Mathlib notions publicly used by `EnhancedDiagramsCones`. They are not private replacements. |
| Natural number `n ≥ 1` | `(n k : ℕ) (hn : 1 ≤ n)` introduces the same parameter and bound. |
| Natural number `0 ≤ k < n` | `(hk : k < n)`; the lower bound follows from `k : ℕ`. No additional hypothesis or typeclass is imposed. |
| The ordered set `J_n` and its identified nerve | `(Δ[2 * n + 1] : SSet.{u})` uses the identification stipulated by the node. Its increasing enumeration is `bar j ↦ n-j`, `j ↦ n+1+j`; these exhaust exactly `Fin (2*n+2)` in the specified order. |
| Spanned faces of nonempty vertex subsets | `stdSimplex.face` is Mathlib's subcomplex of simplices whose vertex image lies in the given finite set. I read its definition and `mem_face_iff` in `StdSimplex.lean:282,289`. |
| First pure block | The filter `v.val ≤ n` in `twistedArrowJoinHorn` gives exactly the barred vertices. |
| Second pure block | The filter `n < v.val` gives exactly the unbarred vertices. |
| Delete `bar j,j` for every `0 ≤ j ≤ n`, except `j = k` | The indexed supremum over `j : Fin (n+1)` and `j.val ≠ k` deletes precisely `n-j.val` and `n+1+j.val`. Natural subtraction does not truncate in this range. |
| Union defining `H_{n,k}` | Both `⊔` operations and the indexed supremum are the lattice unions of subcomplexes, so `twistedArrowJoinHorn n k` is the prescribed domain in every degree. |
| A finite chain of subcomplexes | `∃ (r : ℕ) (A : Fin (r+1) → ...Subcomplex) (hA : Monotone A)` gives exactly a finite filtration in the ambient simplex. Monotonicity expresses the displayed inclusions, without an extra strictness condition. |
| Initial stage equals the prescribed domain | `A 0 = twistedArrowJoinHorn n k`. |
| Final stage equals the full nerve | `A (Fin.last r) = ⊤`; the top subcomplex is the entire ambient simplex. |
| A single horn cell at every adjacent stage | `∀ a : Fin r, ∃ (d : ℕ) (e : Fin (d+1)), ...` chooses the dimension and distinguished vertex separately for each step, after choosing the filtration. |
| Cell dimension and inner index | `2 ≤ d ∧ 0 < e.val ∧ e.val < d` states exactly `d_a ≥ 2` and `0 < e_a < d_a`, including both bounds. |
| Each inclusion is a pushout of that horn inclusion | `IsPushout f Λ[d,e].ι (Subcomplex.homOfLE (hA (Fin.castSucc_le_succ a))) g` has the horn-to-stage map first, the canonical horn inclusion second, the canonical adjacent-stage inclusion third, and the simplex-to-next-stage map fourth. I checked `IsPushout`'s actual signature and `Subcomplex.homOfLE`; this is the required square, with its commutativity and colimit property. |
| The initial inclusion into the full nerve is inner anodyne | The final conjunct `innerAnodyneExtensions (twistedArrowJoinHorn.{u} n k).ι` concerns the canonical ambient inclusion, not an arbitrary map. |

Dependency and definition checks: I read
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, including its stated use of
Mathlib's simplicial primitives and its `coneCategory` signature; the present
node uses the former and needs no comma-cone construction. I also read all of
`Sheaf.AlgebraicTopology.PushoutJoinSaturation`, including `WeaklySaturated`
and `pushout_join_weak_saturation`. Its inner-anodyne convention is precisely
Mathlib's `innerAnodyneExtensions`, reused here. `Inner/Basic.lean:43-99`
provides the inner-fibration lifting definition, horn generators, closure
instances and weak-saturation characterization. Hence the dependency's
weak-saturation description and this theorem's property agree. Both required
dependency modules are imported, and the explicit IsPushout import supplies
the square predicate. No dependency interface repair is needed.

The helper `twistedArrowJoinHorn` is the domain introduced by this very node,
not an independent extra notion. It has actual face-and-union data, contains
no proof hole, and is listed in `lean.declarations`. There are no new node
records or sibling dependency modules requiring an additional stage-1 review.
The theorem's sole proof is `sorry`, and its docstring records all seven DAG
proof steps, including the support argument for degeneracies and the actual
pushout universal property. All declarations have the required source and
blueprint docstrings; all Lean lines are at most 100 characters. No file-local
notation, local instance, private definition, extra universe equation, or
unbound variable occurs. I mechanically compared the node's `lean.statement`
with the file's complete signature before `:= by`: they are verbatim equal.
The only node field changed from the shared node is `lean`.

Edge cases: `n = 0` is excluded exactly as in the node, and admits no `k < n`
in any event. Both extremes `k = 0` and `k = n-1` are included, corresponding
to `i = n` and `i = 1`; the selected indices stay inner. At `n = 1, k = 0`
the domain is the three-edge spine of `Δ[3]`, and four single inner-horn
attachments suffice. I independently enumerated all nonempty vertex subsets
for every `1 ≤ n ≤ 4` and every `k < n`, ordered the source's primary and
secondary cells, and checked that each intersection with the previous stage
is exactly its distinguished horn and that the final stage is full. The
cell counts are respectively 4, 16, 52, and 160 for each admissible `k`.
The support/section argument in the docstring covers degeneracies beyond
this finite nondegenerate check. An empty attaching-step index (`r = 0`) is
allowed by the syntax and still obeys both endpoint equations. Universe `u`
is unrestricted, including `u = 0`; no site, coefficient, characteristic,
zero-object or scheme hypothesis is involved in this combinatorial item.

Independent searches (different phrasing from the author's):

- LeanFinder via `msearch.py`: `edgewise subdivision paired complementary
  vertices simplex cellular inner anodyne extension` returned eight hits,
  principally the general `PairingCore`/`Pairing.IsInner` API and ordinary
  horns. I opened the inner-pairing predicate in `PairingCore.lean:219-222`:
  it requires an already constructed pairing, and does not supply this domain
  or its finite filtration.
- Loogle via `msearch.py`: `"innerAnodyneExtensions", "IsPushout"` returned
  zero hits.
- LeanSearch via `msearch.py`: `The inclusion of the union of paired
  complementary faces and two block faces into a simplex has a finite inner
  horn cellular filtration` returned eight ordinary horn/face declarations
  and the Quillen all-horn generator. I read `Horn.lean:35-64`; these give
  ordinary horn unions and face inclusions, not the present paired-face
  filtration.
- `rg` over Mathlib's AlgebraicTopology, upstream `WeilConjectures`, project
  `lean/Sheaf`, and `dag/nodes` used `edgewise`, `paired.?deletion`,
  `paired.?face`, `complementary.?vert`, and twisted/horn/filtration
  combinations. The Lean hits were generic jointly-surjective horn-cell
  maps, the parent `TwistedArrowLeftFibration` proof referencing this item,
  and unrelated join-slice horn fillers. The other DAG paired-face node,
  `lem-coef-infinity-twisted-pullback-boundary-filtration`, was opened: it
  concerns a different initial domain, all paired deletions and one pure
  block, with a priority ordering, so it is not a duplicate. Searches for
  both proposed full declaration names in Mathlib, upstream, project Lean
  and `dag/lean_names_upstream.json` found no collision.

Mismatches found: none. I changed only this independent-reading section of
`report.md`; the correct Lean and node record are preserved. The initial
compile invocation used a nonexistent relative path from the read-only
repository and was immediately corrected to the absolute sandbox path; this
was an invocation error, not a Lean or tool defect. Final compilation and
server preflight results are recorded below after running the required
wrappers.

Validation completed: `scompile.py Q28 lem-coef-twisted-arrow-join-horn`
compiled the absolute sandbox module cleanly, with no errors or warnings.
`deliver2.py Q28 lem-coef-twisted-arrow-join-horn --no-push` then printed
`OK (dry run): commit d49444a827 passes the preflight and compiles; nothing pushed`.
