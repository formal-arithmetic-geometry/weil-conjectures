## Worker report

The main module states `SheafOfModules.isIso_derivedTensor_truncationWindow`. It uses the
canonical derived tensor bifunctor `SheafOfModules.wfSiteDerivedTensor` and states exactly
the node's hypotheses: a category `C` with `Category.{v} C`, a Grothendieck topology `J`, a
commutative ring sheaf `R`, the displayed derived-category localization instance, derived
objects `K,L`, upper bounds `bK,bL`, the two vanishing hypotheses `hK` and `hL`, a degree
`i`, lower cutoffs `a,c`, and `a ≤ i-bL`, `c ≤ i-bK`. Its first conclusion is `IsIso` on
the homology functor in degree `i`, applied to the bifunctor image of the pair of canonical
maps `truncGEπ a` and `truncGEπ c` (rendered by `CategoryTheory.Prod.mkHom`). The second
conclusion states vanishing of each truncated factor for every `q` with `q < a ∨ bK < q`
respectively `q < c ∨ bL < q`; this includes empty intervals. The proof is `sorry`, as
required for stage 2.

The recorded statement dependencies used are: `Sheaf.Paper.WeilTensorProduct`, providing
`SheafOfModules.wfSiteDerivedTensor`;
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`, documenting the canonical good
truncations through Mathlib and `DerivedCategory.TStructure.t`; `Sheaf.CategoryTheory.RingedSiteModules`,
providing `ringedSiteModules`/Mathlib module sheaves; Mathlib's `DerivedCategory` and
`DerivedCategory.homologyFunctor`; and the imported Mathlib truncation and homology-sequence
interfaces. The maintainer second reading added explicit non-public proof-plan imports for
`BoundedFlatReplacement`, `BoundedAboveFlatSheafKFlat`, `ProjectionMateExact`,
`Mathlib.Algebra.Homology.BifunctorShift`, and
`Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`. The long exact homology
interface is already a public import because the statement uses its homology functor.

Edge cases checked against the node and source include `a = i - bL` and `c = i - bK`,
cutoffs above the corresponding upper bound (empty windows), zero or acyclic factors,
vanishing hypotheses with arbitrary integer bounds, and shifted complexes `K = k[2]`,
`L = k[-2]`, `i = 0`, which is the counterexample to the source's uncorrected uniform
`i-1` cutoff. No Noetherianity, local constancy, finite-generation, points, or finiteness
hypothesis was added.

Searches for an existing statement or duplicate were made with `msearch.py`: `leanfinder`
for “Cohomology of derived tensor of bounded above complexes is unchanged under sufficiently
low good lower truncations” (hits only individual truncation/support declarations),
`loogle` for `CochainComplex.truncGE, DerivedCategory.homologyFunctor` (no hits),
`grep` for `truncGE.*tensor|tensor.*truncGE` (no hits), and `leansearch` for the canonical
lower-truncation comparison (hits only individual truncation maps and support lemmas).
Repository searches with `rg` found no existing declaration of this item; the only related
published construction is `wfSiteDerivedTensor`, which is reused rather than copied.

No `STATEMENT-DISPUTED` issue or statement correction was found.

## Second reading by Q12

I reread the item JSON, its source proof steps, all statement dependencies, and the delivered
module. Every binder in the Lean theorem corresponds to one hypothesis in the node. The
`Prod.mkHom` pair has exactly the two canonical good-lower-truncation maps; the homology map
is in the fixed degree `i`; and both disjunctive vanishing clauses preserve the node's empty
interval convention. The imported recorded truncation module supplies the
existing Mathlib constructions without additional aliases. The shifted-complex edge case confirms why the corrected
cutoff inequalities are needed. No mismatch was found.


Maintainer independent reading of immutable delivery 277f9a199bf31498865254c6565db5ca109c2d48:

| Node clause | Lean rendering | Verdict |
| --- | --- | --- |
| Small site | `{C : Type u} [Category.{v} C]`, `J : GrothendieckTopology C` | Correct; independent object and morphism universes. |
| Commutative ring sheaf and its modules | `R : Sheaf J CommRingCat.{max u v}`, the displayed `SheafOfModules` of its forgotten ring sheaf | Correct; the recorded `ringedSiteModules` is exactly this transparent abbreviation. |
| Derived category and objects | `[HasDerivedCategory.{w, ...} ...]`, `K L : DerivedCategory ...` | Correct; `w` chooses localization morphism size as permitted by the recorded definition. |
| Upper cohomology bounds | `bK bL : ℤ`, `hK`, `hL` | Exactly vanishing for every degree strictly above the respective bound. |
| Degree and lower cutoffs | `i a c : ℤ`, `ha : a ≤ i - bL`, `hc : c ≤ i - bK` | Correct, including equality. |
| Derived tensor | `wfSiteDerivedTensor J R` | General-site K-flat tensor chosen with the representative comparison of `wf_site_derived_tensor_descent`; no completed or pro-etale tensor is substituted. |
| Canonical comparison | `Prod.mkHom ((t.truncGEπ a).app K) ((t.truncGEπ c).app L)` followed by tensor and degree-i homology | Correct direction and specified maps. |
| Isomorphism of module sheaves | `IsIso` of that homology map | Correct; asserts invertibility of the particular canonical map. |
| Both finite windows | The two `∀ q`, `q < a ∨ bK < q` and `q < c ∨ bL < q` vanishing clauses | Correct, including empty intervals. |
| No further geometric or finiteness hypotheses | No such binders | Correct. |

Read the six immutable statement-dependency records and their actual general-site,
module-sheaf, localization, homology and truncation interfaces. The existing ringed-site
module abbreviation and Mathlib truncations are reused. The only new declaration is the
item theorem with exactly `by sorry`; there are no definitions or auxiliary local proofs.
The source and blueprint docstrings contain the five node proof steps.
The node's stored Lean signature matches the file after whitespace normalization; the
replacement changes imports only, so that record remains valid.

Source checks: Stacks `sites-cohomology.tex` 14356-14376 (094H), 3120ff (06YQ),
3173ff (077J), and 3275-3325 (06YU); `homology.tex` 3612ff (0118);
`derived.tex` 4076ff (08J5). The source's uniform `i-1` assertion fails for
`K = k[2]`, `L = k[-2]`, `i = 0`. The corrected cutoffs already belong to the immutable
node, rather than being a statement change in this delivery. The discarded-tail tensor
upper bounds are `a-1+bL ≤ i-1` and `bK+c-1 ≤ i-1`, giving the required vanishing in
both i and i+1. Thus the two long exact sequences give the canonical comparison.

Edge cases: equality in both cutoff inequalities, arbitrary integer shifts and bounds,
zero or acyclic factors, zero ring, empty site, empty windows, and non-flat factors
(such as Z/2 over Z). The good truncations need not be termwise flat. No points are used.
The site object and morphism universes are independent and the coefficient/module universe
is their maximum; no equality of site universes is assumed.

Independent duplicate search used `rg` with tensor/truncation/window terms over the
read-only project's homology and category-theory modules, upstream WeilConjectures,
and Mathlib homology. Related results concern individual truncations, amplitude or
flatness, not this canonical two-factor comparison. The worker's three search kinds
remain recorded above. No duplicate definition or missing helper was found.

Finding H9 (proof-plan import convention): five proof-dependency modules lacked explicit
non-public imports. Added those imports; no theorem, node statement, or dependency record
was changed. Corrected the worker report's import description. No substantive fault found.


Compiler reproduction (maintainer review, 2026-10-17):
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q12
lem-weil-pbc-derived-tensor-truncation-window <file>` succeeded with exit code 0
for both the immutable snapshot module and its replacement under `fixes/lean/`.
The installed wrapper uses the server side overlay and wire confirmation, not a
local compile on this host. Original: sandbox 2.4 s, library 3.2 s;
replacement: sandbox 2.3 s, library 2.9 s. Both outputs had no errors or warnings.
No global build, live Lean write, delivery, merge, or clone edit was performed.
