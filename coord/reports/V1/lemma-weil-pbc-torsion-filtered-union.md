## Worker report

The module `lean/Sheaf/AlgebraicGeometry/TorsionFilteredUnion.lean` states
`AlgebraicGeometry.Scheme.isTorsionAbelianSheaf_of_isTorsion`, with one `sorry` and no new
definitions. It bridges the local-section torsion predicate to the already landed exact
positive-divisibility kernel colimit predicate. No assertion is proved.

Hypothesis and clause matching:

- A scheme X: `{X : Scheme.{u}}`, with explicit universe `u`; no geometric or finiteness
  assumptions are imposed.
- An abelian sheaf on the small étale site: `F : Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1}`. This is the Ab(X_et) encoding recorded by
  `def-weil-pbc-etale-sheaves`.
- Every local section is locally killed by a positive integer: `hF : F.IsTorsion`.
  The source definition quantifies over a section, a covering sieve, and every restriction
  along an arrow in the sieve, asserting `IsOfFinAddOrder`. This means existence of a
  positive natural annihilator, and permits different annihilators on different members.
- The conclusion `IsTorsionAbelianSheaf F` is read by its full existing body, not by its
  name alone. Its index is `Scheme.PositiveNat`, data `val : ℕ` and `pos : 0 < val`,
  with the global partial order `n ≤ m` defined as `n.val ∣ m.val`.
- Its diagram object at n is `kernel (n.val • 𝟙 F)`, exactly F[n] = ker(n:F → F).
- For n dividing m its diagram map is `kernel.lift (m.val • 𝟙 F)
  (kernel.ι (n.val • 𝟙 F)) (torsionKernelTransition_condition ...)`. Its composite
  with the m-kernel inclusion is the n-kernel inclusion, so it is the canonical subsheaf
  inclusion. The existing identity and composition lemmas supply the functor laws.
- The cocone has point F and component `kernel.ι (n.val • 𝟙 F)` at n. The conclusion
  is literally `IsIso (colimit.desc D c)` for that cocone, exactly the canonical map c_F.
- Filteredness is the structural property of this fixed index, rather than an extra
  assumption on F. It is nonempty (1), has positive lcm(n,m) as an upper bound, and has
  at most one arrow between any two objects. There is no replacement by a factorial
  chain or by an unspecified existential diagram. The equality in the node is interpreted
  as its expressly stated canonical isomorphism, not as equality of chosen objects.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.EtaleSheaves`: the mixed record of
  `def-weil-pbc-etale-sheaves`; the relevant declared notion is
  `CategoryTheory.Sheaf.IsTorsion`, whose full definition and docstring were read in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` (lines 63–77).
  The module also imports the source Grothendieck-abelian structure on étale sheaves.
- `Mathlib.CategoryTheory.Sites.Abelian`: `CategoryTheory.sheafIsAbelian`, the
  `mathlib_match` of `def-pur-abelian-sheaf-kernel`. This gives the abelian structure;
  `Mathlib.CategoryTheory.Limits.Shapes.Kernels` supplies `kernel`, `kernel.ι`, and
  `kernel.lift`. The dependency record explicitly instructs this specialization, and
  therefore is usable without a replacement module. Their bodies and signatures were read.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit` and
  `colimit.desc`, the record of `def-weil-pbc-category-colimit`. They occur in the
  unfolded existing conclusion; no new colimit construction is introduced.
- `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`:
  `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`, `PositiveNat`, and
  `torsionKernelTransition_condition`, `torsionKernelTransition_id`,
  `torsionKernelTransition_comp`. The complete file was read. Its owning node
  `def-weil-pbc-torsion-etale-sheaf` is added to stmt_deps under the express rule in
  `coord/brief-stage2.md` §5, STMT_DEPS MAY GAIN LANDED NODES. It already exists with
  a landed Lean record; there is no new node or dependency replacement. The item's
  statement, proof, and proof_deps are unchanged.

Edge cases checked before writing:

- Zero sheaf and empty scheme are included; neither nonemptiness nor nonzero assumptions
  are added.
- n = 0 is excluded only because the node explicitly indexes positive integers.
- n = 1 is included, with kernel of the identity, and provides a nonempty index.
- Equal integers and divisibility in either direction agree with identity/composition
  laws; lcm remains positive, also for n = m.
- No characteristic restriction is imposed; integers divisible by the characteristic
  are included.
- Local annihilators may vary without a global bound. Infinite disjoint unions may have
  nontorsion groups of global sections; the hypothesis uses local torsion rather than
  the stronger assertion that every group of sections is torsion.
- The countable positive integer index is fixed and lies in every needed universe; the
  scheme and abelian-sheaf universes match the project's existing definitions.

Searches for an existing statement:

- msearch.py leansearch: "torsion sheaf filtered colimit kernels multiplication by n".
  Service returned Internal Server Error / UNAVAILABLE; no verdict is inferred.
- msearch.py leanfinder: "A torsion sheaf of abelian groups is the filtered colimit of
  kernels of multiplication by positive integers ordered by divisibility". Eight hits,
  including localCohomology.ofDiagram, Concrete.colimit_no_zero_smul_divisor,
  IdealFilter.IsTorsion and condensed Grothendieck instances; none states this claim.
- msearch.py loogle: "CategoryTheory.Sheaf.IsTorsion". No hits; the identifier is
  unknown to the Mathlib search service, as expected for a source-project declaration.
- msearch.py grep: "IsTorsion|torsion.*[Cc]olimit" in CategoryTheory/Sites/.
  No Mathlib hits.
- rg in WeilConjectures for the item id found the two tagged exists_isColimit docstrings
  in SixFunctors/Etale/BaseChangeTheorems/TorsionSheaf.lean. The full ordinary torsion
  theorem was read: it existentially quantifies an unspecified filtered diagram of module
  sheaves killed by integers. Its proof uses factorial kernels. The docstring explicitly
  says it records only existence of some such diagram, so it is weaker than this node.
  The invertible-order variant further changes the hypotheses, so is not an exact match.
- rg in WeilConjectures/AlgebraicGeometry for IsTorsionAbelianSheaf and torsion-colimit
  patterns found no theorem with this conclusion; HighDegreeVanishing uses a factorial
  chain to prove cohomological vanishing, not the required canonical divisibility map.
- rg in lean/Sheaf for torsion and IsTorsionAbelianSheaf found the existing definition in
  TorsionEtaleSheaf.lean and its uses in constructibility/base-change modules, but no
  theorem from local-section torsion to that predicate. It is reused, not redefined.

Source reading: the item's full statement, four detailed proof steps, blueprint_sketch,
source places, split_report and lead_note were read. The local literature blueprint file
named by source.document is absent on this machine; an attempt to retrieve its pinned
GitHub raw path returned 404. The verbatim imported blueprint sketch in the node and the
source Lean docstrings supply the same claim. No source-based correction is needed.
The module docstring includes all four detailed proof steps and the nodes they use.
No mathematical dispute was found.

Validation: scompile.py V1 lemma-weil-pbc-torsion-filtered-union compiled the module on the
server in 1.8 seconds, exit 0, no warnings or errors. The independent second reader must
read this exact definition-based conclusion and its local-section hypothesis.

## Second reading by V1

I independently matched the node's objects, hypotheses, and conclusion against the module.
The scheme is `{X : Scheme.{u}}` (the node's arbitrary scheme, with no quasi-compactness,
separation, finiteness, characteristic, or nonemptiness assumptions). The sheaf is
`F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`, exactly the abelian-sheaf object of
`Ab(X_et)` from `def-weil-pbc-etale-sheaves`. The hypothesis `hF : F.IsTorsion` is
`CategoryTheory.Sheaf.IsTorsion`, whose definition quantifies each local section, a covering
sieve, and finite additive order after every restriction; this is the node's local-section
notion, including varying positive annihilators. The conclusion is
`IsTorsionAbelianSheaf F`, whose existing definition (dependency
`def-weil-pbc-torsion-etale-sheaf`) unfolds to the fixed `PositiveNat` divisibility diagram,
objects `kernel (n.val • 𝟙 F)`, canonical kernel-lift transitions, cocone components
`kernel.ι (n.val • 𝟙 F)`, and `IsIso (colimit.desc D c)`. Thus it says precisely that the
canonical filtered colimit map is an isomorphism, with the node's transition maps and
positive-index convention. The worker added `def-weil-pbc-torsion-etale-sheaf` to `stmt_deps` because
the conclusion uses that existing definition.

The empty scheme and zero sheaf are allowed; no nonzero or inhabited assumptions occur. The
index excludes zero by `PositiveNat`, includes one (so is nonempty), and divisibility handles
equal indices and lcm upper bounds. No characteristic restriction is present. Universes match:
the scheme is `Scheme.{u}`, the sheaf category is `AddCommGrpCat.{u + 1}`, and the index is the
fixed small `PositiveNat` type. The statement therefore covers the node's edge cases.

I independently searched with msearch LeanFinder: "a locally torsion abelian sheaf equals
the directed union of integer multiplication kernels" (8 unrelated sheaf infrastructure
hits); Loogle: "CategoryTheory.Limits.kernel, CategoryTheory.Limits.IsColimit" (11 hits
on cokernel presentations, no match); LeanSearch: "local finite additive order implies
sheaf colimit of multiplication kernels" (service unavailable, no verdict). Ripgrep on
Mathlib Sites and the source/project found no matching theorem. Mathlib has only
generic sheaf colimit infrastructure and group torsion; the source's `exists_isColimit`
declarations use an unspecified factorial diagram and are weaker. The existing
`IsTorsionAbelianSheaf` definition is the unique matching notion; no duplicate statement exists.
The module compiled cleanly with `scompile.py`, and I found no mismatch requiring a statement
correction.

Source check: the blueprint source file is absent locally. I read Stacks 0DDC at
https://stacks.math.columbia.edu/tag/0DDC and its torsion-sheaves section: the proof writes
F as the union of its integer-torsion subsheaves. The lemma there assumes quasi-compact and
quasi-separated X for cohomology commuting with the union, not for the union itself. The
node's detailed proof establishes the union for arbitrary X without that assumption.
I read the dependency signatures and bodies in EtaleSheaves.lean, TorsionEtaleSheaf.lean,
source SheafCohomology/Basic.lean, Mathlib Sites/Abelian.lean, Shapes/Kernels.lean, and
Limits/HasLimits.lean. No new definition node or dependency module is supplied.
The four proof steps and citations are in the statement docstring, the only proof is sorry,
and no variable or universe is unbound. No mathematical or Lean mismatch was found; the
second reading changes only this report.
I also independently read the raw Stacks `etale-cohomology.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
labels `section-torsion` and `lemma-torsion-cohomology`; there is no standing scheme
hypothesis in the section, and the local lemma's qcqs assumption is for its cohomology claim.
Validation of the unchanged 52-line module: server single-file compile exit 0 in 2.1 seconds,
no errors or warnings; dry run printed OK and passed both preflight and server compilation.
