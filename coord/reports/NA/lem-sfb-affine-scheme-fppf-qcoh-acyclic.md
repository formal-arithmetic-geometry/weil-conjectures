## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSchemeFppfQCohAcyclic` states
`AlgebraicGeometry.Scheme.affine_scheme_fppf_qcoh_acyclic`, with proof `sorry`.
It also states the named sheafification helper
`AlgebraicGeometry.Scheme.affineFppfHasSheafify`, with proof `sorry` and a
construction argument in its docstring. There are no new definitions, new DAG
nodes, statement corrections, or dependency-module replacements. Only the item's
`lean` field changes.

The node and the full signatures/docstrings of its recorded dependencies were
read. The source read was `literature/stacks-project/descent.tex`, proposition
same-cohomology-quasi-coherent (03DW), especially its first affine-objects paragraph,
and `coherent.tex`, lemma quasi-coherent-affine-cohomology-zero (01XB). The module
retains the four steps of the accepted split in its theorem docstring.

Hypothesis and clause correspondence:

- The size convention is explicit `universe u`. `Scheme.{u}` and `Over U` have
  object universe `u+1` and morphism universe `u`. Module carriers remain in `u`.
  `Sheaf.H'.{u+1,u,u+1}` uses Mathlib's `HasExt.standard` in `u+1`. No additional
  smallness, essential-smallness, sheafification or Ext assumption is a binder.
- The arbitrary affine scheme is `(U : Scheme.{u}) [IsAffine U]`; `IsAffine` is
  Mathlib's predicate that the canonical map to Spec of global sections is an iso.
- The arbitrary quasi-coherent Zariski module is `(F : SfbZariskiQCoh U)`.
  This is the existing full subcategory of `SheafOfModules.isQuasicoherent
  U.ringCatSheaf`; `F.obj` is the underlying module. It imposes quasi-coherence
  alone, not `IsQuasiCoherentFiniteType`, coherence, or a finite presentation.
- The big fppf site is the existing `fppfTopology.over U` on `Over U`, not the
  small fppf site or a site with restricted objects.
- The associated module sheaf is `(sfbAssociated U
  ((Classical.choose scheme_big_fppf_quasicoherent_equivalence) U)).obj F`.
  This uses the recorded dependency's fully specified section-normalized witness.
  Its existential section comparisons in `Classical.choose_spec` identify each
  value additively and linearly with `Γ(T, v* F)`, commute with restrictions via
  `sfbSectionPullback` and `Modules.tensorPullbackSectionComp`, and commute with
  module maps. This chooses from a theorem specifying the object up to the
  canonical natural module isomorphism, rather than from an unconstrained
  equivalence or Nonempty. Vanishing of cohomology is invariant under that iso.
  There is no new choice-based definition and no postponed data definition.
- The underlying abelian sheaf is obtained by the existing
  `SheafOfModules.toSheaf (sfbFppfRings U)`.
- Cohomology is the recorded `Sheaf.H'` at `Over.mk (𝟙 U)`, the actual terminal
  arrow of the slice. It is the Ext encoding of derived abelian evaluation,
  not module-derived cohomology or a direct-image assertion.
- `(q : ℕ) (hq : 0 < q)` covers exactly the positive cohomological degrees.
  `IsZero` applies to the bundled abelian group `H'`, so it says that the entire
  cohomology group is zero.
- No finite-generation, module-flatness, Noetherian, separation, nonemptiness,
  characteristic, or additional property of U or F occurs in the signature.

The helper `affineFppfHasSheafify` supplies the left exactness needed by `H'` and
its abelian sheaf category. The existing associated-sheaf module already provides
`sfbFppfHasWeakSheafify` and `sfbFppfWEqualsLocallyBijective` at the small coefficient
universe. The helper's proof plan transports left exactness of the usual larger
sheafification across the sectionwise shrinking isomorphisms of that existing
construction. It adds no mathematical assumption to the vanishing theorem and
introduces no second sheafification functor. This is infrastructure for the
cohomology explicitly requested by this same node; both declarations are listed
in `lean.declarations`.

Dependency declarations used and imported:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes Mathlib's
  `SheafOfModules.IsQuasicoherent`; only that clause of `pqf-def-coherent` is used.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` supplies
  `GrothendieckTopology.over`.
- `Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`:
  `SfbZariskiQCoh`, `sfbAssociated`, `sfbFppfRings`,
  `scheme_big_fppf_quasicoherent_equivalence`, and its small sheafification helpers.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionComp`, used in the recorded associated-sheaf formula.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the recorded site interface and its
  public Mathlib `CategoryTheory.Sheaf.H'` import.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `CategoryTheory.Injective`, `InjectiveResolution`, the resolution interpretation
  of the stipulated abelian derived evaluation.
- Plain proof imports: `Mathlib.AlgebraicGeometry.Pullbacks`
  (`AlgebraicGeometry.pullbackSpecIso`),
  `Sheaf.AlgebraicGeometry.FppfAffineRefinement`
  (`Scheme.exists_finite_fppf_affine_open_refinement`), and
  `WeilConjectures.CategoryTheory.SiteCechVanishingCriterion`
  (`CategoryTheory.Sheaf.isZero_H'_of_siteCech_vanishing`).
  `lem-sfb-finite-affine-fppf-cech-vanishing` has no Lean declaration/module on the
  read base, so its future proof import is omitted; the proof docstring names it.

Edge cases checked before writing: q=0 is deliberately excluded, since its group
is generally Γ(U,F), whereas every q>0 is retained. The zero module is included.
The empty scheme (Spec of the zero ring) is affine and is included; the empty
cover forces zero sections, and both the helper and theorem admit it. There is
no restriction excluding empty cover members or repeated Cech factors. Arbitrary
modules, including non-flat modules and modules not finitely generated, belong
to the quasi-coherent subcategory. Affineness imposes no Noetherian condition.
No independent universe quantification over test schemes can make the
hypotheses vacuous: all objects of the prescribed `Over U` site are retained.

Searches for an existing statement (2026-10-24; wrapper records are in
`searches.jsonl` in the sandbox):

- msearch leanfinder, query `On an affine scheme higher big fppf cohomology of an
  arbitrary quasi coherent module vanishes`: eight hits, on affine limit-section
  vanishing, the abelian module category, and quasi-coherent local presentations;
  none states big-fppf quasi-coherent cohomology vanishing.
- msearch loogle, query `"Sheaf", "cohomology"`: seven hits, general cohomology
  functors/presheaves and unrelated nonabelian H1 relations; no matching theorem.
- msearch grep, query `fppf.*cohomology|cohomology.*fppf|IsAffine.*cohomology|cohomology.*IsAffine`:
  zero Mathlib hits.
- msearch leansearch, query `On the big fppf site of an affine scheme a sheaf
  associated to any quasi coherent module has zero higher abelian sheaf cohomology`:
  eight hits, general `CategoryTheory.Sheaf.H` and quasi-coherent definitions;
  no matching theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf`, query
  `fppf.*cohomology|cohomology.*fppf|affine.*acyclic|acyclic.*affine|lem-sfb-affine-scheme-fppf-qcoh-acyclic`:
  related etale acyclicity, Cech results, the associated equivalence, and the
  downstream `SpaceFppfQCohHigherVanishing` reference; no existing statement of
  this node. In particular `Sites/Ga.lean` is small-etale cohomology of O only.
- rg in upstream, project and `dag/lean_names_upstream.json` for the exact new
  theorem and module names: no declaration collision.

Compilation: prescribed scompile.py compiled both the sandbox module and the
library-named module cleanly (11.2 s and 3.2 s); no errors or warnings. An earlier
probe exposed missing `HasSheafify` (only weak sheafification was exported); the
named helper above repaired it without adding hypotheses or equating universes.
The final dry-run and delivery are recorded below after validation.

No STATEMENT-DISPUTED issue or source-statement fault was found.

## Second reading by NA

A separate pass through the node, its dependency's full section/restriction
signature, the source's first affine paragraph, and the final Lean file checked
every binder and the conclusion. This is the dispatcher's worker self-check;
the maintainer's independent review remains separate, and no other agent was
started. In particular the chosen equivalence is the section-normalized witness
of the recorded theorem, F requires only quasi-coherence, the forgetful functor
lands in abelian sheaves, the group is `H'` at the terminal arrow, and q=0 is
excluded explicitly. The sheafification failure was fixed by a named helper,
not a new hypothesis. No node-statement change or additional mismatch was found.

Validation: deliver2.py --no-push returned `OK (dry run)` for commit
`7773e1c8a5c`: preflight and per-file compilation both pass. Delivery is made
with the same prescribed wrapper, which repeats these checks before pushing.
