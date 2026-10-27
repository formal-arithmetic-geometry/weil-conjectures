## Worker report

The module Sheaf.AlgebraicGeometry.AlgebraicSpaceSerreAffineness states
AlgebraicGeometry.AlgebraicSpace.exists_affine_scheme_of_qcqs_h1_zero.
Its single proof is `by sorry`; it introduces no definitions. The node's mathematical
statement and accepted proof are unchanged. The statement dependencies now also name
the landed owners def-sfb-space-absolute-quasi-separated and
def-a1-space-point-topology, as required by the return.

Source read: literature/stacks-project/spaces-cohomology.tex, situation-vanishing
(Tag 07UY) and proposition-vanishing-affine (Tag 07V6), including the whole proof.
The explicit H1 hypothesis agrees with the source's precise formulation.

Clause-by-clause rendering:

- The arbitrary base scheme is `{S : Scheme.{u}}` and the algebraic space over it is
  `(X : AlgebraicSpace S)`; no affine or quasi-separated hypothesis on S is imposed.
- Quasi-compactness, meaning that open covers admit finite subcovers, is
  `hqc : CompactSpace (Point X.obj.obj)` on the existing atlas/point topology.
- Absolute quasi-separatedness is `hqs : IsAbsolutelyQuasiSeparated X`. This uses the
  existing affine-test criterion: every fibre product of two affine scheme maps to X
  has compact point space. This is the absolute diagonal criterion, including when S
  itself is not quasi-separated; relative quasi-separatedness over S would be wrong.
- Modules are `F : X.Modules`, the original module sheaves on X.etaleTopology with
  X.structureSheaf. Quasi-coherence is exactly Mathlib `F.IsQuasicoherent`, the
  predicate used in the recorded QCoh full subcategory. Quantifying over these modules
  with a proof of quasi-coherence is equivalent to quantifying over X.QCoh.
- The underlying additive sheaf is `(SheafOfModules.toSheaf X.structureSheaf).obj F`.
  H1 vanishing is `Subsingleton (@Sheaf.H ... 1)`. Sheaf.H is the usual Ext-from-the-
  constant-integers model of derived global sections. The full small etale site and
  original AddCommGrpCat.{u} coefficients are retained. The existing
  etaleAlgebraModulesHasSheafify instance supplies sheafification. HasExt.standard
  supplies the large Ext universe, as in the recorded etale/Zariski comparison;
  neither is an extra hypothesis. Subsingleton expresses zero for this additive group.
- The conclusion `∃ Z : Over S, IsAffine Z.left ∧ Nonempty (yoneda.obj Z ≅ X.obj.obj)`
  supplies an actual affine scheme together with its scheme morphism to S and a
  representing isomorphism of relative presheaves. It asserts neither an arbitrary
  affine map nor a chosen chart, and does not require a canonical choice of Z.

Recorded dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.EtaleSite, etaleTopology, structureSheaf and Modules.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule:
  AlgebraicGeometry.AlgebraicSpace.QCoh, using SheafOfModules.IsQuasicoherent from
  Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.
- Sheaf.CategoryTheory.SiteCoveringAxioms:
  CategoryTheory.Precoverage.IsSiteForCoverings, and the retained Mathlib Sheaf.H
  interface from Mathlib.CategoryTheory.Sites.SheafCohomology.Basic. Global cohomology
  is Sheaf.H, not the over-an-object Sheaf.H' (X need not be a scheme-site object).

Additional existing infrastructure is used directly, without a private replacement:
AlgebraicSpace.Point and its pointTopologicalSpace (AlgebraicSpacePointClasses and
AlgebraicSpacePointTopology), IsAbsolutelyQuasiSeparated
(AlgebraicSpaceAbsoluteQuasiSeparated), etaleAlgebraModulesHasSheafify
(AlgebraicSpaceCommAlgebraSheaf), Mathlib HasExt.standard, IsAffine, Over and Yoneda.
All statement imports are public; proof-only imports are plain. The recorded scheme
H1 criterion's duplicate Sheaf.Paper module is replaced by its identical upstream
WeilConjectures.AlgebraicGeometry.QuasiCompactH1Zero module, following the brief's
upstream preference. The docstring gives all five accepted proof steps and their nodes.
Four proof dependencies have no Lean record yet and therefore have no module to import:
lem-sfb-space-acyclic-affinization-geometry,
lem-sfb-space-affine-etale-polynomial-generators,
lem-sfb-space-cohomology-filtered-colimit,
lem-sfb-space-discrete-fibres-locally-quasifinite.
They are proof prerequisites only, not notions needed to state this theorem.

Edge cases checked before writing: X empty is allowed and represented by the empty
scheme (Spec of the zero ring); no nonemptiness binder occurs. The zero module is
included in the universal hypothesis and has zero H1. Affine schemes satisfy the
intended criterion, with no characteristic, Noetherian or finite-type restriction.
For a non-quasi-separated base, an affine X mapping into S still falls under the
statement because hqs is absolute. There is no separated-over-S assumption or
restriction to Spec Z. Universes use Scheme.{u}, its existing Type-u valued sheaves
and existing modules; standard Ext changes only the size of cohomology, not its
vanishing. `set_option autoImplicit false` checks that all binders are explicit.

Searches performed (2026-10-24):

- msearch.py leanfinder: "A quasi compact quasi separated algebraic space with
  vanishing H1 for all quasi coherent modules is affine". Eight hits, including
  IsAffine, scheme quasi-affineness and scheme qc/qs infrastructure; no space criterion.
- msearch.py loogle: `"IsAffine", "IsQuasicoherent"`. Zero hits.
- msearch.py grep: `[Ss]erre.*[Aa]ffine|[Aa]ffine.*[Vv]anishing|[Ii]sAffine.*[Cc]ohomology`.
  Zero hits.
- msearch.py leansearch: "Serre affineness criterion for quasi compact quasi separated
  algebraic spaces with H1 of all quasi coherent modules zero". Eight hits, giving
  scheme affineness constructors and locality results, no algebraic-space theorem.
- rg in lean/WeilConjectures and lean/Sheaf for Serre/affine/H1 and the item id:
  found scheme-only Serre criteria and the distinct affine-base-change theorem;
  no occurrence of the item id and no existing theorem with the item's conclusion.
- rg in AlgebraicSpace modules located the exact existing absolute-quasi-separated
  predicate, original-section-universe sheafification instance and point topology.
  No new notion or dependency repair was necessary.

No statement dispute or mathematical node fault was found. Compilation through
scompile.py passed for the delivered module with no diagnostic errors or warnings.

## Second reading by O1

A separate in-thread audit reread the source situation/proposition, node and final
signature. No independent sub-agent was started, as the dispatcher forbids agents;
the maintainer's independent review remains the independent reading of this delivery.
The audit matched S, X, compactness, absolute quasi-separatedness, all quasi-coherent
modules and degree-one additive cohomology to the binders listed above. It checked
that the conclusion includes both affineness and a representing isomorphism over S.
The potentially delicate choices were resolved using the existing absolute diagonal
predicate and the original additive sheaf with HasExt.standard; no coefficient lift,
chosen atlas or extra typeclass hypothesis was introduced. No further mismatch or
statement correction was needed. The repaired node changes lean and adds the two
landed definition owners to stmt_deps.

## Repair of return H2

Returned immutable head: a04be2e2fc2a. The maintainer found that two existing notions
used in the statement lacked direct statement-dependency edges. Added exactly
`def-sfb-space-absolute-quasi-separated` and `def-a1-space-point-topology` to
`stmt_deps`, using the landed-node exception in coord/brief-stage2.md section 5.
The first owns `IsAbsolutelyQuasiSeparated X`; the second owns
`pointTopologicalSpace`, used by `CompactSpace (Point X.obj.obj)`. Both existing
node records and their complete statements were reread. Their Lean modules are
already exposed by the public import of AlgebraicSpaceAbsoluteQuasiSeparated.
The theorem and its module remain exactly as reviewed. No statement_change record
is required: this repairs dependency bookkeeping without changing the mathematical
statement. Compared the retained node against current main: before this repair
the sole differing field was lean, so no intervening main changes were overwritten.
The independent maintainer reading found the mathematical signature exact, including
arbitrary S, absolute quasi-separatedness, original additive-sheaf H1, affine
representability over S, and the empty-space case; H2 is addressed by both new edges.
