## Worker report

The module Sheaf.AlgebraicGeometry.SpaceAffineChartUniformQcohVanishing states
AlgebraicGeometry.AlgebraicSpace.affineChartModuleSections_uniform_vanishing.
Its only construction is affineChartModuleSections, the node's F_V on the actual
module category. Its two named additivity obligations and the vanishing theorem
have sorry proofs, with source and proof docstrings. No mathematical statement
was corrected, and no new definition node or dependency repair is needed.

The node and Lean match as follows, including every hypothesis and clause:

- Size convention: explicit universe u, Scheme.{u}, module and additive-section
  carriers in u. The recorded SmallEtaleModel is a u-small skeleton of affine
  charts and preserves the original coefficient universe. No equality of unrelated
  site universes, coefficient lift, or derived-category size assumption is added.
- S is a scheme: `{S : Scheme.{u}}`. X and Y are algebraic spaces over that same
  S: `{X Y : AlgebraicSpace S}`. Their morphism is `(f : X ⟶ Y)`.
- Y is quasi-compact: `(hYqc : IsQuasiCompact Y.obj)` uses the existing
  AlgebraicSpace.IsQuasiCompact from StackQcqsMorphism, owned by
  def-sfb-stack-qcqs-morphism. Its definition is existence of a quasi-compact
  scheme atlas that is representable, surjective and etale. The definition is
  reused directly, without an inline copy. No atlas is fixed before choosing N.
- f is quasi-compact on every affine test: hfqc is
  IsQuasiCompactPresheafMap f.hom.hom. Its existing definition quantifies over
  every affine Z and every h_Z → Y, supplying a quasi-compact surjective etale
  scheme atlas of the actual fibre product. This is the node's condition that
  every such pullback source is quasi-compact.
- The relative diagonal is quasi-compact: hfqs is the same predicate applied to
  diagonalPresheafMap f.hom.hom. This is the relative diagonal into X ×_Y X;
  no absolute quasi-separatedness of Y, or separatedness of f, is required.
- An arbitrary affine etale scheme V → Y: V : Y.EtaleSite already includes its
  representable etale map from the underlying scheme over S;
  IsAffine (Y.etaleForget.obj V) is exactly the remaining affine condition.
- W = X ×_Y V: `(enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V)`
  is the actual algebraic-space fibre product, with its etale projection to X.
- Extension M̃: `(smallEnlargedModuleEquivalence.{u,u} X).inverse` is the existing
  normalized inverse to enlarged-site restriction, retaining the u-sized modules.
  The dependency's recorded module publicly exposes this interface through
  AtlasEtaleRestriction and SmallEnlargedEtaleModules. No arbitrary extension or
  presheaf replacement is introduced.
- F_V(M) = M̃(W), forgetting the section ring action: affineChartModuleSections
  composes this inverse with SheafOfModules.toSheaf, sheafToPresheaf and evaluation
  at op W. Its maps are exactly the extension and section maps. The first named
  additivity obligation records the node's adjective "additive"; the second
  records its transport to the equivalent small affine model.
- R^p F_V is derived using injective resolutions in ALL module sheaves:
  `(X.smallModuleEquivalence.inverse ⋙ affineChartModuleSections f V).rightDerived p`
  is applied to `X.smallModuleRestriction.obj M`. Mathlib rightDerived is
  homology of its functor applied to a nonnegative injective resolution. The
  source SmallModules is all modules, not QCoh. smallModuleEquivalence is an
  additive exact equivalence and preserves injectives, so this is precisely the
  node's injective computation, independent of the skeleton. The existing
  SheafOfModules.isGrothendieckAbelian theorem supplies enough injectives on the
  small model, with the standard Mathlib abelian instance; no categorical
  structure is chosen from Nonempty and no extra hypothesis is imposed.
- M is any quasi-coherent module: `(M : X.Modules), M.IsQuasicoherent`, using
  the existing Mathlib presentation predicate specialized by the recorded
  AlgebraicSpaceQuasiCoherentModule module. Derivation occurs before this input
  restriction; no injectives of QCoh are used.
- One integer N >= 1 depending only on f: `∃ N : ℕ, 1 ≤ N ∧ ...` appears after
  f and its three geometric hypotheses, before V, M, and p. A natural bound
  is equivalent to an integer bound because N >= 1. Every integer p >= N is
  uniquely a natural degree, so `∀ p : ℕ, N ≤ p → ...` includes exactly every
  asserted integer degree. There is no missing negative-degree case.
- Vanishing: IsZero of the resulting AddCommGrpCat object means precisely the
  zero section-cohomology group. It is not IsZero on a bare Type.
- There are no Noetherian, finite-type, finite-presentation, coherence, properness,
  or characteristic assumptions anywhere in the signature.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, EtaleSite,
  etaleForget, structureSheaf and Modules (with IsEtale and IsSurjective for atlases).
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently Mathlib SheafOfModules with its ordinary morphisms and abelian instance.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its slice
  sheafification instances, specializing Mathlib SheafOfModules.IsQuasicoherent.
- Sheaf.AlgebraicGeometry.SpaceCotangentRingMap, through its public imports:
  enlargedSchemeInclusion, enlargedBaseChange, enlargedStructureSheaf,
  smallEnlargedModuleRestriction and smallEnlargedModuleEquivalence. The full
  original EnlargedEtaleRingedSite and SmallEnlargedEtaleModules declarations
  were read, including their universe parameters and normalized restriction.
- Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal:
  IsQuasiCompactPresheafMap and diagonalPresheafMap. Their existing:true owners
  def-sfb-space-quasi-compact-presheaf-map and
  def-sfb-presheaf-map-separated-diagonal are cited in stmt_deps. The etale-locality
  theorem is not a statement dependency.
- Sheaf.AlgebraicGeometry.StackQcqsMorphism: AlgebraicSpace.IsQuasiCompact,
  owned by def-sfb-stack-qcqs-morphism, is used directly for hYqc. Its complete
  signature, real atlas definition and source docstring were read.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: SmallEtaleModel,
  SmallModules, smallModuleRestriction, smallModuleEquivalence. Its owning landed
  node def-sfb-space-small-ringed-model is added to stmt_deps for the skeleton
  permitted by the original size convention. Neither addition changes the statement.
- Mathlib.CategoryTheory.Abelian.RightDerived: Functor.rightDerived, which applies
  the functor to injective resolutions in the ambient abelian category and then
  takes cohomology. SheafOfModules.isGrothendieckAbelian is reused from the
  upstream module publicly imported by AlgebraicSpaceSmallRingedModel.

All currently recorded proof-dependency modules are imported privately unless
already public statement dependencies. The unstated proof nodes remain in the
proof docstring; none is being assumed as a new hypothesis. The Mathlib proof
leaves for affine qcqs, bounded-below K-injectives and preservation of injectives
are imported as well.

Source checked locally: literature/stacks-project/spaces-cohomology.tex,
lemma-vanishing-higher-direct-images (073G) and
lemma-quasi-coherence-higher-direct-images-application (08EX), and
spaces-perfect.tex, lemma-quasi-coherence-direct-image (08FA), proof of (2).
The node is a supporting lemma, not a blueprint unit's own statement. The stated
bound is the precise affine-chart bound called for in 08FA's proof.

Edge cases checked: X empty, Y empty (then also X empty), empty affine chart,
zero module, arbitrary characteristic, non-Noetherian base and non-quasi-separated
Y are all admitted. All their section complexes are zero in the empty or zero
cases. Degree zero is correctly outside the claim because N >= 1; p = N is
included. Disconnected charts and modules with arbitrary, infinite presentations
are admitted. N is independent of every chart, module, presentation and resolution.

Searches for existing declarations (2026-10-24):

- msearch.py leansearch: "For a quasi compact quasi separated morphism of algebraic
  spaces and a quasi compact target the higher derived sections of quasi coherent
  modules over affine etale charts vanish uniformly". Eight hits, including
  QuasiSeparated.of_quasiSeparatedSpace and quasiCompact_isStableUnderBaseChange;
  these are scheme-geometric facts, not the algebraic-space cohomology bound.
- msearch.py leanfinder: "Uniform vanishing of higher derived module sections over
  affine etale charts of quasi compact quasi separated algebraic space morphisms".
  Eight hits about affine limits and formal unramifiedness, no matching theorem.
- msearch.py loogle: "Functor.rightDerived, SheafOfModules.evaluation,
  IsQuasicoherent". Zero hits; remote index reports unknown Functor.rightDerived.
  The actual pinned Mathlib declaration was read directly instead.
- msearch.py grep in Mathlib/AlgebraicGeometry:
  `uniform.*vanish|finiteAmplitude|affine.*[Cc]hart.*[Vv]anish`: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, the proposed names,
  and `uniform.*[Vv]anishing|[Vv]anishing.*uniform`: no matching statement.
  Hits concerning finite-coefficient torsion bounds, projective Serre vanishing
  and ring-theoretic Tor bounds have different coefficients and hypotheses.
  Existing algebraic-space globalSections_finiteAmplitude is a single-space
  unbounded-complex bound and is reused as a proof dependency, not duplicated.
- Direct reads and rg of enlarged-site modules found the already available
  coefficient-preserving extension and base-change object, so no new notion
  or duplicate canonical map was introduced.

Validation: scompile.py compiled the sandbox and final library module cleanly;
all declarations use explicit universes and autoImplicit is false. The two initial
missing-additivity elaboration errors were repaired with the named obligations
for this node's F_V and its small-model expression. No diagnostic commands remain.

## Second reading by Q87

Author's second pass with the node, source and final module open; the maintainer
performs the independent reading required by this direct-worker protocol.
I rechecked the quantifier order, hYqc atlas characterization, all-affine-test
meaning of hfqc, relative (not absolute) diagonal in hfqs, actual W and normalized
M̃, section ring forgetting, ambient-module right derivation, the quasi-coherent
input predicate, and the inclusive bound. The small-model expression changes
neither the category up to its recorded exact equivalence nor the section
universe. Natural degrees lose no integer p >= N >= 1. No extra finiteness or
separation condition occurs. The first delivery added two explicit
additivity obligations, each a property of the exact functor the node introduces.
This repair additionally replaces the inline hYqc predicate by the exact existing
IsQuasiCompact Y.obj and cites the definition nodes owning all three predicates.
No statement mismatch or mathematical dispute was found.


## Returned delivery repaired

The return concerns immutable head e94a41c255d9. The retained sandbox was compared
with current main: only lean and stmt_deps differed, and the module is not present
on main. The node was reconstructed from current main with the repaired lean
record and added definition dependencies; other current-main fields are preserved.
The delivery wrapper handles rebasing and packaging against the live server base.

1. H2: removed lem-trf-space-qc-separated-etale-local from stmt_deps. Added the
   already landed existing:true definition owners
   def-sfb-space-quasi-compact-presheaf-map (IsQuasiCompactPresheafMap) and
   def-sfb-presheaf-map-separated-diagonal (diagonalPresheafMap). Their node
   statements, Lean records, full signatures and source docstrings were read.
   The shared module stays publicly imported for those definitions, so its
   etale-locality theorem remains available to the eventual proof. There is a
   bookkeeping discrepancy in the return's phrase "keep the theorem in
   proof_deps": neither returned head nor main has that theorem in proof_deps.
   The original proof plan and proof_deps are preserved, as the stage-2 field
   contract forbids adding a proof dependency without a statement correction.
   No statement correction is needed for these exact interface substitutions.
2. H4: imported StackQcqsMorphism and changed hYqc to
   `(hYqc : IsQuasiCompact Y.obj)`. Added its owning definition node
   def-sfb-stack-qcqs-morphism to stmt_deps. Updated lean.statement verbatim
   from the final declaration and updated the hypothesis mapping above.
   This existing definition unfolds to precisely the former inline predicate,
   so it preserves the already reviewed mathematical content and edge cases.

Second reading of the repair: hYqc now names its existing definition; hfqc and
hfqs name the same predicates as before but cite their definition owners. F_V,
its normalized extension, fibre product evaluation, all-module right derivation,
quantifier order and bound are unchanged. The author performed this pass; the
maintainer supplies the independent review, as in the original direct-worker brief.
