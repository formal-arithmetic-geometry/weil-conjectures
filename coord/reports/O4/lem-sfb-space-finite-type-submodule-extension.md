## Worker report

Item: lem-sfb-space-finite-type-submodule-extension. This is a stage-2 statement
assignment, following the accepted stage-1 split of 2026-10-24. The shared node has
no lean record and there is no released repair note. The inherited stage-1
unchanged-node refusal does not apply to this delivery: it adds the missing Lean
statement and leaves the accepted statement and proof unchanged.

The new module is
Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTypeSubmoduleExtension, with theorem
AlgebraicGeometry.AlgebraicSpace.exists_finiteType_submodule_extension. Its only
proof is sorry. There are no new definitions, postponed helper obligations, new
nodes, or dependency repairs.

Source read: literature/stacks-project/spaces-limits.tex, lemma-extend, Tag 0853,
lines 2534–2561. The source has precisely the supplied node's hypotheses and
conclusion. All five steps of the accepted DAG proof appear in the theorem
docstring, including the empty-generator case in the filtered-stage selection.

Clause-by-clause statement correspondence:

- Base scheme S: `{S : Scheme.{u}}`. Arbitrary algebraic spaces over S: binders
  `(X W : AlgebraicSpace S)`. The explicit universe u is the existing framework's
  scheme, ring and module-section universe; the small étale site objects live in
  u+1. No equality between independent site universes has been imposed.
- Quasi-compactness of X in the node's atlas definition: `hXqc` asserts an S-scheme
  T and an atlas a with `CompactSpace T.left ∧ IsEtale a ∧ IsSurjective a`.
- Absolute quasi-separatedness of X: `hXqs : IsAbsolutelyQuasiSeparated X`. The
  recorded definition quantifies over every pair of affine S-schemes mapping to
  X and requires their fibre product to be compact. Its Tag 0AHR affine-test
  criterion is equivalent to the node's absolute diagonal condition even over a
  base S which is not quasi-separated; relative separatedness is not substituted.
- Open subspace W of X: a specified map `j : W ⟶ X` with `hj` saying that every
  scheme base change is represented by an open immersion. Open immersions are
  monomorphisms, so this is the usual equivalent presentation of an open subspace;
  the map, rather than an arbitrary inclusion into another ambient space, is kept.
- Quasi-compactness of W: `hWqc` repeats the same atlas definition for W.
- Ambient module: `(F : X.Modules) [F.IsQuasicoherent]`. Modules are sheaves over
  the existing small étale structure sheaf. The quasi-coherence predicate is
  Mathlib's local presentation predicate, via the recorded dependency module.
- Prescribed finite-type quasi-coherent submodule: `(G : W.Modules)` with
  `[G.IsQuasicoherent] [G.IsFiniteType]` and the inclusion
  `(ι : G ⟶ (moduleTensorPullback j).obj F) [Mono ι]`. Mathlib's IsFiniteType is
  finite local generating sections, not finite presentation or finite global
  generation. Monomorphisms of module sheaves are precisely maps injective on
  sections, hence give subsheaves whose section images are submodules.
- Restriction: `moduleTensorPullback j` is the existing canonical pullback of
  modules. Since j is a representable open immersion it is étale. The existing
  theorem `moduleTensorPullback_etale_restriction` identifies this very functor
  with `AlgebraicSpace.pullback j hjEt`, which is precomposition on the small
  étale sites with identity scalar map. The comparison is normalized by
  `a ⊗ m ↦ a m`; thus it transports exactly the specified inclusion and not an
  arbitrarily chosen map or identification. This uses the existing interface
  and does not require a new hypothesis asserting that j is étale.
- Existence and both properties: `∃ G' : X.Modules, G'.IsQuasicoherent ∧
  G'.IsFiniteType`. Its placement inside F is `∃ ι' : G' ⟶ F, Mono ι'`.
- Equality of restricted submodule sheaves inside F restricted to W:
  `∃ e : (moduleTensorPullback j).obj G' ≅ G,
  (moduleTensorPullback j).map ι' = e.hom ≫ ι`. The commutative inclusion equation
  says their section images in the SAME ambient restricted module coincide on
  every étale chart. This is equality as subobjects, including the inclusions,
  rather than only an abstract isomorphism between G and the restricted G'.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, a locally ringed
  space locally affine at every point.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion,
  the locally ringed-space open immersion predicate.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  transparently SheafOfModules on the given ringed site (imported publicly by
  AlgebraicSpace).
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  IsRepresentableWith, IsEtale, IsSurjective, EtaleSite, structureSheaf, Modules,
  etaleMap and pullback. Read their full definitions and restriction docstrings.
- def-weil-size-convention is metatheoretic and has no Lean declaration; the
  explicit universe u follows the existing framework without a replacement def.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh and its named
  slice sheafification/local-bijectivity instances, using the exact Mathlib
  SheafOfModules.IsQuasicoherent predicate; no private replacement is made.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated:
  IsAbsolutelyQuasiSeparated, the existing absolute affine-test criterion.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations:
  moduleTensorPullback, the left adjoint to the canonically normalized direct
  image; no arbitrary functor or map is assumed.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators: IsFiniteType and its
  LocalGeneratorsData witness (finite generating families locally).
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent: IsQuasicoherent and
  QuasicoherentData, local presentations by arbitrary coproducts.
- The already stated proof dependencies are imported privately:
  AlgebraicSpaceEtaleOpenImage.etale_open_image,
  AlgebraicSpaceQuasiCoherentPushforward.isQuasicoherent_moduleDirectImage_of_quasiCompact_separated,
  AlgebraicSpaceModuleFpDirectedApproximation.exists_finitePresentation_filtered_colimit,
  and Mathlib's IsClosedImmersion. Their actual namespace is
  AlgebraicGeometry.AlgebraicSpace, except IsClosedImmersion in AlgebraicGeometry.
  Also privately imported AlgebraicSpaceEtaleModulePushforwardRestriction for
  its canonical moduleTensorPullback_etale_restriction comparison.
- The other proof dependencies currently have no Lean record; no declaration
  needed to STATE this theorem is missing. The statement adds no assumptions
  corresponding to those future proof lemmas.

Edge cases: W empty (the zero submodule extends it), W = X (take the given
submodule), G = 0 or F = 0 (take zero), empty generating families, arbitrary
non-Noetherian bases, a base S that is not quasi-separated, and arbitrary
non-finite-presentation F. No nonempty, Noetherian, separated, finite-presentation
or finite-global-generation assumption was added. The existential isomorphism
retains the prescribed inclusion in each case. No statement fault or dispute.

Searches performed with the prescribed wrapper:

- leanfinder: "A finite type quasi coherent submodule on a quasi compact open
  algebraic subspace extends to a finite type quasi coherent submodule". Eight
  hits: local finite-type generators and finite-presentation definitions, no
  extension theorem on algebraic spaces.
- leansearch: "finite type quasi coherent submodule extension from a quasi
  compact open algebraic space". Eight hits including IsQuasicoherent of finite
  presentation and local finite generators, no exact theorem.
- loogle: "SheafOfModules.IsFiniteType, SheafOfModules.Submodule". Zero hits.
- grep through msearch: "finite.type.*submodule|submodule.*extend|extend.*submodule"
  in AlgebraicGeometry. Zero hits.
- rg in lean/WeilConjectures and lean/Sheaf: finite-type/submodule/extension name
  and concept searches. The scheme theorem in
  WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension is not an
  algebraic-space theorem. Its commuting-inclusion conclusion provides a useful
  existing convention. Other hits concern ideals, kernels or scheme extensions.
  Exact `exists_finiteType_submodule_extension` has no hit, and the item id has
  no hit under lean/WeilConjectures. No exact duplicate was found.
- Read the matching generator, quasi-coherence, module and submodule source
  signatures after the search; the general Mathlib definitions are reused.

Validation: scompile.py O4 lem-sfb-space-finite-type-submodule-extension on the
new module compiled both the sandbox probe (13.7 s) and the library module
(8.4 s), with no errors or unexpected warnings. All binders and universe levels
are explicit and autoImplicit is false. No diagnostic commands remain.

## Second reading by O4

The dispatcher brief explicitly requires no subagents and assigns independent
review to the maintainer. This section records the worker's final self-check,
not a claimed independent reading. With the source, node and module open, I
checked the two atlas hypotheses separately, absolute rather than relative
quasi-separatedness, the representable open immersion, all three module
properties, both inclusions, and the commuting isomorphism that gives equality
inside the ambient restricted module. No mismatch was found and the accepted
stage-1 statement and proof were not altered. The maintainer's independent
stage-2 review remains to be performed.
