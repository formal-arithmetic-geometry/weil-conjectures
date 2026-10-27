## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectTestsPseudoCoherence` states
`AlgebraicGeometry.AlgebraicSpace.isPseudoCoherent_of_perfect_tensor_tests`.
Its sole theorem has proof `sorry`; no definition is introduced. The mathematical
statement and the accepted five-step proof plan are unchanged. Four already-landed
notion nodes are added to stmt_deps under brief-stage2 §5, to record the precise
interfaces used instead of duplicating definitions. No new nodes or dependency
repairs are needed.

Source checked: Stacks `spaces-more-morphisms.tex`, lemma-characterize-pseudo-coh-improved
(Tag 0GFJ), lines 12229ff, and lemma-relative-pseudo-coherent-is-moot (Tag 0DII),
lines 10859ff. The first gives relative pseudo-coherence; the second gives the
absolute conclusion under exactly flatness and local finite presentation. Read the
current blueprint latest six-functor stability unit and its direct-images proof;
this node is a supporting Stacks lemma, not the unit statement.

Clause-by-clause rendering:

- The size convention is explicit `universe u w`: rings and scheme/chart sections
  live in u; the source localization has independent Hom universe w. SmallModules
  is the already defined equivalent small affine étale ringed-site model, not a
  scheme replacement or the derived category of the abelian category QCoh.
- A commutative ring: `(A : Type u) [CommRing A]`; there are no restrictions on A.
- Algebraic space over Spec A: `(X : AlgebraicSpace (Spec (.of A)))`.
- The specified map f to the affine scheme, represented as an algebraic space:
  `(f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of A)))))`.
- Separated: `_hsep : MapIsSeparated f`, the representable closed-immersion
  condition on the actual relative diagonal.
- Flat: `_hflat : MapIsFlat f`, quantified over all compatible étale scheme charts.
- Finite presentation: `_hfp` is `MapIsLocallyOfFinitePresentation f ∧
  MapIsQuasiCompact f.hom.hom ∧ MapIsQuasiCompact (pullback.diagonal f.hom.hom)`.
  These are respectively local finite presentation, quasi-compactness, and
  quasi-separatedness; no properness condition is substituted.
- The unbounded derived object: `(K : X.DerivedModules)` and the explicit
  `[HasDerivedCategory.{w} X.SmallModules]` localization binder.
- Quasi-coherent cohomology: `_hK : X.derivedQCohProperty K`, i.e. every homology
  sheaf is quasi-coherent after the fixed inverse module restriction equivalence.
- Every perfect E, without an extra boundedness or QCoh assumption on its binder:
  `_htest : ∀ E : X.DerivedModules, IsPerfectOnRingedSiteOfUniverses ... E → ...`.
  The existing predicate expresses étale-local bounded complexes of finite-free
  retracts. Bounds and ranks vary locally, exactly as in the node.
- Derived tensor is `X.derivedDualityModel.closed.tensor.obj (E, K)`, the existing
  normalized K-flat tensor on the same localization.
- Derived global sections in D(A) are the existing `affineDerivedSections A
  (Over.mk (𝟙 (Spec (.of A)))) (Iso.refl _) X f`. This is the K-injective right
  derived functor of Hom(O_X,-) with its structural A-action. Iso.refl is the
  actual identity of Spec A and adds no hypothesis or arbitrary affine lift.
  The D(A) localization uses the canonical standard universe u+1 selected by
  that existing interface; it imposes no equality on w. This is a presentation
  of the same D(A), not a restriction of the objects being tested.
- Pseudo-coherence of each test is `DerivedCategory.IsPseudoCoherent`, precisely
  existence of an isomorphic bounded-above finite-free A-complex.
- Conclusion `X.IsPseudoCoherent K` is the existing bounded-above finite-free
  local model condition on all covering sieves of the affine étale model. It
  permits different bounds on different covering members. No uniform bound or
  finite Tor dimension conclusion has been added.

Dependency declarations read and used (full signatures and docstrings checked):

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, Mathlib.AlgebraicGeometry.Scheme.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace`, its Modules,
  structureSheaf and etaleTopology, Sheaf.AlgebraicGeometry.AlgebraicSpace.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`,
  Sheaf.CategoryTheory.RingedSiteModules; transparently Mathlib SheafOfModules.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  Mathlib.Algebra.Homology.DerivedCategory.Basic.
- `def-trf-space-quasi-coherent-module`: `AlgebraicSpace.QCoh`,
  Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule, and the unchanged
  Mathlib `SheafOfModules.IsQuasicoherent` used by derivedQCohProperty.
- `def-weil-pbc-strict-perfect-coefficient-package`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`,
  Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses. The independently
  sized site specialization here is u,u,u,w, since the existing affine basis has
  both objects and arrows small in u; no universe equality is imposed on the
  original small étale site, whose objects have universe u+1.
- `def-pur-ringed-site-zeroth-hypercohomology`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`,
  Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses. Its module is
  publicly imported. The node uses full A-valued RΓ, not just additive H^0;
  affineDerivedSections supplies the already-landed structural scalar refinement
  of that same Hom(O,-) K-injective construction. Nothing is redefined or replaced
  by an unstructured additive-group condition.
- `def-pc-ring-pseudo-coherent-complex`: `DerivedCategory.IsPseudoCoherent`,
  WeilConjectures.RingTheory.RingPseudoCoherent.
- Added landed `def-sfb-space-derived-module-calculus`: DerivedModules,
  derivedQCohProperty, derivedDualityModel,
  Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules.
- Added landed `def-sfb-space-morphism-properties`: MapIsSeparated, MapIsFlat,
  MapIsLocallyOfFinitePresentation,
  Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties; quasi-compactness is
  the existing MapIsQuasiCompact from ProperCurveModuli, a transitive import.
- Added landed `def-sfb-space-affine-global-sections`: affineDerivedSections,
  affineScalarSections, affineGlobalScalar,
  Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections.
- Added landed `def-sfb-space-pseudocoherent-complex`: IsPseudoCoherent,
  Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex.

The five statement proof prerequisites have no Lean records or Mathlib matches in
this checkout: space-fp-qcqs-source, space-perfect-tensor-tests-upper-bound,
space-perfect-to-pseudocoherent-tests, space-pseudocoherent-tests-relative and
space-flat-relative-pseudocoherence (each with the `lem-sfb-` prefix). Their names
and steps are retained in the proof docstring. They are not needed to elaborate
the present statement and are not restated. The already-stated proof dependency
lem-weil-pbc-affine-scheme-qcqs is available through the private Mathlib
QuasiSeparated import (and its AffineScheme dependency); the ring pseudo-coherence
proof dependency is also a statement dependency and publicly imported.

Edge cases checked before writing:

- Empty X and the zero ring A are allowed; all local model conditions are
  vacuous or have rank zero models, and no Nonempty assumption appears.
- K=0 and E=0 are included, with rank zero bounded models. The test quantifier
  is not restricted to nonzero or globally free perfect complexes.
- Identity map X=Spec A is allowed; its structural scalar action is the usual
  one. No field, Noetherian, positive characteristic, or nonzero-ring condition.
- K can initially be unbounded in either direction. Only its quasi-coherent
  cohomology is assumed; upper boundedness is a proof step from the tests, not
  a hidden extra hypothesis. Individual test bounds are not assumed uniform.
- Nonproper separated flat finite-presentation spaces are included; the source
  uses finite presentation, not properness. Flatness is retained because Tag
  0GFJ alone yields relative rather than absolute pseudo-coherence.

Searches for an existing statement (recorded by msearch in searches.jsonl):

- LeanFinder: `perfect tensor tests derived global sections detect pseudo coherent
  complexes on flat finitely presented algebraic spaces`: 8 hits, ordinary flat
  morphisms, module tensor exactness, and condensed-module results; none matches.
- Loogle: `"PseudoCoherent"`: 0 hits.
- Mathlib grep via msearch: `pseudoCoherent|pseudo_coherent|pseudocoherent`: 0 hits.
- LeanSearch: `Perfect tensor tests detect pseudo coherent complexes on algebraic
  spaces flat and finitely presented over an affine scheme`: 8 ordinary flat
  module results; none matches this derived algebraic-space criterion.
- rg of WeilConjectures for the item id: no hit. rg for perfect/test names and
  pseudo-coherence found no algebraic-space criterion.
- rg of Sheaf for the item id and perfect/pseudo-coherence found
  PerfectTestsDetectPseudoCoherence.lean, a theorem for schemes, not algebraic
  spaces. It cannot state this node. Other hits were perfect approximation,
  relative perfection, tensor-limit preservation, or pseudo-coherent direct
  image statements. Reused their existing notion APIs as listed above.
- Full proposed declaration name is absent from Mathlib, WeilConjectures,
  Sheaf and dag/lean_names_upstream.json. The scheme theorem has the same last
  component in namespace AlgebraicGeometry, a different full name.

Validation: scompile.py compiled the final module in sandbox and library forms
without errors or warnings (5.2 s and 5.4 s). The prescribed deliver2.py --no-push
reported OK: commit 34812eca738 passes preflight and compiles. No
STATEMENT-DISPUTED issue or statement correction was found.

## Second reading by Q113

A separate self-review pass reopened the item and the final module, as this
single-worker dispatcher explicitly forbids spawning other agents. This is not
represented as an independent agent review; the maintainer performs the independent
review on delivery.

Rechecked A, X, f and the affine target; all three geometric hypotheses are present,
with finite presentation expanded into its three actual conditions. Rechecked the
unbounded K and its quasi-coherent cohomology predicate against the full signature.
The test quantifies over every perfect E in the ambient derived category, uses the
existing K-flat tensor in the stated order, and retains the A-action through the
canonical scalar sections functor. The conclusion uses the existing local finite-free
pseudo-coherence predicate rather than relative perfection or a boundedness assertion.
Read both source lemmas: flatness is exactly what converts their relative conclusion
to the absolute one stated here. The arbitrary source localization universe is
retained; the standard target D(A) is inherited from the existing sections API.

No mathematical mismatch was found. Added the existing hypercohomology dependency
module to the imports to retain the recorded ringed-site cohomology interface; the
scalar RΓ expression remains the precise A-valued existing construction. Four
landed definition nodes were added to stmt_deps to make ownership explicit. No
new nodes, dependency modules, extra theorem statements, or proofs were introduced.
