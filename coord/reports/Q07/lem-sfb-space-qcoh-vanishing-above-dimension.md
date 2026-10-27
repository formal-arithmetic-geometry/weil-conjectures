## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceCohomologyAboveDimension` states
`AlgebraicGeometry.AlgebraicSpace.isZero_moduleCohomology_of_dimension_le` with one
`sorry`. There are no new definitions or proved theorems. Its declaration docstring
carries all five steps of the accepted proof, including the top-degree restriction
surjectivity needed at q=d+1. Source: Stacks spaces-cohomology.tex, Tag 0A4R(1),
and the paragraph preceding that lemma, read in the local Stacks source.

The original natural-language statement is unchanged. The only node changes are its
Lean record and the addition of two already-landed statement dependencies:
`def-sfb-space-absolute-quasi-separated` and `def-sfb-space-small-ringed-model`.
This is the brief's permission to add already-recorded notions to stmt_deps.
Neither dependency's node or module is changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary base scheme B is `{B : Scheme.{u}}`. There is no property of B.
- X is an algebraic space over B: `(X : AlgebraicSpace B)`, the recorded fppf-sheaf
  full subcategory with representable diagonal and surjective etale scheme atlas.
- Quasi-compactness means that a quasi-compact surjective etale scheme atlas exists:
  `hqc : ∃ (U : Over B) (a : yoneda.obj U ⟶ X.obj.obj), CompactSpace U.left ∧
  IsEtale a ∧ IsSurjective a`. This retains exactly the atlas definition in the node,
  rather than assuming quasi-compactness of an unrelated structure map.
- Absolute quasi-separatedness is `hqs : IsAbsolutelyQuasiSeparated X`. This is the
  existing affine-test predicate of def-sfb-space-absolute-quasi-separated; its
  source is Stacks 0AHR(3), equivalent to quasi-compactness of the absolute diagonal.
  In particular, no quasi-separatedness of B or relative-only diagonal is substituted.
- The point space and its topology are `Point X.obj.obj` with the recorded
  `pointTopologicalSpace` instance. This is final for all representable etale scheme
  charts, hence the quotient topology of any surjective etale atlas.
- The integer bound d≥0 is `(d : ℤ) (hd : 0 ≤ d)`. The dimension condition is
  `topologicalKrullDim (Point X.obj.obj) ≤ (d.toNat : WithBot ℕ∞)`. Because d≥0,
  d.toNat represents exactly d, including zero, in the dimension codomain.
- An arbitrary quasi-coherent O_X-module G is `(G : X.QCoh)`. Its underlying object
  `G.obj` is in all module sheaves, with Mathlib's local-presentation predicate.
  There is no coherence or finite-generation condition.
- The all-module injective-resolution computation is
  `(I : InjectiveResolution (X.smallModuleRestriction.obj G.obj))`.
  `smallModuleRestriction` is the already-recorded equivalence to modules on the
  small affine etale skeleton. It restricts actual chart sections, with the same
  coefficient universe and the same structure rings. It therefore preserves the
  structure module and global sections, as well as injectives and resolutions.
  I ranges over resolutions in **all** such modules, not in QCoh(X). The equivalent
  small site has a Grothendieck abelian module category by the existing
  `SheafOfModules.isGrothendieckAbelian`; enough injectives and injective resolutions
  follow from Mathlib's standard theorems. Thus this resolution parameter is an
  arbitrary computation of H^q, not an added existence hypothesis or a vacuous test.
- Every integer q>d is `(q : ℤ) (hq : d < q)`.
- `preadditiveCoyoneda.obj (op (SheafOfModules.unit X.smallStructureRings))` is the
  additive global sections functor Hom(O_X,-). Mathlib's `unitHomEquiv` identifies
  these module maps with compatible section families by evaluation at 1; its inverse
  takes a compatible family s to a↦a*s. This is the same standard global-sections
  model already used by def-pur-ringed-site-zeroth-hypercohomology.
- `mapHomologicalComplex (ComplexShape.up ℤ)` applies that functor termwise to
  `I.cocomplex.extend ComplexShape.embeddingUpNat`, the injective resolution extended
  by zero to integer degrees. Taking `.homology q` is precisely H^q(X,G), and `IsZero`
  states its vanishing as an abelian-group object. No replacement by abelian-sheaf
  injectives or by cohomology internal to the quasi-coherent category is made.
- No Noetherian, separatedness, properness, coherence, flatness, finite type,
  connectedness, nonemptiness, or additional size hypothesis occurs.

Recorded dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme |
| def-trf-algebraic-space | Sheaf.AlgebraicGeometry.AlgebraicSpace | AlgebraicGeometry.AlgebraicSpace; Modules; structureSheaf; IsEtale; IsSurjective |
| def-a1-space-point-topology | Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology | AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension | topologicalKrullDim |
| def-trf-space-quasi-coherent-module | Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule | AlgebraicGeometry.AlgebraicSpace.QCoh |
| def-weil-sheaf-of-modules-category | Sheaf.CategoryTheory.RingedSiteModules | CategoryTheory.ringedSiteModules |
| def-sp-injective-resolutions | Mathlib.CategoryTheory.Preadditive.Injective.Resolution | CategoryTheory.InjectiveResolution; cocomplex |
| def-sfb-space-absolute-quasi-separated | Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated | AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated |
| def-sfb-space-small-ringed-model | Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel | smallModuleRestriction; smallModuleEquivalence; SmallModules; smallStructureRings |

All presently recorded project modules of proof dependencies are imported without
`public`. Unstated proof prerequisites have no imports yet:
lem-sfb-qcqs-space-splitting-filtration, lem-sfb-space-etale-atlas-topological-dimension,
lem-sfb-space-qcqs-permanence, lem-sfb-spectral-module-top-degree-restriction, and
lem-sfb-space-derived-hom-mayer-vietoris. Mathlib proof leaves are available through
the corresponding imports (dimension monotonicity, separated implies quasi-separated,
and spectrality of qcqs schemes). No proof-dependency record is changed.

Edge cases checked before writing and again against the signature:

- Empty X and the empty scheme atlas are allowed. The point dimension is bottom,
  so every nonnegative bound is admissible, and all its module cohomology vanishes.
- d=0 is included and the conclusion covers every positive integer q.
- q=d is excluded as required: the theorem does not assert top-degree vanishing.
- Infinite-dimensional spaces do not satisfy a finite dimension bound; no dimension
  truncation or finite-dimensionality class silently changes this implication.
- The zero module is included by the same quasi-coherence predicate and resolution.
- Non-Noetherian qcqs spaces and non-quasi-separated base schemes are allowed.
- q is genuinely integer-valued; extension by zero is explicit. As q>d≥0, these
  cohomology degrees are positive and agree with ordinary resolution-derived functors.
- Site object universe u+1 and section universe u are retained. The existing small
  affine model supplies a genuine equivalent site, not an extra universe equality.

Searches performed using the prescribed wrapper, with output also in searches.jsonl:

1. LeanFinder: "Quasi coherent module cohomology on a quasi compact quasi separated
   algebraic space vanishes above topological Krull dimension". Eight hits: section
   localization for qcqs schemes, abstract derived-category vanishing, Sheaf.H, and
   injective-dimension criteria. None states this algebraic-space vanishing theorem.
2. Loogle: `"cohomology", "krullDim"`. Zero hits.
3. Mathlib grep: `cohomology.*(dimension|krullDim)|AlgebraicSpace|vanishing.above.dimension`.
   Zero hits.
4. LeanSearch: "Quasi coherent cohomology of qcqs algebraic spaces vanishes above
   dimension". Eight hits on IsQuasicoherent/local presentations and localization
   of scheme sections; no matching theorem.
5. rg in lean/WeilConjectures and lean/Sheaf for the item id, cohomology/dimension
   patterns, and `vanishing_above_dimension|isZero_moduleCohomology_of_dimension_le|moduleCohomology.*dimension`;
   grep -rn of the exact item id in lean/WeilConjectures; rg of the proposed name in
   dag/lean_names_upstream.json. No exact declaration. The nearby existing
   AlgebraicSpaceGlobalSectionsAmplitude theorem supplies an unspecified finite bound,
   not the dimension bound here. SpectralSpaceCohomologyDimension applies to abelian
   sheaves on spectral topological spaces, not to modules on algebraic-space etale sites.
6. Searched the existing algebraic-space modules for cohomology/global-sections and
   absolute quasi-separatedness. Reused the latter and the small affine ringed model.
   Mathlib's unitHomEquiv and additive coyoneda provide sections without a new definition.

No statement dispute, correction, new definition node, or dependency repair is needed.

## Second reading by Q07

Self-review with the source, node, dependencies and final signature open: the atlas
existential has exactly compactness, etaleness and surjectivity; absolute, rather than
relative, quasi-separatedness is used. The dimension is the field-point quotient's
Krull dimension. d and q are integers and the nonnegative bound is explicit. G belongs
to the original QCoh category and the resolution belongs to all modules on the existing
equivalent small site. Hom from the unit followed by integer-degree homology computes
exactly the stated right-derived global sections. No source hypothesis is added.

The first compile exposed a missing zero-object instance for the larger chart encoding.
Reusing the already-landed small ringed model resolved this without changing the source
statement or coefficient size. A formatting error in field notation and a line-width
warning were repaired. The proof docstring retains the q=d+1 surjectivity step.
No second agent was started, as the dispatcher brief prohibits it; the maintainer's
independent review remains the independent reading.

## Validation

Validation used only the prescribed scompile.py and deliver2.py wrappers.

- Final scompile.py: both sandbox module and actual library module compile cleanly,
  2.4 seconds each, no errors or warnings.
- deliver2.py --no-push: OK; commit 14165b7556a passed server preflight and per-file
  compilation, with nothing pushed.
- The actual delivery rechecks the same module and final report before its push.
