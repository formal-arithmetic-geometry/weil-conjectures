## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.exists_relativeAmpleLocus` in
`Sheaf.AlgebraicGeometry.SpaceRelativeAmpleLocus`. Its only theorem proof is `sorry`.
The original mathematical statement is unchanged. Its proof docstring reproduces all nine
DAG proof steps and their named inputs, including the non-cartesian approximation step.
The source was read in full locally: Stacks spaces-descent.tex, Tag 0D3D, the scheme-base
proof of (A); spaces-divisors.tex, Tags 0D31 and 0D32, including representability.
No statement correction or dependency repair was needed.

Hypothesis and clause correspondence:

- Scheme base T: `{T : Scheme.{u}}`. Algebraic space X over T: `{X : AlgebraicSpace T}`.
  Viewing all spaces over the named target scheme T introduces no new hypothesis.
- The named morphism f: `(f : X ⟶ schemeSpace (Over.mk (𝟙 T)))`. Its properness is
  `(hf : MapIsProper f)`, the existing conjunction of separatedness, finite type,
  and universal closedness; it does not assert representability of f.
- The original line module: `(L : X.Modules) (hL : X.IsLineModule L)`, on the recorded
  small etale site, locally isomorphic to the structure module.
- Open subscheme A: `∃ A : T.Opens`, with scheme `A.toScheme` and inclusion `A.ι`.
- Every scheme morphism T' → T: `∀ B : Over T`. Factorization is exactly
  `∃ a : B.left ⟶ A.toScheme, a ≫ A.ι = B.hom`; the first biconditional identifies
  this with `IsAmpleSchemeBaseChange f L B`.
- Relative ampleness, including schematicity, is expanded by the new definition node
  below. It uses the actual sheaf fibre product and the canonical tensor pullback of L,
  never an unrelated module or an arbitrary comparison. A chart `U` with
  `IsIso U.obj.hom` represents the entire fibre product. Its module's restriction to
  every inverse image of an affine open of B has an invertibility proof and satisfies
  the existing `Scheme.Modules.IsAmple`. The existential proof argument merely supplies
  the class argument required by that predicate.
- Points exactly the ample geometric fibres: the second clause quantifies over every
  `K : Type u`, `[Field K]`, `[IsAlgClosed K]`, every `a : Spec (.of K) ⟶ T`, and every
  `x : Spec (.of K)`, and says `a x ∈ A ↔ IsAmpleSchemeBaseChange f L (Over.mk a)`.
  Over a field, relative ampleness is absolute ampleness, since the affine top open is
  among the tests; the empty open adds no condition. This includes representability
  of the geometric fibre. Every geometric point occurs, and every point of T admits
  such a geometric point via an algebraic closure of its residue field, in universe u.
- Arbitrary base change: for any `B : Over T`, the open is explicitly `B.hom ⁻¹ᵁ A`.
  For every scheme C and `g : C ⟶ B.left`, factorization through its open subscheme is
  equivalent to the relative-ampleness test on `Over.mk (g ≫ B.hom)`. This is the full
  representing-open characterization for the base-changed family: its C-fibre product
  and module pullback are canonically those of the original family along the composite.
  Thus it identifies the open itself after base change, not merely its set of points.
- In particular X_A is a scheme: the final existential exhibits an etale scheme object
  of the actual fibre product over `A.ι` whose map is an isomorphism of presheaves.
- No Noetherian or quasi-compact condition is imposed on T, B, A, C or their maps.
  All variables and universes are explicitly bound; `autoImplicit` is false.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  a locally ringed space locally affine, and its actual category of morphisms.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `Modules`, `IsLineModule`. Their original definitions
  retain the fppf sheaf and small etale ringed site.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (rank-one local trivializations).
- WeilConjectures.AlgebraicGeometry.Ample:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` (quasi-compact and positive-power affine
  nonvanishing neighbourhoods).
- The recorded enlarged-site module is
  Sheaf.AlgebraicGeometry.SpaceCotangentRingMap, publicly importing the existing
  enlarged-site model. The construction uses its `schemeSpace`,
  `enlargedFibreProduct`, and `enlargedFibreProductFst`, all with their actual sheaf
  fibre-product definitions. The CommRing inverse-image interface is not needed here.
- Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence:
  `Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`; its restriction
  is restriction to opens, its line correspondence supplies ordinary invertibility.
  The statement uses the recorded concrete restriction below, not a chosen equivalence.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties:
  `AlgebraicSpace.MapIsProper`. The owning landed node
  `def-sfb-space-morphism-properties` is added to the item's stmt_deps.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations:
  `AlgebraicSpace.moduleTensorPullback`, the left adjoint of the canonical chart-limit
  direct image with its specified unit, used for every fibre-product projection.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction:
  `AlgebraicSpace.schemeRestriction`, the canonical restriction to Zariski opens.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction publicly exposes the
  upstream `Scheme.Modules.tensorPullback` used for restriction to inverse-image opens.
  These last three definitions belong to the new node's explicit stmt_deps.

Every proof dependency with a recorded Lean module is imported with proof visibility,
except the two already public statement dependencies. The existing Mathlib affine,
quasi-separated and Noetherian interfaces are present via these imports. The following
five proof dependencies have no Lean record or Mathlib match and supply no object needed
for the present statement: lem-sfb-space-relative-ampleness-fpqc-descent,
lem-sfb-space-proper-noetherian-approximation, lem-sfb-space-affine-limits-schematic-stages,
lem-sfb-space-invertible-limit-descent, lem-sfb-space-noetherian-ample-neighbourhood.
Their existing DAG proofs are cited in the docstring; no duplicate statements are added.

Edge cases checked mathematically:

- Empty T: A is empty and all scheme tests have empty source; all clauses hold.
- Empty X: the empty fibre is a scheme and its line is ample vacuously, so A = T.
- Empty B or empty affine open: the fibre or restriction is empty, still included.
- A field base with a schematic ample fibre: A is the whole field spectrum.
- P^1 with O(1), respectively O(-1): the open is the whole base, respectively empty.
- A non-schematic fibre never passes the definition: an arbitrary atlas is insufficient;
  the chart map must be an isomorphism. No representability hypothesis is placed on X
  globally; the conclusion produces it only over A.
- Non-quasi-compact bases and infinite open covers remain admitted.
- All scheme and field tests use the single ambient universe u, so the geometric-point
  condition cannot become vacuous through a smaller independent field universe.
- The identity and arbitrary non-flat base changes are included with no extra condition.

Searches: msearch.py leanfinder, query "For a proper morphism of algebraic spaces the relative
ampleness locus of a line module is open and commutes with arbitrary base change", returned
8 scheme locality/universal-openness hits, none the requested theorem. Loogle query
"AlgebraicGeometry.Scheme.Modules.IsAmple, AlgebraicGeometry.IsProper" returned no hits
(unknown first identifier). Mathlib grep "ampleLocus|RelativelyAmple|relative.*ample" under
AlgebraicGeometry returned 0 hits. LeanSearch query "Relative ampleness of a line module on
an algebraic space after scheme base change means schematic source and ample restrictions
over affine opens" returned 8 affine-locality/base-change hits, no relative-ample predicate.
Project rg searched relative-ampleness names and the item id in both lean/Sheaf and
lean/WeilConjectures; only references and scheme ampleness theorems were found. DAG definition
search and blueprint_refs.py search "relative ample" found no matching definition. Broad
relative/ample DAG hits were inspected against the actual definitions and existing etale-local
theorem. Original tool log records are retained in the new node's mathlib_searches.

Compilation: both delivery modules passed scompile.py against the current server sources,
separately, in dependency order, under the standard 60-second limit. The wrapper's local
private-overlay attempt encountered "No space left on device" and its automatic server
confirmation compiled both modules successfully (1.8 and 2.4 seconds), without warnings.

## New nodes

`def-sfb-space-relative-ample-test` defines `IsAmpleSchemeBaseChange` and its two canonical
projection helpers in `Sheaf.AlgebraicGeometry.SpaceRelativeAmpleTest`. Its source is Stacks
0D31/0D32. The definition unfolds exactly the scheme-base relative ampleness in the item,
with schematicity witnessed by an isomorphism chart. Data is constructed entirely from
existing fibre-product, Yoneda, tensor-pullback and restriction definitions. The searches
above, recorded verbatim as tool log records in its mathlib_searches, found no existing node
or declaration for this predicate. Existing ordinary and algebraic-space notions are reused.
The item cites this new definition, and the existing properness definition; all inherited
statement and proof dependencies are preserved. No other node file is modified.

## Second reading by NL

The delivered section was a self-audit by the delivering worker ("not an independent-agent
review"). It is replaced by the maintainer second reading below (H11 report repair).

Node statement as a list, with the Lean and the verdict:

1. Scheme T [def-pc-scheme]: `{T : Scheme.{u}}`. Correct.
2. Algebraic space X with f : X → T [def-trf-algebraic-space]: `{X : AlgebraicSpace T}`,
   `f : X ⟶ schemeSpace (Over.mk (𝟙 T))` (T as representable sheaf, the terminal space). Correct.
3. f proper = separated, finite type, universally closed: `hf : MapIsProper f`, which is
   `MapIsSeparated ∧ MapIsFiniteType ∧ MapIsUniversallyClosed` (def-sfb-space-morphism-properties,
   a definition node, legitimately added). No representability assumed. Correct.
4. L a line module on X_et: `(L : X.Modules) (hL : X.IsLineModule L)`, IsLineModule = étale-locally
   isomorphic to the unit module. Correct.
5. Open subscheme A ⊂ T: `∃ A : T.Opens`. Correct.
6. ∀ T' → T: factors through A ⇔ L_{T'} relatively ample: clause 1, `∀ B : Over T,
   (∃ a, a ≫ A.ι = B.hom) ↔ IsAmpleSchemeBaseChange f L B`. The new definition requires an étale
   scheme object U of the actual sheaf fibre product X ×_T B with `IsIso U.obj.hom` (the fibre
   product is representable, i.e. X_{T'} is a scheme, not just atlas-covered) and, for every affine
   W ⊂ B, invertibility and `Scheme.Modules.IsAmple` of the ordinary module on p⁻¹(W), obtained as the
   Zariski restriction (`schemeRestriction`) of the canonical tensor pullback
   `moduleTensorPullback (enlargedFibreProductFst …) L`, then ordinary tensor pullback along the open
   inclusion. This is Stacks 0D31 (including representability) on a scheme base. Correct.
7. Points of A = t with L ample on the geometric fibre: clause 2 over every algebraically closed
   `K : Type u` and `a : Spec K → T`. Over a field the top open is affine, so the test is absolute
   ampleness plus schematicity of the fibre (node: "an ample line on an algebraic space over a field
   includes that this space is a scheme"). Every t has such a point (algebraic closure of κ(t) in
   Type u). Quantifying over all geometric points is equivalent (ampleness is invariant under field
   extension, proof step 2). Correct.
8. Formation of A commutes with arbitrary base change: clause 3, for B over T the open
   `B.hom ⁻¹ᵁ A` represents relative ampleness of the C-tests, phrased through X ×_T C along the
   composite `g ≫ B.hom` (canonically X_B ×_B C). Mathematically equivalent to the node; advisory:
   it is a direct corollary of clause 1, since no algebraic space over B is formed.
9. X_A is a scheme: clause 4, an étale scheme object of X ×_T A with `IsIso`. Correct.
10. No Noetherian / quasi-compact hypothesis on T: none present. Universes: one u throughout,
    K : Type u, no restriction. Correct.

Edge cases: T empty (A = ∅, clauses vacuous); X empty (empty fibre product representable by the
empty scheme, A = T); field base; P^1 with O(1)/O(-1); non-schematic fibre (no isomorphism chart).
All covered as in the node.

One definition per notion: no relative-ampleness predicate for algebraic spaces exists in Mathlib,
WeilConjectures or the landed Sheaf tree (AlgebraicSpaceAmpleLocal states the étale-local theorem
inline; Q23 noetherian-neighbourhood uses its own inline form). The new definition node is needed.

Repair made: the new node def-sfb-space-relative-ample-test cited the theorem node
lem-trf-space-enlarged-etale-ringed-site-model for `schemeSpace` and `enlargedFibreProduct(Fst)`.
These are owned by def-trf-scheme-algebraic-space and def-sfb-space-sheaf-fibre-product (both
existing:true on Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite). The node now cites those two
definition nodes, and its module imports EnlargedEtaleRingedSite instead of SpaceCotangentRingMap.
Both modules compile cleanly (1.6 s, 1.7 s). The item keeps its base theorem stmt_dep (not added
by this delivery; advisory only).
