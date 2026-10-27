## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGradedCohomologyFinite` states
`AlgebraicGeometry.AlgebraicSpace.space_graded_cohomology_finite`, with its entire
proof postponed by `sorry`. The only other declaration is the transparent abbreviation
`gradedCohomologyPiece` for existing underlying-additive sheaf cohomology. There is
no new axiom, theorem assumed as input, or definition with postponed data.

I read the current node, all statement-dependency node statements and records,
the recorded declarations and their docstrings, and the complete local source of
Stacks `spaces-cohomology.tex`, `lemma-graded-finiteness` (08AT), including its proof.
The inherited rejection concerns an unchanged stage-1 delivery of an accepted split.
The current item is stage 2, is in `coord/queue.tsv` with stage 2, has no Lean record,
and has no released repair note. The stage-handoff instruction in
`coord/brief-stage2.md` section 0 expressly distinguishes these situations. This
packet preserves that accepted split, its statement, and all proof steps.

Hypothesis and clause correspondence:

- Commutative Noetherian A is `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- Commutative unital A-algebra B is `[CommRing B] [Algebra A B]`. Finite algebra type
  is `[Algebra.FiniteType A B]`. The dependency's current primary record is
  `RingHom.FiniteType`; its recorded Mathlib match is `Algebra.FiniteType`, and
  `RingHom.FiniteType (algebraMap A B)` is equivalent to the displayed class.
- `graded : ℕ → Submodule A B` supplies the A-submodules B_k.
  `hgrading : DirectSum.IsInternal graded` says exactly that their sum is internal
  and exhaustive: each b has a unique finite homogeneous decomposition.
  `hunit` supplies 1 in degree 0, `hmul` gives B_k B_l contained in B_(k+l), and
  `hscalar` makes every image of A have degree 0. These are the node's four grading
  conditions. The use of submodules fixes their A-action to that of B.
- Algebraic spaces are the existing `AlgebraicSpace S`. `Y : Over S` and
  `e : Y.left ≅ Spec (.of A)` express the affine scheme target in the common
  ambient category; `f : X ⟶ schemeSpace Y` is precisely its named structural
  morphism. This includes the literal target by taking S=Spec A, Y=Over.mk(id),
  and e the identity, and also allows the arbitrary ambient scheme of the existing
  algebraic-space framework. `hf : MapIsProper f` is the recorded separated,
  finite-type, universally closed predicate, without extra finiteness hypotheses.
- The homogeneous module pieces are `G : ℕ → X.Modules`. This is the existing
  category of module sheaves on the small étale ringed site. `hG` says that each
  piece satisfies Mathlib's site-local quasi-coherence predicate. That is exactly
  the recorded `def-trf-space-quasi-coherent-module` predicate, not scheme coherence
  or a locally free substitute.
- The graded module over the *specified* pulled-back algebra is encoded by its
  homogeneous constant-section multiplications
  `mu : ∀ r k, graded k → (G r ⟶ G (r+k))`. These are actual O_X-linear sheaf maps;
  hence restrictions and linearity in the module argument are built in. `hadd`
  gives additivity in b and `hassoc` gives the product law with the actual product
  in B. The `HEq` only handles natural-number reassociations in the target degree.
- `hbase` fixes the A-action to multiplication by f-sharp(a) on EVERY chart. Its
  function is the actual map from A to Gamma(U,O_U), namely the inverse Gamma-Spec
  comparison followed by regular-function pullback along the chart's composite
  `U → Y → Spec A`. The first arrow is `yoneda.preimage` of `U.obj.hom ≫ f.hom.hom`.
  Taking a=1 gives the unit law; this is not an arbitrary module action.
- More explicitly, these data encode exactly, without choosing another algebra,
  the node's bilinear action of Bcal_k=f^*(B_k tilde). Locally a tensor c⊗b acts by
  c mu(b). Additivity and O-linearity, together with `hbase` and `hassoc` applied to
  a degree-zero scalar, give A-balancedness. Thus the tensor universal property
  extends this to Bcal_k; sheafification extends it from local tensor sections.
  Conversely restriction to 1⊗b recovers mu. This correspondence is inverse and
  preserves the unit, associativity and restriction laws. It is the same standard
  action encoding used by the published scheme graded-finiteness statements; no
  auxiliary algebra, arbitrary pullback comparison, or stronger assumption appears.
  The module imports the recorded canonical tensor-pullback and Zariski/étale
  equivalence modules; the above is their universal-property presentation.
- `hfinite` is precisely étale-local finite generation by homogeneous sections.
  For every chart U, a covering sieve R supplies neighbourhoods V with finitely
  many sections `s : ∀ a : Fin n, G_(d a)(V)`. For every W→V, degree r and section
  t of G_r(W), a covering sieve T of W makes the restriction of t belong to the
  O_X(Z)-span of `mu (d a) (r-d a) b` applied to the restricted s_a, with `d a ≤ r`.
  A submodule span means finite linear combinations. This is equivalent to using
  arbitrary Bcal_(r-d a) coefficients: every such coefficient is locally a finite
  sum of c⊗b, and c can be absorbed into that span; conversely each span term is
  an allowed Bcal multiple. Refining finitely many covers handles all terms at
  once. Covering sieves are exactly the topology of the recorded étale site.
  No global generators or surjectivity on all sections is assumed.
- `q : ℕ` ranges over exactly the stated q≥0. `gradedCohomologyPiece X (G r) q`
  abbreviates `Sheaf.H` of the underlying additive sheaf of the restriction to
  the existing small affine étale model. This is ordinary abelian-sheaf cohomology
  (Ext from the constant integer sheaf, equivalently right-derived global sections).
  The restriction is the specified equivalence, not a freely chosen model or
  arbitrary resolution. It retains section universe u, and standard small-site
  Grothendieck/HasExt instances supply the cohomology without new hypotheses.
- The conclusion existentially supplies `mod : Module B (DirectSum ℕ ...)`, the
  requested B-module structure on the precise additive direct sum. It is not
  merely finiteness conditional on an unproved existence of an action.
- Its finite-sum identity gives exactly the requested action formula: an arbitrary
  finite homogeneous scalar sum over K acts on an arbitrary finite vector sum over
  R by the double sum of the actual `Sheaf.H.map` of mu, inserted in degree r+k.
  Collecting the terms r+k=d is exactly the node's displayed degree-d convolution.
  Every scalar is such a finite sum by hgrading, and every direct-sum vector is
  such a finite sum by its definition. Conversely singleton K and R recover each
  homogeneous action. Thus the equation uniquely determines the action on the
  entire additive group, and includes both empty-support cases.
- `@Module.Finite B _ _ _ mod` asserts finite generation for this very action.
  In degree zero, a homogeneous scalar from A acts by the cohomology map induced
  by the `hbase` multiplication, so the node's final normalization is retained.

Dependency declarations used/read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; Gamma-Spec normalization from `Scheme.ΓSpecIso`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper` and
  its separated, finite-type and universally closed components.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  `moduleTensorAdjunction`, `moduleTensorSection`, and the normalized chart-limit
  `ModuleDirectImageModel`; their tensor universal property explains the encoding.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `AlgebraicGeometry.Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`,
  including its actual tensor-section and scalar normalizations.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, which is the
  full subcategory for the unchanged Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules.toSheaf`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings` and its
  retained `Sheaf.H` convention; `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`:
  `Sheaf.H` and `Sheaf.H.map`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- The two additional landed statement dependencies are
  `def-trf-scheme-algebraic-space`, declaration `schemeSpace` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, and
  `def-sfb-space-small-ringed-model`, declarations `smallModuleRestriction`,
  `smallStructureRings`, `smallEtaleModelTopology`, `smallModuleEquivalence` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`. Both already have usable
  Lean records. These are added to stmt_deps under the landed-dependency rule.
  No dependency record is replaced and no new definition node is needed.

Available proof dependencies are imported privately: `Mathlib.AlgebraicGeometry.Noetherian`,
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`Sheaf.CategoryTheory.RingedSiteLeraySpectralSequence`,
`Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing`, and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
The finite-type/Noetherian result is already in the public finite-type module, and
space morphism properties are already public. Other proof prerequisites have no
recorded declaration at this reading and so cannot yet be imported; their nodes
and their complete proof plan remain unchanged. There is no new import cycle.

Edge cases checked before writing:

- The zero ring, zero algebra, empty space and zero graded module are allowed:
  no nontriviality, point, nonempty-cover, or nonzero-piece binder is added.
- n=0 in hfinite is allowed; its empty span is zero. On empty charts the topology's
  empty covers remain available. Local generators may have arbitrary degrees.
- The condition d_a≤r excludes truncated subtraction artifacts. `HEq` handles only
  equality of degrees; it does not forget which sheaf or action is being used.
- B concentrated in degree zero gives ordinary finite coherent cohomology;
  positive degrees, including infinitely many nonzero pieces, are retained.
- q=0 is included. There is no improper assumption of vanishing in positive degree.
- Empty K or R makes both sides of the action equation zero. Singleton K={0}
  with b=algebraMap(a) gives the exact A-scalar normalization via hbase.
- Universe u is arbitrary and is the existing scheme/ring/module size convention.
  The full chart category still has objects in u+1 and morphisms in u; restriction
  to its published u-small affine model avoids imposing equality of those sizes.

Searches (all performed with msearch.py or read-only rg/grep):

- LeanFinder: "Cohomology of a finite type graded quasi coherent module on a proper
  algebraic space is finite over the graded algebra". Eight results concerned
  Proj finite type, module-sheaf generators and cotangent homology; none is this theorem.
- LeanSearch: "Finite generation of graded cohomology over a finite type algebra
  on a proper algebraic space". Returned graded-algebra finite generators,
  `GradedAlgebra`, `Module.Finite.finiteType`, and finite ring maps, not space cohomology.
- Loogle: `DirectSum.IsInternal, Module.Finite`. Seven results concerned traces
  on finite direct sums and primary torsion decompositions; none is this theorem.
- Mathlib grep: `graded.*cohomology|cohomology.*graded`: zero matches.
- rg over `lean/WeilConjectures` with the same conceptual patterns found the
  unrelated filtered-complex results and the graded cohomology action for schemes.
  `grep -rn` for the item id in that tree returned no occurrence.
- rg over `lean/Sheaf` located `Paper/GradedCohomologyModuleFinite.lean` and the
  graded finiteness wrapper. I read their complete signatures: their X is a scheme,
  with Zariski O_X-modules and scheme properness, so they do not state this node.
  The existing `GradedSheafAlgebra`, `GradedSheafModule`, and local graded-generation
  predicates are likewise scheme/Zariski-specific, so they cannot be used verbatim
  for this algebraic-space statement. The present theorem uses inline homogeneous
  maps and the existing Mathlib sheaf notions, with no duplicate graded-sheaf definition.
- rg for the two new full declaration names in Mathlib/project source and
  `dag/lean_names_upstream.json` found no existing declarations.

Validation: scompile.py compiled the delivered module in both sandbox and library
module modes on the server, cleanly with no warnings or errors (20.0 s and 27.1 s
respectively). The earlier module-mode probe established that the chosen small-site
cohomology expression has type `Type u`; a stray diagnostic command referring to
out-of-scope variables was removed before the clean final compile. No global or
local direct Lean build was run.

No statement correction, disputed assertion, new definition node or dependency-module
repair is claimed. The module docstring explains the tensor-universal-property
encoding, and the theorem docstring carries all eight steps of the accepted proof.

Delivery validation: `deliver2.py Q21 lem-sfb-space-graded-cohomology-finite --no-push`
printed `OK (dry run): commit 39b83639802 passes the preflight and compiles`.
The maintainer's independent review is the second reading; no other worker was
started and no independent self-review is claimed.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
