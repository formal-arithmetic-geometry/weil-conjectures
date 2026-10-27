## Worker report

The module `Sheaf.AlgebraicGeometry.RegularSurfaceVectorBundleExtension` states
`AlgebraicGeometry.Scheme.Modules.regularSurfaceVectorBundleExtension`. Its only
proof is `sorry`; it introduces no definitions or additional nodes. The node's
statement, dependencies and proof are unchanged.

Hypothesis and conclusion correspondence:

- The schemes are `X U : Scheme.{u}`, with arbitrary explicit universe `u`.
  An arbitrary `j : U ⟶ X` with `[IsOpenImmersion j]` represents the open subscheme,
  so the theorem also covers open immersions not syntactically chosen as an Opens inclusion.
- Integral X is `[IsIntegral X]`, including nonemptiness. Noetherian X is
  `[IsLocallyNoetherian X] [CompactSpace X]`, precisely the two fields of Mathlib's
  `IsNoetherian X`; compactness imposes no separation condition.
- Regularity is `hregular : IsRegularScheme X`, the recorded scheme notion including
  local Noetherianity and regular local stalks. Its local Noetherian conjunct agrees
  with the separately supplied Noetherian hypothesis; no regularity of U is assumed.
- Dimension at most two is `hdim : topologicalKrullDim X ≤ 2`. The node explicitly
  cites def-kun-topological-krull-dimension for scheme dimension. This is the usual
  dimension of X, distinct from the local dimension condition on omitted points.
- `hcodim : ∀ x : X, x ∉ Set.range j → 2 ≤ ringKrullDim (X.presheaf.stalk x)`
  expresses the stated condition at every point of the complement, using the actual
  image of the given open immersion and the actual local ring of X.
- The first conjunct says restriction preserves finite locally free modules and
  that the canonical unit `E ⟶ j_*(E|_U)` is an isomorphism for each such E.
  It uses `(restrictAdjunction j).unit.app E`, rather than an unspecified comparison.
- The second conjunct says the actual `(pushforward j).obj V` is finite locally
  free for every finite locally free V on U and the canonical counit
  `(restrictAdjunction j).counit.app V` is an isomorphism. Its source is exactly
  the restriction of that direct image, and its target is V.
- The third conjunct quantifies over all module morphisms a between restrictions
  of bundles E,F on X and asserts `∃! b : E ⟶ F, (restrictFunctor j).map b = a`.
  This is precisely existence and uniqueness of the extension. Taking E,F to be
  the direct images from the second conjunct includes maps between the specified
  extensions of two bundles on U; the counit identifies their restrictions with
  the original bundles.
- The fourth conjunct explicitly supplies an equivalence of the full subcategories
  cut out by the existing `SheafOfModules.isFiniteLocallyFree`. Two natural
  isomorphisms, after the full-subcategory inclusions, identify its functor with
  the canonical restriction and its inverse with the actual direct image.
  Thus an unrelated equivalence of the underlying abstract categories cannot satisfy
  the statement. All module morphisms are retained. The natural isomorphisms are
  propositionally asserted with `Nonempty`, rather than selected from bare existence.

Dependency declarations read and reused:

- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- def-weil-regular-scheme: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- def-weil-pbc-krull-dimension-ring: `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- def-sc-finite-locally-free-sheaf:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree` and `SheafOfModules.isFiniteLocallyFree`.
- def-kun-topological-krull-dimension: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsLocallyNoetherian`.
- def-weil-pbc-quasi-compact-scheme: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- def-pc-module-pullback: imported its recorded
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`; read
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`, its normalized
  unit characterization, identity and composition comparisons. For an open immersion
  the statement uses the existing canonical `restrictFunctor`, `pushforward` and
  `restrictAdjunction` of `Mathlib.AlgebraicGeometry.Modules.Sheaf` (publicly available
  through that dependency). These are exactly the ordinary restriction/direct image;
  no new pullback or adjunction is defined.
- Proof-only pqf-lem-coherent-ft-locnoeth imports
  `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`, declaring
  `AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`.
- Proof-only rem-pc-regular-normal imports `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`,
  declaring `AlgebraicGeometry.regular_normal_and_normal_decomposition` (clause 1).
- The proof dependencies lem-sfb-regular-surface-reflexive-locally-free and
  lem-sfb-normal-reflexive-open-equivalence have no Lean records at the time of
  reading and are not required to type this statement. Their full mathematical
  statements were read and the proof docstring cites them; there is no module to
  import. This delivery does not duplicate them.

Sources checked: local `literature/stacks-project/divisors.tex`, labels
`lemma-reflexive-S2-extend` (Tag 0EBJ) and `lemma-reflexive-over-regular-dim-2`
(Tag 0B3N), including their proofs; the latest blueprint unit sk-thm-sf-ctf-stability
and its direct-images statement/proof. The proof docstring includes the node's four
steps, with the coherence and normality hypotheses checked and the explicit formula
for morphism extension. No source-based correction is needed.

Edge cases checked before writing: an integral X is nonempty, so the empty scheme is
correctly excluded by the node itself. U may syntactically be empty, but for a nonempty
integral X the codimension condition fails at its generic point. Dimension zero or
one forces the complement empty; the identity/arbitrary isomorphic open immersion
case is included. Rank zero bundles and their maps are included, as are variable ranks:
the class is finite locally free, not fixed positive rank. No characteristic, field,
separatedness or affine hypothesis is introduced. In dimension two the complement
condition is at each omitted local ring, not merely a dimension bound on the complement.
Without regularity, reflexive sheaves on a singular surface need not be locally free;
without codimension two, even the trivial bundle need not be recovered from direct
image. Both necessary hypotheses are present.

Searches performed through the prescribed `msearch.py`, with outputs inspected:

- leanfinder: "Finite locally free sheaves on a regular Noetherian surface extend by
  direct image across codimension two and restriction is an equivalence". Eight hits,
  including `restrictFunctorAdjCounitIso`, `restrictAdjunction`,
  `instIsIsoFunctorCounitRestrictAdjunction` and `restrictFunctorIsoPullback`.
  These supply restriction adjunctions for all open immersions, not extension or
  a unit isomorphism for finite locally free sheaves on a regular surface.
- loogle: `"IsLocallyFree"`. Eleven hits, including `SheafOfModules.IsLocallyFree`,
  local generator data and its basic instances; no surface extension theorem.
- leansearch: "Restriction of finite locally free sheaves across codimension two in
  a regular surface is an equivalence". Eight hits, including `Scheme.Modules.restrict`,
  `restrict_obj` and open-immersion facts; no extension theorem.
- grep (Mathlib/AlgebraicGeometry):
  `reflexive.*regular|regular.*reflexive|Hartogs|punctured`, zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf`:
  `regular.*[Ss]urface|[Ss]urface.*[Ee]xten|[Vv]ectorBundle.*[Ee]xten`.
  Only unrelated regular-surface resolutions, depth/flatness results and vector-bundle
  geometry, none stating this theorem. Wider finite-locally-free searches located
  the already recorded variable-rank class and full-subcategory predicate.
- `grep -rn lem-sfb-regular-surface-vector-bundle-extension lean/WeilConjectures`:
  no existing declaration carrying this node. Exact proposed-name search in both
  project roots, Mathlib and `dag/lean_names_upstream.json`: no collision.

## Second reading by Q119

A separate read of the completed node copy and final signature checked all the
correspondences above: X is integral, Noetherian and regular, global dimension is at
most two, j is any open immersion and every omitted point satisfies the stalk-dimension
bound. The output is a full-subcategory equivalence tied naturally to restriction and
actual direct image, together with unit, counit, local-freeness and unique-map-extension
clauses. A compiler check caught an unavailable ring-sheaf alias; it was replaced by
Mathlib's own `X.ringCatSheaf`/`U.ringCatSheaf`, the exact ring sheaves defining
`Scheme.Modules`. No mathematical correction was required. This is the worker's own
second pass; no other agent was started, as the dispatcher brief prohibits that.
The maintainer's independent review remains the independent reading of the delivery.
