## Worker report

Q03, stage 2, 2026-10-23 UTC. This delivery states
`AlgebraicGeometry.NodalIdealScalarGluing.nodal_ideal_scalar_gluing` in
`Sheaf.AlgebraicGeometry.NodalIdealScalarGluing`. Its only postponed proof is that named
DAG theorem. The seven auxiliary definitions have real data, no choice from a postponed
existence claim, and source/blueprint docstrings. They belong to this node's coefficient
criterion, as permitted by the missing-helper rule. There are no new nodes, dependency
repairs, or statement corrections.

The inherited ending was a stage-1 refusal. The current brief-stage2.md section 0 explicitly
says that a reviewed split is input to stage 2 and an old stage-1 BLOCKED ending is not a
stage-2 tool failure. The live item has no lean record. Its accepted statement, proof,
proof_deps, source and review are preserved. The only additional field change is adding
five already-landed definition dependencies for the actual reused interfaces, permitted by
brief-stage2 section 5: reduced-normalization, marked-ideal-order, module-stalk-functor,
field-linear-module-cohomology-operations and scalar-global-sections-comparison.

Hypothesis and clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Nonempty projective reduced k-scheme: `(X : Scheme.{u})`, structural map
  `p : X ⟶ Spec (.of k)`, `[IsHProjective p]`, `[Nonempty X]`, `[IsReduced X]`.
  H-projectivity is the node's finite-projective-space embedding convention.
- Pure dimension one: `hpure : X.IsPureDimension 1`.
- Smooth except at split nodes: `hnodal` quantifies over closed points outside
  `p.smoothLocus`. It supplies the ring equivalence between the maximal-ideal completion
  and `MvPowerSeries (Fin 2) k / (X 0 * X 1)`, together with its compatibility with every
  constant `a : k`. This is precisely a k-algebra identification, not merely a ring
  isomorphism. The smooth locus is Mathlib's recorded Smooth interface, not a substitute
  notion of regularity or formal smoothness at a local ring.
- The components: `irreducibleComponents X`; existing
  `X.reducedNormalizationComponent C` is the reduced component BEFORE normalization.
  `componentι C` is its vanishing-ideal subscheme inclusion. No enumeration, finiteness,
  smoothness of components, or normalization of a self-node is assumed. Finiteness follows
  from the projective curve hypotheses, as in the node proof.
- Invertible module: `(L : X.Modules) [L.IsInvertible]`.
- Arbitrary zero-dimensional closed cluster: `(T : Scheme.{u}) (i : T ⟶ X)` with
  `[IsClosedImmersion i]` and `hdimT : topologicalKrullDim T ≤ 0`. The inequality includes
  the empty scheme, whose dimension is bottom. No reducedness, Cartier or smooth-support
  condition is present. `i.ker` is the recorded quasi-coherent ideal sheaf.
- Ideal tensor line: `i.ker.toModules ⊗ L` uses the existing monoidal tensor construction.
  `twistι` is `i.ker.toModulesι ▷ L ≫ (λ_ L).hom`, the canonical inclusion into L.
- s in H^0: `scalarObj p (i.ker.toModules ⊗ L) (op ⊤)` is ordinary global sections with
  k-scalars restricted along p. The existing `scalarGlobalSectionsEquiv` identifies this
  with degree-zero module cohomology. It is not a different cohomology theory.
- Regard sections as L-sections: `ambientSection` applies `twistι.app ⊤`.
- Nonvanishing at every component generic point: `hs` quantifies over C and every ξ with
  `IsGenericPoint ξ C.val`, requiring the ambient section's L-germ to be nonzero.
  The reduced projective curve has these generic points; its generic local rings are
  fields. No stronger nowhere-vanishing condition is imposed.
- W_s: the existential submodule W has its membership predicate specified by an iff,
  for EVERY section t. On each reduced component it restricts, by the existing
  `tensorPullbackTopSection`, to a scalar multiple of the restriction of s. The scalar
  is inserted through `scalarMap (componentι C ≫ p) ⊤`, so the formula is in the actual
  pulled-back line bundle. W is not an unconstrained subspace hypothesis.
- Coefficient map: `c : W →ₗ[k] (irreducibleComponents X → k)` is accompanied by its
  componentwise restriction formula for every t and C. Generic nonvanishing uniquely
  determines c by that formula. `Function.Injective c` is the requested injectivity.
- Completed full ideal: `completedIdeal i.ker x` maps the existing
  `HilbertSamuel.stalkIdeal i.ker x` along the actual completion map.
- Local frame and completed germ: e is any linear equivalence from the stalk of L to
  the local ring. `completedValue` applies e to the germ of the ambient s, then the
  completion map. Any local frame induces such an equivalence; conversely a basis of an
  invertible stalk extends to a local frame. This is not an extra triviality assumption.
- The branch pair: put R = completed local ring, J = completedIdeal i.ker x,
  P = completedIdeal (componentι C).ker x, Q = completedIdeal (componentι D).ker x,
  and z = completedValue. The pair `(f,0)` in `R/P × R/Q` lies in the image of J iff
  `∃ r ∈ J, r-z ∈ P ∧ r ∈ Q`. Its negation is `Constrained J P Q z`.
  At a node joining distinct components, P and Q are the two minimal branch primes,
  so R/P and R/Q are k[[u]] and k[[v]], in the corresponding order. This is the same
  membership test as the node, with the branch rings written in their canonical quotient
  form. Crucially r must be IN J IN R: the test includes the equal-constant condition.
  Replacing J by its two separate branch extensions would give a false weaker criterion;
  this delivery does not do that.
- Exact image: `∀ a, a ∈ LinearMap.range c ↔ ...` requires equality a C = a D at every
  closed nonsmooth point on distinct components whenever `constrainedAt` holds. It
  quantifies over all frames, a choice-independent expression of the same condition.
- Frame and ordering invariance: the second conjunct compares `constrainedAt` for any
  e,e' and swapped C,D. The pair criterion and the fact s belongs to J identify the
  swap with subtraction from s, so this includes independence of both choices.
- Presentation invariance: the third conjunct transports J,P,Q and z by every scalar-
  compatible nodal ring equivalence ρ. `Ideal.map ρ.toRingHom` is the transported ideal;
  `Constrained` on the presented ring is equivalent to the intrinsic test. Since P,Q
  are defined by the actual reduced components, this is independence of arbitrary
  compatible nodal presentations, including relabelling the two minimal primes.
- Self-nodes: the image condition quantifies only over C ≠ D. A self-node has one
  component coefficient and imposes no additional equation. No connectedness assumption
  appears anywhere. No characteristic restriction or extra universe equality appears.

Definitions and dependency declarations reused (read from their source and node records):

- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`, the algebraically-closed clause of
  def-weil-algebraic-closure's mathlib_match (AlgebraicClosure itself is unnecessary).
- Mathlib.Topology.Irreducible: `irreducibleComponents`, `IsGenericPoint` and closedness of
  components, as recorded by def-weil-irreducible-components.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `Scheme.Modules.IsInvertible` and its existing monoidal tensor instance.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module: `toModules`, `toModulesι`.
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic: `Scheme.Hom.ker`, `vanishingIdeal`,
  `subschemeι`. These are the node's recorded ideal-sheaf construction and its bridge.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsHProjective`.
- Mathlib.AlgebraicGeometry.Properties: `IsReduced`.
- Sheaf.AlgebraicGeometry.PureDimension: `Scheme.IsPureDimension`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`, `Scheme.Hom.smoothLocus`.
- Mathlib.RingTheory.AdicCompletion.Basic and Algebra: `AdicCompletion` and its actual
  algebra map; Mathlib.RingTheory.MvPowerSeries.Basic: `MvPowerSeries`, `X`, `C`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  `SheafOfModules.cochainModulesMonoidal`, public import of the recorded tensor interface.
- WeilConjectures.Topology.RingedSpaceModuleCohomology: `moduleCohomology`,
  `globalSectionsFunctor` (publicly reexported by ScalarGlobalSectionsComparison).
- Sheaf.AlgebraicGeometry.ReducedNormalization: `Scheme.reducedNormalizationComponent`.
- Sheaf.AlgebraicGeometry.MarkedIdealOrder: `HilbertSamuel.stalkIdeal`.
- WeilConjectures.Algebra.Homology.ModuleStalkFunctor: `RingedSpace.moduleStalkFunctor`.
- WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations:
  `Scheme.Modules.scalarObj`, `scalarMap`.
- WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison:
  `Scheme.Modules.tensorPullbackTopSection`, `scalarGlobalSectionsEquiv`.

Already-stated proof dependencies are imported privately: ProjectiveImpliesProper,
NodalSubcurveBoundary, upstream ModuleStalkExact, Mathlib Flat.Basic,
Flat.FaithfullyFlat.Algebra, AdicCompletion.AsTensorProduct and AdicCompletion.LocalRing.
The last three give the recorded mathlib_match completion and faithful-flat interfaces.
The three proof-only DAG nodes nodal-completed-normalization-model,
closed-component-stalk-calculus and split-node-component-normalization have no Lean record
or Mathlib match in the live read clone. Their eventual module imports are left to the
maintainer when those nodes are stated (stages/2-statements.md rule 7); they are not needed
to type the present statement, and this delivery does not create private substitutes.

Edge cases checked before drafting:

- T empty: J=R. For s=(1,1), the pair (1,0) is not in R; the node is constrained, as
  required. Our witness requires r mod P = 1 and r mod Q = 0 IN R, so detects this.
- J=(u+v), s=(u,v): the one-branch pair is not in J although s vanishes at the node;
  the condition requires a=b. It does not merely test whether s(x)=0.
- J=(u,v), s=(u,v), and J=(u,v)^2, s=(u²,v²): the one-branch pairs belong to J and
  distinct scalars are allowed. Arbitrary nonreduced clusters are retained.
- Disconnected X: each component has its own coefficient and only actual intersections
  impose equations. A smooth irreducible component has W=k*s. A self-node on an integral
  component has no distinct component pair. Characteristic two causes no change to the
  subtraction/inverse argument. Empty X is excluded by the statement itself, not silently.
- Zero s is excluded exactly by hs on the nonempty components; no assumption that s is
  nonzero at nodes is present. The cluster dimension inequality admits empty T.

Searches for existing declarations:

1. msearch.py leanfinder, query "Componentwise scalar multiples of a nonzero section of an
   ideal twist on a nodal curve glue exactly when coefficients agree at constrained nodes":
   eight hits, all Weierstrass affine coordinate-ideal identities; none is this theorem.
2. msearch.py loogle, query `"Scheme", "scalar"`: one scalar-tower instance in
   Modules.Tilde, not the requested statement.
3. msearch.py grep, query `nodal.*ideal|scalar.*gluing`, subdirectory AlgebraicGeometry:
   zero hits.
4. msearch.py leansearch, query "ideal sheaf stalk ideal scheme quasi coherent ideal":
   eight general IdealSheafData and localization hits. This supported using existing
   ideal data; no scalar-gluing theorem was returned.
5. rg of `nodal.*ideal|[Ii]deal.*[Tt]wist|componentwise.*scalar|[Ss]calar.*[Gg]luing`
   in lean/Sheaf and lean/WeilConjectures found the disjoint-ideal-twist modules and
   unrelated scalar constructions, no equivalent nodal coefficient theorem. The exact
   node id and NodalIdealScalarGluing/nodal_ideal_scalar_gluing names have no source hit.
6. Narrow source searches found the existing stalkIdeal, reducedNormalizationComponent,
   scalarObj and tensorPullbackTopSection interfaces, which are imported and reused.
   No new independent notion was needed, so no new definition node is supplied.

Sources read locally: curves.tex lemma-split-node (Tag 0CBW), varieties.tex
lemma-normalization-same-after-completion (Tag 0C3V), algebra.tex
lemma-completion-faithfully-flat (Tag 00MC), and the current latest blueprint
sk-thm-sf-ctf-stability-direct-images.proof.md (3). The scalar-space consequence is the
agent-written argument of the live node, not a claim that Stacks states this global theorem
verbatim. No STATEMENT-DISPUTED flag or mathematical correction is needed.

Validation: scompile.py compiled both the sandbox module and its actual library module
name cleanly, about three seconds each. The first draft's module visibility and stalk-type
elaboration errors were corrected using the recorded public ideal-module import and the
bundled moduleStalkFunctor object; no mathematical hypothesis was changed.

## Second reading by Q03

Separate in-thread rereading of the live node and final Lean source, with no subagents
(the dispatcher prohibits starting other agents). This is a worker self-check; the
maintainer supplies the independent delivery review.

I matched every hypothesis and clause as listed above and checked the two sensitive
points directly: the ideal-membership witness lies in the full completed ideal in R,
and the component inclusions are those of reduced components, not their normalizations.
I checked W's iff against all scalarObj sections, c's graph formula against ordinary
pullback sections, and the exact-image iff against every distinct-component node. I also
checked that presentation transport moves all three ideals and the germ together, and
that arbitrary frames and swapping branches are both quantified. Empty and nonreduced
clusters and disconnected schemes remain available; a self-node never produces a pair
of distinct component indices. Definitions contain no postponed data, there are no
file-local instances or notations, all variables/universes are explicit, and every line
of the Lean source is at most 100 characters. No further statement mismatch found.
