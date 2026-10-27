## Worker report

The module Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentAbelian states
AlgebraicGeometry.AlgebraicSpace.coherent_kernel_cokernel_zero_finite_sum_extension.
Its only theorem has proof `sorry`; it introduces no definition or axiom. The accepted
stage-1 split is preserved. Q21's reviewed stamp is a stage-1 review; the current node
has no lean record or reviewed_lean record, and coord/queue.tsv queues it at stage 2.
There is no repair note for this item. The prior worker's unchanged stage-1 refusal
therefore does not preclude this stage-2 statement delivery (brief-stage2 section 0).

Hypothesis and clause correspondence:

- An arbitrary scheme S is `{S : Scheme.{u}}`; an algebraic space over S is
  `(X : AlgebraicSpace S)`, using the recorded algebraic-space definition.
- Locally Noetherian on every etale scheme chart is exactly
  `hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)`.
  The base S is not required to be locally Noetherian; there is no quasi-compactness,
  separatedness or finiteness assumption on X or its atlas.
- All sheaves and arrows are in `X.Modules`, the existing small-etale structure-sheaf
  module category, rather than QCoh, sections, a scheme's Zariski modules, or arbitrary
  rings supplied by the user.
- The node defines coherence as site quasi-coherence plus coherent pullback on every
  etale scheme chart. Source 07UB equates this with finite presentation on the site
  (conditions 1, 3 and 4). Thus `F.IsFinitePresentation` is precisely the coherent
  predicate under hln. It entails Mathlib's `F.IsQuasicoherent`; the scheme-chart
  condition is equivalent by 07UB and 01XZ. This is the same existing encoding used
  in the landed AlgebraicSpaceCoherentFilteredUnion.CoherentSubobjects definition,
  not a new coherence definition. We retain the full finite-presentation property,
  rather than finite type alone or a statement about global sections.
- For every morphism `f : F ⟶ G` between coherent F and G, the first conjunct says
  each limiting `KernelFork f` and each colimiting `CokernelCofork f` has finitely
  presented point. These are exactly any choice of kernel and cokernel in ALL module
  sheaves. Universal properties replace chosen-object instance arguments; they do
  not assume kernels in the coherent subcategory. Every possible universal object
  is covered, and the predicate is invariant under isomorphism.
- The zero clause is `SheafOfModules.IsFinitePresentation (⊤_ X.Modules)`.
  Mathlib supplies finite limits without sheafification-size hypotheses, and the
  terminal sheaf of modules has zero module at every object and is also initial.
  Thus this is the zero object, including on the empty space. The first compile
  found that numeral `(0 : X.Modules)` has no instance; the terminal-object spelling
  expresses the same zero module using the existing finite-limit API.
- The finite-sum clause quantifies `I : Type v` with `[Finite I]`, independently of u,
  any family F, the coherence of every F i, and ANY bilimit bicone of F. A bilimit
  bicone is precisely a direct sum together with its biproduct structure. Its point
  is coherent. No chosen global biproduct instance or equality of index and section
  universes is required; arbitrary finite index sets including empty are covered.
- An extension is `c : ShortComplex X.Modules` with `c.ShortExact`. This means the
  composite is zero, the sequence is exact, the first map is mono and the second
  epi. Only c.X₁ and c.X₃ are assumed coherent; the conclusion is coherence of the
  arbitrary middle term c.X₂. No quasi-coherence of the middle term is assumed.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme (and its Hom/category).
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.EtaleSite, etaleForget, etaleTopology, structureSheaf and Modules.
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh, the two slice
  sheafification instance obligations, and the Mathlib predicate
  SheafOfModules.IsQuasicoherent; the recorded specialization is imported publicly.
- Sheaf.AlgebraicGeometry.CoherentFiniteType:
  AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType, whose full body is
  IsQuasicoherent AND IsFiniteType. This is the finite-type notion used in the
  proof's scheme-chart comparison, not by itself a coherent predicate. The upstream
  WeilConjectures.AlgebraicGeometry.Coherent declaration RingedSpace.IsCoherent
  and Cohomology.FiniteFibre.IsFiniteTypeWithFiniteTypeKernels were also read to
  distinguish actual coherence from just finite type on general schemes.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:
  SheafOfModules.IsFinitePresentation, whose witnesses are local presentations with
  both free-index sets finite. Its existing instances imply quasi-coherence and
  finite type. No new definition node is needed for that existing notion.

All recorded and available proof dependency modules are imported privately:
CoherentFiniteTypeLocallyNoetherian, QuasicoherentFiniteTypeAffine,
SchemeZariskiEtaleQuasiCoherentEquivalence, TensorPullbackTilde, and Modules.Tilde.
The QCoh and finite-type dependencies are already public statement imports. The
proof dependency lem-sfb-space-coherent-kernel-cokernel-extension has no Lean record
or Mathlib match and hence no module to import; its proof obligation is referenced
by name in the docstring. It is not needed to TYPE this item's statement.

Source read: literature/stacks-project/spaces-cohomology.tex, lines 1877--1925,
Tags 07UB and 07UC. The proof docstring records all three node proof steps: compare
coherence predicates on charts, apply the existing DAG closure result, and use
split extensions and finite induction. No source-based statement correction is
needed and no statement is disputed.

Edge cases checked mathematically: the empty algebraic space and the zero module;
zero and identity morphisms of coherent modules; kernels and cokernels up to an
arbitrary isomorphism; empty, singleton and two-term finite sums; extensions with a
zero end; nonsplit extensions; affine X = Spec k and Spec(k[epsilon]/epsilon^2).
Finite presentation is invariant under isomorphism, including the terminal/zero
choice. Without local Noetherianity the finite-presentation closure statement need
not hold; hln is retained. There is no exactness claim for global sections.

Searches for an existing statement, performed with the prescribed msearch.py:

- leanfinder: "Kernels cokernels finite direct sums and extensions of coherent modules
  on a locally Noetherian algebraic space are coherent"; eight hits, including
  Scheme.Modules.instAbelian and SheafOfModules.IsFinitePresentation. None states
  the requested coherent closure theorem on algebraic spaces.
- loogle: `"IsCoherent", "kernel"`; zero hits.
- grep: `coherent.*abelian|abelian.*coherent|coherent.*cokernel|AlgebraicSpace`;
  one hit, the IsQuasicoherent docstring, not this theorem.
- rg in lean/WeilConjectures: coherence closure hits concern Zariski ringed spaces
  and schemes, especially CoherentKernelCokernelLocallyNoetherian and
  CoherentKernelCokernelSum. The item id itself has no hit there.
- rg in lean/Sheaf: AlgebraicSpaceCoherentFilteredUnion already uses the exact
  finite-presentation encoding of coherent subobjects, but has no closure theorem;
  the algebraic-space framework and QCoh specialization exist and are reused.
- The proposed theorem name was searched in both project roots, with no collision.

## Second reading by Q28

This is a separate self-reading of the node, source, dependency signatures and final
file in the same worker session; no second agent was started, as the dispatcher
explicitly prohibits starting agents. The maintainer's independent review remains
required. I compared every clause again: S is arbitrary; X is an actual algebraic
space over S; hln quantifies every chart; all arrows and universal constructions are
in the ambient module-sheaf category. Both coherent endpoints are required for each
map, and the conclusion covers both kernel and cokernel. Zero and finite sums are
separate conjuncts and the finite type I may be empty. For extensions, the middle
term is unrestricted and only the ends are coherent.

I re-read 07UB: finite presentation is condition (3), and coherent chart pullback is
condition (4), so the use of the existing predicate is equivalent on exactly these
locally Noetherian spaces. It does not conflate finite type and coherence without
hln. I checked that the source's finite presentations use finite generators AND
finite relations, matching the Mathlib declaration. I re-read ShortComplex.ShortExact
and Bicone.IsBilimit to verify exactness and direct-sum semantics. The universal
kernel/cokernel formulation does not change the arrow or add an exactness hypothesis;
it covers every representative of the universal object. The terminal sheaf really
is the zero sheaf of modules. The only change after the first reading was replacing
the unavailable numeral-zero object notation by that existing terminal object.
There are no new nodes, dependency repairs, statement corrections, unbound variables
or data containing sorry. The only postponed declaration is the named theorem of
this item.
