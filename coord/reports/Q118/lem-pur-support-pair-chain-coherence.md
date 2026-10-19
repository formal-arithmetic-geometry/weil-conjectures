## Worker report

Repaired the returned packet at immutable head `95f7ea082304`. The saved
packet's initial dry run passed as `2a098a63ce`; that was a syntactic check
of the old statement, and did not resolve H3-1, H3-2, or H3-3. The delivery
now changes the Lean interface to match the unchanged mathematical node.
The theorem is `CategoryTheory.supportPairChainCoherence`, in
`Sheaf.Paper.SupportPairChainCoherence`. Its only postponed theorem is that
named theorem, with `sorry`. All helper data and predicates are explicit;
no new independent notion, dependency repair, or statement correction is needed.

Hypothesis and clause correspondence:

- The two small sites are `C`, `D`, their category instances, and the
  Grothendieck topologies `Jc`, `Jd`. Abelian sheaves are Mathlib's
  `Sheaf Jc AddCommGrpCat` and `Sheaf Jd AddCommGrpCat`, with `HasSheafify`
  instances providing the abelian-category infrastructure. Site object and
  morphism universes are independently named.
- The precomposition condition is `[u.IsContinuous Jc Jd]`. The right
  adjoint is exactly `u.sheafPushforwardContinuous AddCommGrpCat Jc Jd`:
  its sheaf, restriction maps, and action on sheaf morphisms are the
  precomposition functor, not merely section objects of equal type.
  The adjunction is `adj : L ⊣ u.sheafPushforwardContinuous ...`;
  `[L.Additive]`, `[PreservesFiniteLimits L]`, and
  `[PreservesFiniteColimits L]` render additivity and preservation of
  kernels and cokernels between abelian categories. There is no arbitrary
  `R`, object-only equation `hR`, or `eqToHom` transport.
- `SupportPair` has objects `V,T`, arrow `m : V ⟶ T`, and `Mono m`.
  `P,P'` are the two monomorphic pairs. `t,s` are the two specified site
  arrows. `square : s ≫ u.map P.m = P'.m ≫ t` is exactly the required
  commuting square in Lean's composition order.
- `supportKernel J P I` is the kernel in the cochain-complex category
  of the natural restriction chain map. Kernels there are degreewise
  kernels. `supportDiagram J P I` is the short complex whose arrows
  are that kernel's inclusion and the restriction chain map. Thus its
  three objects are the kernel complex, `I(T)`, and `I(V)`; this use of
  `ShortComplex` is only for the diagram, never for its homotopies.
- All complexes are `CochainComplex ... ℤ`. `BoundedBelow` means
  `∃ n : ℤ, ∀ i < n, IsZero (I.X i)`. Each resolution term's injectivity
  is `∀ n : ℤ, Injective (I.X n)`. The derived localization is
  `standardDerivedQ`, defined as Mathlib `DerivedCategory.Q`, with
  the two `HasDerivedCategory` instances.
- Part (1): `degreewiseAdjoint` is `adj.homEquiv` on each `h.f n`.
  `supportPairMapCondition` specifies both section maps as evaluation
  of this adjoint followed by restriction along `t` and `s`.
  `∃! φ : supportDiagram ... ⟶ supportDiagram ...` states existence
  and uniqueness of the diagram map with those components. The
  `ShortComplex.Hom` structure supplies both commuting squares;
  its first component is precisely the unique compatible kernel map.
- Part (2): the supplied `z : _root_.Homotopy h h'` is a degree -1
  sheaf homotopy, with `z.hom i j` zero unless `j + 1 = i`.
  The conclusion supplies three `_root_.Homotopy` witnesses `H₁,H₂,H₃`
  on `φ.τ₁`, `φ.τ₂`, `φ.τ₃`. For every `i,j`, their first two equations
  say that the kernel inclusion and restriction commute with the
  degree -1 maps. The last two equations specify `H₂.hom i j` and
  `H₃.hom i j` as the evaluated adjoints of `z.hom i j`, restricted
  along `t,s`. The kernel equation uniquely determines the restricted
  kernel homotopy. This states the prescribed compatible cochain
  homotopies, including kernel homotopy invariance.
- The next clause represents every `a : Q(LI) ⟶ QK` by a chain map
  `h` with `Q.map h = a`, under exactly the bounded-below injective
  hypotheses in the node. The following clause states uniqueness up
  to `Nonempty (_root_.Homotopy h₁ h₂)` when their localized maps agree.
  It also explicitly asserts `supportCohomologyEqual φ ψ` for the
  diagram maps of *any* two such representatives. That predicate is
  the three separate equalities of `HomologicalComplex.homologyFunctor`
  maps in every degree, so dependence of all three cohomology maps
  only on `a` is part of the conclusion.
- Step 5 / replacement invariance: the final clause quantifies over
  other bounded-below injective complexes `I',K'` and chain maps
  `g : I' ⟶ I`, `g' : K ⟶ K'` whose derived images are isomorphisms.
  Such maps represent all identifications of these derived objects:
  the K-injective comparison supplies a representative of every
  derived isomorphism, and its inverse up to homotopy. The equation
  for `Q.map h'` is transport of `Q.map h` along `Q(Lg)` and `Q(g')`.
  For arbitrary diagram maps `φ,ψ` belonging to `h,h'`, the conclusion
  supplies ordinary comparison diagram maps `α,β`.
  `supportOrdinaryMapCondition` fixes their section components to
  evaluation of `g,g'`; the kernel components are then uniquely fixed.
  `supportCohomologyIsIso α` and `supportCohomologyIsIso β` explicitly
  assert that all six component cohomology maps are isomorphisms.
  `supportCohomologyEqual (α ≫ φ ≫ β) ψ` is the equality after these
  canonical identifications, in all three components and all degrees.
  Homotopy invariance, also applied to the identity adjunction, makes
  these identifications independent of the chosen chain lifts of the
  derived isomorphisms. No arbitrary cohomology isomorphisms are used.

Dependencies and exact declarations read and used:

- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings` (the imported site
  convention); Mathlib `Sheaf`, `sheafSections`,
  `Functor.IsContinuous` and `Functor.sheafPushforwardContinuous`
  from `Mathlib.CategoryTheory.Sites.Continuous` for the actual
  sheaf precomposition interface.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; cochain complexes and
  their `HomologicalComplex.homologyFunctor` are the recorded
  complex/cohomology infrastructure.
- `def-sp-injective-resolutions`: Mathlib `CategoryTheory.Injective`
  from `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
  The full `InjectiveResolution` structure was read; the node here
  uses integer-indexed bounded-below injective complexes directly,
  rather than an object resolution based in degree zero.
- `def-sp-left-exact-additive`: Mathlib `Functor.Additive`,
  `PreservesFiniteLimits`, `PreservesFiniteColimits`, supplied by the
  existing `Mathlib.CategoryTheory.Abelian.RightDerived` import.
- Proof dependencies, imported without `public`:
  `CochainComplex.isKInjective_of_injective` from
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` and
  `CochainComplex.IsKInjective.Qh_map_bijective` (also `quasiIso_iff`)
  from `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
  These are the nodes' exact Mathlib matches.

Edge cases checked: arbitrary integer lower bounds, degree zero and negative
cohomology, zero complexes, empty sites, identity site functor, identity
monomorphisms and identity comparison arrows. No nonempty, positive-degree,
or degree-zero resolution assumption is imposed. For `m = id`, the kernel
complex is zero but the two section homotopies remain ordinary degree -1
homotopies. Homotopy components for nonadjacent degrees are zero by the
Mathlib `Homotopy.zero` field, so the all-`i,j` formulas add no extra condition.

The maintainer's two-object-site counterexample has restriction multiplication
by 2. Our `H₂` is a degree -1 homotopy from the T section complex to itself,
and `H₃` one from the V section complex to itself; neither is a map from
the V section complex into the T section complex. Hence no factorization
`id_Z = 2 ∘ h₂` is requested. The sign-twisted precomposition example is
excluded because the right adjoint is definitionally canonical precomposition,
including its restriction maps and functorial action. Replacement maps are
only required to be derived isomorphisms, not termwise isomorphisms, so all
bounded-below injective representatives remain covered.

Searches made:

- `msearch.py ... leanfinder "Adjoint chain maps between injective sheaf resolutions induce homotopy independent functorial maps on kernels of restriction to a subobject"`: eight injective-resolution homotopy hits, none stated pair-kernel coherence.
- `msearch.py ... loogle "CategoryTheory.Limits.kernel.map, CategoryTheory.InjectiveResolution.descHomotopy"`: zero hits for the combined statement.
- `msearch.py ... grep "supportPair|supportedSections|kernel.*[Rr]estriction|[Rr]estriction.*kernel" CategoryTheory`: zero hits.
- `rg` over `WeilConjectures/` and shared `lean/Sheaf/`: no declaration with the node's full statement. The existing `SupportLongExact` support-sequence declarations concern a different, specialized D+ statement and do not match this generic adjunction theorem.


Repair searches: `rg` for `SupportPair`, `supportOrdinaryMapCondition`,
`supportCohomologyEqual`, `supportCohomologyIsIso`, and
`supportPairChainCoherence` in the source project's `WeilConjectures/`,
shared `lean/Sheaf/`, and pinned Mathlib found no collisions. Read the exact
Mathlib `Homotopy` fields and the implementation of
`sheafPushforwardContinuous`: the latter really is precomposition on both
objects and morphisms. Existing searches above were retained rather than
restarting the original investigation.

## Returned points repaired

- H3-1: replaced `ShortComplex.Homotopy` by three `_root_.Homotopy`
  witnesses with explicit inclusion/restriction compatibility and the
  required evaluated-adjoint formulas.
- H3-2: canonical `sheafPushforwardContinuous`, continuity instance,
  no arbitrary `R`, `hR`, or equality transport.
- H3-3: explicit equality of all three cohomology maps for equal derived
  morphisms, and explicit isomorphisms and transport equality for
  other bounded-below injective representatives.
- H8: added source places and blueprint tags to every helper's docstring;
  removed unused `sectionComplex`; listed all helpers in `lean.declarations`.

The node's existing statement already contains all these intended clauses,
so only `lean` changes. No `STATEMENT-DISPUTED` flag remains.

## Second reading by Q118

Self-check of the repaired node and file (the dispatcher explicitly forbids
starting another agent; the maintainer performs the independent review).
Checked every hypothesis and clause using the correspondence above, with
particular attention to the types and degrees of the three homotopies,
the actual functorial right adjoint, and the final representative-transport
identity. The first compile exposed only two line-width warnings; those
lines were split. The original mathematical node is unchanged. All
helpers have concrete data or explicit Prop definitions, and the main
theorem is the only `sorry`. The `lean.statement` is extracted verbatim
from the final theorem signature and every declaration is recorded.
