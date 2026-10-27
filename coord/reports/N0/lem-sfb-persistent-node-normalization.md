## Worker report

Stage 2: `Sheaf.AlgebraicGeometry.PersistentNodeNormalization` states
`AlgebraicGeometry.persistent_node_normalization`, with its proof `sorry`.
Its five helper definitions have actual data: the reduced closed nonsmooth complement
in the generic fibre, its composite immersion into X, its scheme-theoretic image,
the image inclusion, and the pullback of the recorded componentwise normalization
along that inclusion. These are the canonical objects named in this node, not new
independent notions. There are no new nodes and no dependency repairs.
The complete ten-step natural-language proof of the live node is in the theorem docstring.

The previous worker's reported stage-1 completion by Q05 is the `reviewed` record of
the split, not a stage-2 Lean binding: both `lean` and `reviewed_lean` were absent.
The incoming sandbox contained only dispatcher brief markers. This delivery supplies
the missing stage-2 statement rather than redelivering the stage-1 split.

### Hypotheses and canonical objects

- DVR R: `(R K : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The residue field is the canonical
  `IsLocalRing.ResidueField R`; it needs no extra parameter because no conclusion
  depends on a separately chosen presentation of k.
- Its fraction field: `[Field K] [Algebra R K] [IsFractionRing R K]`.
  The notation parameter `η` is required by `hη` to be precisely
  `Spec.map (CommRingCat.ofHom (algebraMap R K))`. Quantifying over that pinned
  parameter is equivalent to substituting the displayed canonical term everywhere.
- S is literally `Spec (.of R)`; X and its structural map are `(X : Scheme.{u})`
  and `(f : X ⟶ Spec (.of R))`.
- Projective: `[IsHProjective f]`, the recorded finite-projective-space convention.
  Flat: `[Flat f]`. Finite presentation: `[LocallyOfFinitePresentation f]`
  together with H-projectivity, which implies properness, quasi-compactness and
  separatedness, hence quasi-separatedness. Thus this is full finite presentation,
  not the unrestricted locally finitely presented case.
- Every geometric fibre: `hgeom` quantifies over every algebraically closed field
  `Ω : Type u` and every geometric point `g : Spec (.of Ω) ⟶ Spec (.of R)`.
  Each fibre is the actual scheme `pullback (C := Scheme.{u}) f g`.
- Nonempty fibres: `Nonempty` of that scheme. Reduced fibres: `IsReduced`.
  Pure dimension one: `Scheme.IsPureDimension ... 1`, the existing declaration.
- Nodal completed local rings: for every nonsmooth point of that geometric fibre,
  `Nonempty (AdicCompletion (IsLocalRing.maximalIdeal ...) ... ≃+*
  (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}))`.
  This tests the actual geometric stalk, not the total-space stalk. In a reduced
  finite-type curve over an algebraically closed field, the generic points are
  smooth and every nonsmooth point is closed. Hence testing all nonsmooth points
  is equivalent to the closed-point wording in the node. No connectedness or
  geometric irreducibility condition appears.
- N_K is `persistentGenericSingular f η`, the reduced induced scheme on the
  complement of `(pullback.snd f η).smoothLocus`, using the existing vanishing ideal.
  `persistentGenericSingularMap f η` composes its closed immersion with the generic
  fibre's first projection. `persistentNodes f η` and `persistentNodesι f η` are
  its Mathlib scheme-theoretic image and image inclusion. Thus the closure has its
  scheme-theoretic structure, not just the reduced topological closure.
- C and ν are exactly `X.reducedNormalization` and `X.fromReducedNormalization`
  from `def-weil-pbc-reduced-normalization`. This is the componentwise
  function-field normalization; its affine integral-closure description follows
  from that recorded definition and the proof's affine calculation. No alternate
  normalization object is chosen.
- B is `persistentBranches f η`, literally the scheme pullback of ν and N ↪ X.
  The two displayed maps are the actual `pullback.fst` and `pullback.snd`.

### Conclusions, clause by clause

- X is reduced: the first conclusion `IsReduced X`.
- N finite étale over S: `IsFinite (persistentNodesι f η ≫ f)` and `Etale` of
  the same structural morphism. Its inclusion is closed by construction as an image.
- Finite normalization: `IsFinite X.fromReducedNormalization`.
- C projective and flat over S: `IsHProjective (X.fromReducedNormalization ≫ f)`
  and `Flat` of that composite. The existential `hfp` supplies its local finite
  presentation; H-projectivity again supplies the remaining global conditions.
- Nodal geometric fibres of C: the same four-part geometric-fibre condition as
  `hgeom`, including nonemptiness, reducedness, pure dimension one, and the precise
  completed local ring. Its generic fibre is smooth by
  `Smooth (pullback.snd (X.fromReducedNormalization ≫ f) η)`.
- Isomorphism off N: for every open U disjoint from `Set.range (persistentNodesι f η)`,
  `IsIso (pullback.snd X.fromReducedNormalization U.ι)`. Because N is closed,
  this includes U = X \ N and is equivalent to the node's formulation.
- B ↪ C closed: `IsClosedImmersion (pullback.fst ... ...)`.
- B lies in the relative smooth locus of C: the universal assertion over
  `z : persistentBranches f η` that its first projection belongs to
  `@Scheme.Hom.smoothLocus ... hfp`. The same hfp controls the entire locus.
- B finite étale over S: `IsFinite` and `Etale` of its composite B → C → X → S.
- B → N finite étale: `IsFinite` and `Etale` of `pullback.snd`.
- Constant degree two: every geometric fibre of that same map has `Nat.card ... = 2`.
  Since the map is already finite étale, the point count is its locally constant
  module rank, including the usual vacuous rank convention over an empty N.
- Pushout: `IsPushout (pullback.fst ...) (pullback.snd ...)
  X.fromReducedNormalization (persistentNodesι f η)`, in the actual category of schemes.
- Restriction to every open V ⊆ X: quantification over every open immersion `j : V ⟶ X`
  and the three actual inverse-image pullback schemes. The two top arrows `a` and `c`
  satisfy BOTH projection equations for the respective pullbacks. Those equations
  uniquely characterize the canonical induced arrows, so these are not unconstrained
  maps or extra geometric data. The conclusion is `IsPushout a c ... ...`.
  This includes the identity immersion and the empty open.
- Integral-closure coordinate rings of N and B: two assertions, each saying the
  restriction on global sections to the generic fibre is injective, and its image
  consists exactly of the elements integral over R. Integrality is
  `RingHom.IsIntegralElem` for the composite R → Γ(Spec R) → Γ(T_K), with the
  structural map explicitly given by `pullback.snd ... η ≫ η`.
  This is integral closure inside the actual generic finite algebra, rather than
  an unspecified ring isomorphism. Finite schemes over the affine S are affine.
  Consequently these equalities determine each scheme over S from its generic algebra.
- Their map is determined by its generic map: the added universal assertion over
  `ψ : persistentBranches f η ⟶ persistentNodes f η` requires it to be over S
  and equal to the actual branch map after restriction to the generic source;
  its conclusion is equality with `pullback.snd`. This states the claimed uniqueness
  directly, in addition to the integral-closure descriptions giving reconstruction.
- Generic square: the displayed isomorphism from C_K to `(pullback f η).reducedNormalization`
  commutes with both projections to X and Spec K. The displayed isomorphism from
  N ×_S Spec K to `persistentGenericSingular f η` also commutes with both projections.
  B is the pullback by definition, so its generic fibre is the corresponding inverse image.
- Generic conductor: on every affine open U of X_K, membership in the ideal of
  its reduced singular closed subscheme is equivalent to multiplying every section
  of the normalization above U back into the image of Γ(X_K,U). This is the
  conductor ideal criterion. Together with the generic identifications and the
  pushout clause, it states the normalization and conductor square.
- Regular semilocal one-dimensional N and B when nonempty: two assertions of
  `IsRegularScheme T`, `(closedPoints T).Finite`, and
  `Nonempty T → topologicalKrullDim T = 1`. Semilocality means finitely many closed
  points for these affine schemes.
- At each closed point x of N and B: an explicitly bound `IsDomain` structure and
  `IsDiscreteValuationRing` for the actual stalk, and, for each irreducible π of R,
  equality of the stalk's maximal ideal with the span of the image of π under
  R → Γ(T) → T_x. By the recorded DVR equivalence, irreducible elements of R
  are precisely its uniformizers. Thus the uniformizer assertion is structural.
- Empty case: nothing assumes N or B nonempty. Dimension-one assertions are
  guarded by `Nonempty`; degree two is tested only at existing geometric points.

### Dependency declarations and imports

All original statement dependencies retain their records and are used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` and the uniformizer
  convention in `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective`,
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` and `Scheme.Hom.smoothLocus`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-geometric-fibre`: `CategoryTheory.Limits.pullback`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-pbc-adic-completion`: `AdicCompletion`,
  `Mathlib.RingTheory.AdicCompletion.Basic` and its `Algebra` module for rings.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-pbc-category-colimit`: `IsPushout`, the pushout instance of the
  recorded `IsColimit` universal property in `CategoryTheory.Limits`.
- `def-nagata-scheme-theoretic-image`: `Scheme.Hom.image` and `imageι`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-weil-pbc-reduced-normalization`: `Scheme.reducedNormalization` and
  `Scheme.fromReducedNormalization`, `Sheaf.AlgebraicGeometry.ReducedNormalization`.

Two existing landed definition dependencies are added, without copying or modifying them:
`def-weil-pure-dimension` (`Scheme.IsPureDimension`,
`Sheaf.AlgebraicGeometry.PureDimension`) and `def-weil-regular-scheme`
(`IsRegularScheme`, `Sheaf.AlgebraicGeometry.IsRegularScheme`).
Their declarations and docstrings were read in full.

All currently importable proof modules with recorded `lean.module` are included as
plain imports. The node's `lem-trf-nodal-family-etale-source-locality` module is the
exception: `scompile.py` reports
`cannot import non-module Sheaf.AlgebraicGeometry.NodalFamilyEtaleSourceLocality from module`.
It is a legacy non-module file, so that proof-only import is omitted; no declaration
from it is used in the statement. Its DAG proof dependency remains, and the complete
proof plan still names it. This is a source module-format repair for the maintainer,
not a replacement definition in this delivery. Unstated proof nodes (the DVR local
form, smooth normalization pullback, affine closed pinching) have no module to import.

### Edge cases checked before stating

1. Smooth projective family: N_K, N and B are empty, C = X. Both integral-closure
   criteria describe the zero ring; empty conductor and pushout are correct.
2. Persistent split chart uv = 0: N = Spec R and B = Spec(R × R), degree two,
   normalization the two branches; conductor (u,v) gives the stated product criterion.
3. Smoothing chart uv = π and uv = π^m for m > 1: total ring is normal even though
   the special fibre is nodal; N = B = empty and the normalization is the identity.
   The theorem does not assert the normalized total space or its special fibre is smooth.
4. Smooth chart uv = 1: same empty persistent-node conclusion.
5. Nonsplit node: no two individually rational branches or split N/B assumption;
   the degree-two cover is finite étale and is tested geometrically.
6. Disconnected fibres and disjoint normalized components are allowed; the
   connected-fibre predicate `HasNodalGeometricFibres` is deliberately not used.
7. No completeness, excellence, Japanese property, characteristic restriction,
   or assumption that all special nodes persist is imposed on R.
8. V = X and V = empty are allowed in the open-restriction statement. Empty N
   has no geometric points at which a nonvacuous degree assertion could be imposed.
9. Dimension-one assertions are only made when the respective finite étale
   scheme is nonempty; the source curve's geometric fibres remain nonempty as required.

### Searches

- msearch leanfinder: "Normalization of nodal curve family over discrete valuation
  ring finite etale persistent nodes conductor pushout". Eight hits, including
  Weierstrass minimality/good reduction and relative `Scheme.Hom.normalization`;
  none states this persistent-node assertion.
- msearch loogle: "AlgebraicGeometry.Scheme.fromReducedNormalization,
  AlgebraicGeometry.Scheme.Hom.smoothLocus". Zero hits; unknown identifier
  `AlgebraicGeometry.Scheme.fromReducedNormalization` in the remote Mathlib index.
  The project source does supply that definition and it is reused.
- msearch grep in Mathlib AlgebraicGeometry:
  "persistent.?[Nn]ode|normalization.*conductor|conductor.*normalization".
  Zero hits.
- msearch leansearch: "The normalization of a nodal curve over a discrete valuation
  ring separates its persistent nodes and is a finite morphism". Eight relative
  normalization API hits (`normalizationDesc`, `normalization`, `toNormalization`,
  `fromNormalization`, etc.), none giving this theorem.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for persistent-node names
  and the item id: no existing declaration of this item. Broader nodal, conductor,
  singular-locus and normalization searches found the existing reduced normalization,
  connected nodal-geometric-fibre predicate, pure dimension, Fitting singular
  subscheme, regular-scheme predicate, and the conductor helper restricted by its
  surrounding theorem to schemes over Q. The general conductor condition is written
  by multiplication into the image on affine sections, so no Q-hypothesis is introduced.

No `STATEMENT-DISPUTED` issue or statement correction is needed.

### Validation

The prescribed `scompile.py` has compiled the module in both sandbox and library
module modes against the live published build. Auto-bound implicits are disabled,
all universes are explicit, and every definition has real data. The only postponed
proof is `AlgebraicGeometry.persistent_node_normalization`, matching this DAG node.
Delivery preflight and final per-file compile are run through `deliver2.py`.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
