## Worker report

The delivery states `AlgebraicGeometry.exists_embedded_surface_curve_resolution` in
`Sheaf.AlgebraicGeometry.EmbeddedSurfaceCurveResolution`, with `sorry` as its only proof.
It preserves the live Q100 eight-step split, statement, proof dependencies, provenance,
and review. A reviewed stage-1 split does not supply this missing stage-2 declaration.
Only `lean` and three additions to `stmt_deps` change. There are no new definitions,
new nodes, dependency repairs, statement corrections, or disputed assertions.

### Hypotheses and clauses

- The ambient scheme is the explicit binder `X : Scheme.{u}`. `[IsIntegral X]` gives
  nonemptiness and reduced irreducibility, using Mathlib's recorded definition.
- `[IsNoetherian X]` is global Noetherianity, including quasi-compactness;
  `hRegular : IsRegularScheme X` uses the recorded locally-Noetherian, stalkwise-regular
  definition. Neither separation nor a field base is imposed.
- `hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U)` is excellence on every affine
  coordinate ring, using the dependency's actual `IsExcellent`, with its G-ring, J-2,
  and universal-catenarity conditions. This is the standard excellent-scheme condition.
- `hDim : topologicalKrullDim X = 2` is scheme dimension two. The topological dimension
  counts chains of irreducible closed subsets, and agrees on affine opens with the
  recorded `ringKrullDim` prime-chain convention. No equicodimensionality is assumed.
- `hAmple` existentially quantifies an actual `X.Modules` object `L`, its invertibility
  proof `hL`, and the recorded `@Scheme.Modules.IsAmple X L hL` predicate. The sheaf is
  not chosen from a postponed existence theorem.
- `Z : X.IdealSheafData` encodes a closed subscheme by its quasi-coherent ideal;
  `Z.subschemeι` is its canonical closed immersion. `hZ : Z ≠ ⊥` excludes the whole
  subscheme X (zero ideal). It permits the empty subscheme (unit ideal). Any closed
  immersion into X is isomorphic over X to the closed subscheme of its kernel ideal,
  so this presentation neither restricts nor adds closed subschemes. Here proper means
  properly contained, not an extra proper-morphism hypothesis.
- `∃ A : OrdinaryBlowupTower X` is the finite sequence with an initial identification,
  all intermediate schemes, composable transition maps, actual quasi-coherent centre
  ideals, and isomorphisms `A.blowupIso i` to `(A.center i).blowup` whose composites with
  `blowupMap` are exactly the tower arrows. This raw tower has no characteristic,
  rational-base, finite-type-over-a-field, or resolution assumption: those conditions
  occur in other declarations of its module and are not used here. Its `toBase` is the
  actual composite; it is not a freely chosen arrow.
- The blowups are the existing canonical Rees construction: upstream `Gluing.blowup`
  glues `AffineBlowup (I.ideal U)`, and `AffineBlowup` is the Proj of the Rees algebra
  whose degree a is `(I.ideal U)^a`. Thus these are precisely the relative Rees Proj
  blowups named in the statement. The recorded relative Proj module is imported;
  a second construction or a universal-property surrogate is not introduced.
- `∀ i, IsRegularScheme (A.level i)` states regularity of every intermediate scheme,
  including the initial and final schemes.
- For each `i : Fin A.length`, the existential `p : A.level i.castSucc` and
  `IsClosed {p}` specify a closed point; `(A.center i).radical = A.center i` and
  `(A.center i).support = {p}` specify exactly its reduced closed subscheme. The
  membership `p ∈ (Z.comap (A.toBase i.castSucc)).support` puts the centre in the
  current inverse image. Since the centre is radical, set inclusion also implies
  containment as a closed subscheme. No arbitrary ideal supported at a point is allowed.
- `Z.comap (A.toBase (Fin.last A.length))` is the scheme-theoretic total inverse image,
  not the strict transform or merely its support. Its `IsInvertible` predicate is
  exactly effective Cartier: affine-locally a nonzerodivisor generator.
- `IsStrictNormalCrossingsBoundary` is applied to the radical of that same total
  transform. This uses the already landed general regular-scheme SNC definition,
  rather than the different smooth-over-a-field divisor predicate. It expresses a
  reduced Cartier union of finitely many distinct integral regular components whose
  every scheme-theoretic intersection is regular of the expected codimension.
  On this regular surface, the singleton-intersection condition gives codimension one;
  a nonempty triple intersection would force ambient local dimension at least three,
  so at most two components pass through a point. For one component, lift a regular
  parameter of its quotient local ring and adjoin its prime local equation. For two,
  expected codimension two gives a zero-dimensional regular local intersection, hence
  its quotient is the residue field; the two local equations generate the maximal
  ideal. Thus the equations are part of a regular parameter system, using the recorded
  `IsLocalRing.IsRegularSystemOfParameters` convention. Conversely such parameter
  products give exactly these regular intersections. This is precisely the local
  parameter equivalence already explained in step 7 and Stacks 0BIA. Zero-dimensional
  codimension-one components are included, as the live Q100 review requires.
- `IsHProjective (A.toBase (Fin.last A.length))` uses the finite-projective-space
  convention recorded by `def-kun-projective`, not projective-bundle projectivity.
- `∃ F : Closeds X, Set.Finite (F : Set X)` retains a finite closed subset; the
  separate `∀ x ∈ F, IsClosed {x}` ensures each individual point is closed (finiteness
  of a closed subset alone would not imply this). `(F : Set X) ⊆ Z.support` puts it
  in the original Z. `IsIso ((A.toBase ...) ∣_ F.compl)` asserts the composite really
  is an isomorphism over the complement of that finite set.

### Dependency declarations used

Read the recorded nodes and the full defining signatures/docstrings of:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` and its constituent predicates.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  the existing `IdealSheafData` interface supplies `subschemeι`, `comap`, `radical`,
  and `support` for the closed-subscheme presentation.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData.relProj` and `relProjHom`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`.
- `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.

The Ample, Projective, and RelativeProj modules were read using `scompile.py --source`
because those current upstream files are absent from the older local source checkout.

Three already landed nodes are added to `stmt_deps` to cite their exact existing
interfaces: `def-trf-ordinary-resolution-rule` for `OrdinaryBlowupTower` and `toBase`,
`def-trf-strict-normal-crossings-boundary` for `IsStrictNormalCrossingsBoundary`,
and `def-nagata-global-blowup` for `IdealSheafData.blowup` and `blowupMap`. Their
statements and declaration bodies were read. None is restated or modified.

All available recorded proof modules are imported without `public`: StrictTransform,
IsExcellentFiniteTypeLocalization, ProjectiveImpliesProper,
ExcellentNormalizationPreparation, HProjectiveComposition,
RegularLocalUFDBoundaryFactorization, BlowupUniversal, and Blowup.Complement.
The five new surface support lemmas have no recorded declarations yet; they are only
proof prerequisites, so their absence does not require construction of definitions
or an interface repair to state this theorem. The Mathlib leaves for finite irreducible
components, module length, and height-one factorization need no private replacement.

### Sources and edge cases

Read `literature/stacks-project/resolve.tex`, lemma-embedded-resolution, Tag 0BIC,
including its proof. The live node specializes its source to excellent integral
Noetherian surfaces with an ample invertible module and records the projectivity and
finite exceptional image consequences of that proof. Its eight steps remain intact.
The erroneous isolated phrase more than 3 in the source proof is already corrected
to at least three in the live split; the module follows that reviewed correction.

Checked: Z empty (unit ideal), an already SNC Cartier divisor, a finite non-Cartier
zero-dimensional subscheme, a nonreduced divisor, tangent branches, three transverse
branches, and a codimension-one closed point on a nonequicodimensional semilocal
surface. No component dimension-one hypothesis was introduced. Length zero is permitted
by `OrdinaryBlowupTower.length`, and `Fin 0` makes centre assertions vacuous; the empty
component family in the existing boundary definition represents the empty divisor.
The finite exceptional set may be empty. The initial surface cannot be empty because
it is integral of dimension two; no additional nonempty hypothesis was introduced.
All schemes and centres have the same explicitly bound universe u; no independent
smaller universe makes an excellence or geometric test vacuous. The theorem has no
`let`, local notation, local instance, auto-bound variable, or data containing `sorry`.

### Searches and validation

- `msearch.py leanfinder`: Embedded resolution of a closed subscheme of a regular
  excellent surface by point blowups to a strict normal crossing divisor. Results
  concern residue-field immersions, smoothness and normalization; no matching theorem.
- `msearch.py leansearch`: Embedded resolution by point blowups of a regular excellent
  surface with strict normal crossings total transform. Eight hits: normalization,
  properness, residue fields and preimmersions, none the resolution theorem.
- `msearch.py loogle`: AlgebraicGeometry, Blowup, IsRegular returned no hits (unknown
  identifier AlgebraicGeometry). Repeated with the valid name-fragment query
  `"blowup"`: zero hits.
- `msearch.py grep`: embeddedResolution|[Bb]lowup.*[Ss]urface|StrictNormalCrossings,
  restricted to AlgebraicGeometry: zero Mathlib hits.
- `rg` of upstream WeilConjectures and project lean/Sheaf for the exact node id and
  embedded.surface/embeddedSurface/embedded_surface: no existing theorem. Searches for
  blowup, SNC and tower notions found and led to reuse of OrdinaryResolutionRule and
  StrictNormalCrossingsBoundary. ExcellentSurfaceDesingularization resolves the ambient
  surface and does not assert embedded SNC resolution or a tower with all stages regular.
  Normalized/log/fan towers and rational embedded histories have different objects.
- DAG search found the already reviewed split and the distinct support lemmas, not a
  duplicate statement or an existing binding for this item. The previous worker's
  stage-1 synchronization observation does not eliminate the stage-2 task.
- `scompile.py` checked the delivered module in sandbox and library modes: 2.5 seconds
  and 2.1 seconds, exit zero, with no non-sorry warnings. The required deliver2.py
  dry run passed server preflight and compilation (commit 37eaca88f2); the corrected
  report is checked again before the final push.

## Second reading by Q42

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
