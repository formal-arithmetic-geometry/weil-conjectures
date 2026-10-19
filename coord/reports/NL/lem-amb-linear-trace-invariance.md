## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance` states
`AlgebraicGeometry.Etale.affineSpaceLinearTraceInvariance`. Its only postponed theorem
is that item itself. All helper definitions contain real constructions; no other DAG
statement is stated, no dependency is changed, and no new node is added.

The source read is the complete detailed blueprint lemma
`sec-smooth-purity/sk-prop-an/lem-amb-linear-trace-invariance.md`, both proof paragraphs,
and the node's seven expanded proof steps. The main theorem's docstring carries those
seven steps, including the GL family, actual Cartesian action, trace base change,
degree-zero full faithfulness, locally constant scalar, connected residue-field fibres,
and final pullback along the given matrix.

Hypothesis and clause correspondence:

- `N : ℕ`, `hN : 0 < N` express N ≥ 1. `A : Type (u + 1)`, `[CommRing A]`,
  `[Finite A]`, `hA : (N : A) = 0` express precisely the finite commutative coefficient
  ring and annihilation assumption. No field or nonzero-ring assumption is imposed.
- `S : Scheme.{u}`, `[IsNoetherian S]` is the recorded scheme and Noetherian convention:
  quasi-compact and locally Noetherian, equivalently a finite affine Noetherian cover.
  `hS : IsUnit (N : Γ(S, ⊤))` expresses invertibility of N on S.
- `DerivedCategoryModule A T` throughout is the dependency's ordinary unbounded derived
  category of module-valued sheaves on the small etale site, with the established
  coefficient universe u+1. No pro-etale category or new derived category is introduced.
- `t : OrdinaryFiniteTwistTransport A N hA` is normalized by its roots inclusion and
  pure-generator equations, not an arbitrary orientation. `D` is the existing family
  of `OrdinaryFiniteP1Datum` records with the Kummer-normalized decomposition and actual
  counit normalization. These are the representation parameters of the specified trace
  of `lem-amb-affine-space-top-trace`; the theorem asserts invariance for these normalized
  data, rather than introducing an independently chosen trace or adjunction.
- `d : ℕ` includes zero. The projection is `affineTraceProjection S d` on the dependency's
  `affineTraceTower S d`. `affineTraceAffineSpaceIso S d` is the recorded canonical
  polynomial-coordinate identification with `AffineSpace (ULift (Fin d)) S`.
- `affineTraceCounit A N hA t D S hS d` is exactly the dependency's actual coordinate-tower
  counit. Neither its definition nor its normalization is copied or changed.
- `g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)` is GL_d of the global-sections ring.
  `affineTraceLinearMap` is the explicit map v ↦ gv: its ith coordinate is
  `∑ j, p.appTop.hom (g i j) * affineTraceCoordinate S d j`. It uses
  `AffineSpace.homOfVector` and the canonical inverse tower coordinate isomorphism.
- The existential `sq : IsPullback (affineTraceLinearMap S d g) p p (𝟙 S)` supplies the
  certificate for precisely the square in the node. This is in the conclusion and adds
  no hypothesis on g. With bottom map the identity, being Cartesian also certifies that
  this top map is an isomorphism. There is no arbitrary top map or arbitrary action.
- `affineLinearCoefficientDescent` identifies the existing coefficient object
  `(affineTraceRight ... S d).obj (ordinaryFiniteUnit A S)` with p* of the ordered tensor
  of d copies of `ordinaryFiniteLine A N hA S` shifted by 2. This is A(d)[2d]: degree zero
  is the constant unit, each coordinate contributes the same finite Tate line and even
  shift. It uses the existing roots-of-unity coefficient line, not a second Tate sheaf.
  Its line step uses `ordinaryFiniteTensorPullback`, inverse-image composition, and
  `ordinaryFiniteShiftedLinePullback` from the normalized transport t. Its induction
  uses exactly those maps again. All data are explicit compositions of isomorphisms.
- `affineLinearCoefficientPullback` is the canonical theta_a on this coefficient model.
  It pulls the preceding descent along a, uses a ≫ p = p, and undoes that same descent.
  Compatibility of the normalized Tate transport with composition identifies this with
  the usual Tate-tensor-shift comparison. No scalar, arbitrary isomorphism, or existence
  choice is inserted. This construction avoids choosing the dependency theorem's bare
  `Nonempty` isomorphism to a flattened Tate-power expression.
- `affineLinearCompactComparison` extracts the already stated boundedness clause
  of `exists_affineSpaceTopTrace` by `Exists.elim`, selecting no mathematical object,
  and uses this proof to apply the dependency's literal
  `affineTraceCompactSupportComparison`, together with its existing
  `affineTracePlusCompatibility` and `rightDerivedLowerShriekPlusCompatibility`.
- `affineLinearTraceAction` first uses that comparison to Rp_d!, then inserts the inverse
  identity-pullback comparison on S, applies `rightDerivedLowerShriekBaseChangeMap A sq`,
  applies Rp_d! to the canonical theta_a, and returns through the same comparison. It is
  therefore precisely the specified compact-support exchange action, expressed on the
  source of the actual counit. All inputs are bounded below as just noted; the ambient
  unbounded exchange is read on that input. This is the ordinary exchange of the recorded
  compact-support theorem, with the canonical compactification-independent comparisons.
- The equation in the conclusion is `affineLinearTraceAction ... sq ≫ affineTraceCounit ...
  = affineTraceCounit ...`. Lean's composition order makes this exactly t_p ∘ rho_g = t_p.
  The final sentence of the node restates this equality, including d = 0.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms, and Spec.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`,
  `AffineSpace.homOfVector`, its projection and coordinate signatures; the node's
  `mathlib_match` is the correct existing declaration despite having no `lean` field.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and its upstream public coefficient import:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: the full recorded theorem
  `AlgebraicGeometry.Scheme.etaleFiniteTwistPullback`, including roots normalization,
  coefficient generator normalization, tensor/identity/composition/shift compatibility.
  The normalized line interface used by the trace is
  `OrdinaryFiniteTwistTransport` and `ordinaryFiniteShiftedLinePullback`, imported through
  `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows` by the trace dependency.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: `affineTraceRight`, `affineTraceLeft`,
  `affineTraceCounit`, `affineTraceCompactSupportComparison`,
  `affineTracePlusCompatibility`, and `exists_affineSpaceTopTrace`; also the concrete
  tower/coordinate maps from its public `AffineTraceTower` import.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, its chosen-compactification
  `rightDerivedLowerShriek` and restriction compatibility. Its body is derived open
  extension by zero followed by total right derived proper direct image.
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`: `compactSupportFiniteTorsion` and
  the recorded canonical exchange/pasting interfaces. The actual action uses its public
  upstream `rightDerivedLowerShriekBaseChangeMap`, already used in the affine-trace module.
  The current `LowerShriekPlusBaseChange` source was read through `scompile.py --source`,
  since that published module is absent from the older local upstream checkout.
- All recorded proof-dependency modules are imported without `public` when they are not
  already statement imports, including degree-zero full faithfulness, finite-type
  Noetherianity, projective compactification, constant sections and local constancy.

Edge cases checked before and after writing:

- d = 0: the tower, projection and adjunction are identities, the coordinate family and
  finite sums have empty index sets, and GL_0 has its usual empty invertible matrix.
  The descent uses the canonical identity inverse-image comparison; no positive-dimension
  assumption occurs anywhere.
- Empty S: no nonempty or connected hypothesis is imposed on the base. The scalar argument
  in the docstring is vacuous on its points and valid on empty fibres as appropriate.
- A the zero ring and N = 1: allowed. All tensor constructions, constant coefficients and
  invertibility assumptions retain their literal meaning; no `Nontrivial A` is required.
- General nonaffine Noetherian S: matrix entries are global functions and coordinates use
  the relative affine-space universal property, not an affine-base assumption.
- Universes: schemes live in u and coefficients in u+1, as in each recorded dependency;
  the finite coordinate index is lifted only where Mathlib's affine space requires it.
- Every variable and universe is explicitly bound; `autoImplicit false` is set. No local
  instance, private definition, file-local notation, or unnamed postponed proof is used.

Searches (no existing statement matched):

- `msearch.py`, LeanFinder: "Every invertible linear coordinate change preserves the affine
  space compact support etale trace". Eight hits about etale loci and smooth presentations;
  none gives trace invariance. Repeated once while inspecting the dependency API, same result.
- `msearch.py`, Loogle: "AlgebraicGeometry.AffineSpace.homOfVector, GeneralLinearGroup".
  Zero hits; Loogle reported unknown identifier `GeneralLinearGroup`. The actual matrix
  declaration was then found and read at `Matrix.GeneralLinearGroup` by source search.
  A further valid Loogle statement search, `"trace", "AffineSpace"`, returned zero hits.
- `msearch.py`, Mathlib grep: `affine.*[Tt]race|[Tt]race.*affine`. Zero hits.
- `rg` in upstream `WeilConjectures` and published `lean/Sheaf` for affine/linear traces and
  the item id: only the already recorded affine-space top-trace/tower modules and unrelated
  trace modules; no linear-invariance theorem. The required upstream item-id search had
  no hit. The upstream name index likewise has no entry for this item.
- `rg` of all proposed full-name stems in Mathlib, upstream, and project `lean/Sheaf`:
  no declaration collision. Read `Matrix.GeneralLinearGroup` and
  `AffineSpace.homOfVector` directly rather than inventing either notion.

No statement correction, dependency fault, or STATEMENT-DISPUTED issue was found.
Validation: the final module compiled cleanly through `scompile.py NL
lem-amb-linear-trace-invariance`, both in the sandbox and as its library module, in
6.7 and 5.8 seconds respectively, with no warnings. During development, an equation-form
recursive descent caused a kernel timeout; expressing its induction step with explicit
line-functor and tensor targets, and using `Nat.rec`, repaired that elaboration issue.
No compilation limit was changed. A redundant proof-valued helper was removed so the
boundedness extraction is directly from the already recorded named theorem.
The prescribed delivery dry run is the final check.

## Second reading by NL

Independent second reading, 2026-10-16. I read the sandbox node and all 274 lines of
its module against the detailed blueprint lemma, both proof paragraphs, the enclosing
`sk-prop-an/_section.md` (especially Steps 5--7), and the node's seven expanded proof
steps. The item's source is the blueprint, not a Stacks lemma with an additional
ambient context. For the coefficient dependency I also read Stacks
`etale-cohomology.tex`, `section-kummer` (Tag 03PK) and `lemma-stalk-pullback` (Tag
03Q1): roots are the kernel of the power map, N is invertible, and inverse image
is exact for every scheme morphism. No smoothness, connectedness, affineness,
nonempty-base or nonzero-coefficient hypothesis is implicit in these sources.

Here is my object/hypothesis/conclusion checklist, formed from the node before
checking the Lean. Every row passes.

| Node item | Lean rendering and verdict |
| --- | --- |
| An integer N at least one | `(N : ℕ) (hN : 0 < N)`; precisely the positive integers. |
| A finite commutative ring killed by N | `(A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)`; scalar annihilation is equivalent to the cast being zero in a unital ring. No field or nontriviality assumption. |
| A Noetherian scheme S, meaning a finite affine Noetherian cover | `(S : Scheme.{u}) [IsNoetherian S]`; read Mathlib's class and `isNoetherian_iff_of_finite_iSup_eq_top`, which give exactly this convention. |
| N invertible on S | `hS : IsUnit (N : Γ(S, ⊤))`; a global inverse is equivalent to local invertibility, since the local inverses glue uniquely. |
| Ordinary module-valued small-etale derived categories | `DerivedCategoryModule A T`; read `DerivedCategories.lean` and upstream `Derived.Coefficients`, whose abbreviation is `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`. |
| Ordinary finite Tate lines and canonical inverse-image identifications | `ordinaryFiniteLine`, `OrdinaryFiniteTwistTransport`, `ordinaryFiniteShiftedLinePullback`; read the transport record, including root-inclusion and pure-generator normalizations, and the full `etaleFiniteTwistPullback` signature. These specify the canonical maps. |
| Any dimension d, including zero | `(d : ℕ)`; no positivity binder on dimension. |
| Relative affine d-space and its projection p | `affineTraceTower S d`, `affineTraceProjection S d`; read `AffineTraceTower.lean`, its coordinates, and `affineTraceAffineSpaceIso S d` to Mathlib's `AffineSpace (ULift (Fin d)) S`. |
| The explicit coordinate-tower counit trace | `affineTraceCounit A N hA t D S hS d`; read its definition as the actual composite adjunction counit and `OrdinaryFiniteP1Datum` with its Kummer, decomposition and counit-normalization fields. |
| Every invertible d-by-d matrix of global functions | `(g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤))`; read Mathlib's definition as units of the matrix ring. No determinant restriction beyond invertibility. |
| Its S-automorphism v mapping to gv | `affineTraceLinearMap S d g`; row i is the sum over j of the pullback of `g i j` times coordinate j. `AffineSpace.homOfVector` then the inverse canonical tower identification gives exactly this map. |
| Compact-support exchange for the actual Cartesian square (a_g, identity) | The conclusion supplies `sq : IsPullback (affineTraceLinearMap S d g) p p (𝟙 S)`. This certifies the specified map is over S and invertible; with bottom identity the Cartesian condition is equivalent to invertibility of its top map. It adds no hypothesis or arbitrary arrow. |
| Exchange followed by the canonical coefficient comparison | `affineLinearTraceAction` uses `rightDerivedLowerShriekBaseChangeMap A sq`, then the image of `affineLinearCoefficientPullback`, conjugated by `affineLinearCompactComparison`. This is the specified rho_g on the counit's source. |
| The equality t composed with rho_g equals t | `affineLinearTraceAction ... sq ≫ affineTraceCounit ... = affineTraceCounit ...`; Lean's left-to-right composition is precisely the displayed node equality. The final sentence of the node is its interpretation, including d=0. |

I checked the two representation parameters particularly carefully. The transport
`t` is determined by the root inclusion and pure generators, so it is not a free
orientation. `D` is a family of the dependency's normalized projective-line data:
`chern_spec` specifies the Kummer Chern class, `decomposition_hom` fixes both
components, and `counit_normalization` fixes the counit through the projection
formula. These are presentations of the trace specified in the node. Quantifying
over their normalized presentations introduces no extra mathematical restriction
on N, A or S and no different trace. The dependency's existence theorem supplies
such presentations; no independent base-change hypothesis on D is needed to state
the invariant equality. The normalized trace is unchanged between presentations.

For the coefficient comparison, I followed `affineLinearLineDescent`,
`affineLinearCoefficientDescentStep`, and its `Nat.rec` definition. They use the
existing tensor pullback, inverse-image composition, and normalized shifted-line
comparisons, to express the tower coefficient as p* of the ordered tensor of d
shifted lines on S. `affineLinearCoefficientPullback` pulls this same descent along
a, uses a composed with p equals p, and undoes the descent. Thus it is the
canonical comparison on A(d)[2d], including its tensor and shift normalizations;
there is no inserted scalar or choice of the dependency's bare `Nonempty` iso.

For compact supports I read the recorded `LowerShriek` definitions and compatibility
isomorphisms, `CompactSupportFiniteTorsion.lean`, and upstream
`LowerShriekBaseChange.lean`. The latter's actual exchange is proper derived
exchange followed by open exchange and the canonical compactification comparison.
I also obtained and read the published `LowerShriekPlusBaseChange` source using
`scompile.py --source`. The bounded-below/unbounded models use those canonical
restriction comparisons. `affineLinearCompactComparison` extracts only the
boundedness proposition for the fixed coefficient from `exists_affineSpaceTopTrace`;
its `Exists.elim` selects no data. The object is independent of t and D, so the
existential extraction is valid for every presentation used in the statement.
All three statement-dependency interfaces (coefficients, counit trace and compact
supports), as well as Scheme and affine space, were checked from declarations,
not inferred from their names. No dependency module or new node is needed.

Edge cases: d=0 leaves an empty matrix index and empty sums; the tower projection
and adjunction are identities and the canonical descent starts with the identity
pullback comparison. The existential square still applies. Empty S is allowed:
there is no point, connectedness or nonempty hypothesis on S. A may be the zero
ring, and N=1 is allowed with its resulting zero coefficients. N=0 is excluded by
the node itself. No additional residue-characteristic restriction occurs beyond
N being invertible. Matrix entries are global functions on any Noetherian S,
not merely an affine S. Schemes have the arbitrary universe u; coefficients and
module objects use the common u+1 convention of the recorded dependencies, and
ULift only raises the finite coordinate type. No independent site universes are
identified, and finiteness of A introduces no size loss. All binders and the sole
universe are explicit under `autoImplicit false`.

Independent searches, using queries different from the first worker's:

- LeanFinder via `msearch.py`: "An invertible matrix acts trivially on integration
  of the Tate twisted constant sheaf on affine space". Eight hits, mainly
  `AffineSpace` coordinate equivalences and Picard functoriality; none states
  etale compact-support trace invariance.
- Loogle via `msearch.py`: `"trace", "affine"`. Zero hits, successful query.
- LeanSearch via `msearch.py`: "Integration in compactly supported etale cohomology
  of affine space is unchanged by an invertible matrix". Eight hits about real
  integration and change of variables, none about this statement.
- `rg` in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`, using
  `linear.*trace|trace.*linear|affine.*trace|trace.*affine` and a narrower
  `integration|compact.*trace|trace.*compact|coordinate.*change` search. The
  pertinent project results are the already used tower and top-trace modules;
  other results concern unrelated matrix traces, Fourier transforms, or other
  coefficient comparisons. No duplicate action or invariance statement.
- An exact-name search for all ten proposed declarations across the entire
  Mathlib source, upstream and project Lean returned no collisions. The item id
  is absent from upstream and `dag/lean_names_upstream.json`.

H5/H6/H8/H9 checks: every helper has real data assembled from the recorded
canonical constructions. The only postponed theorem is this node's theorem;
its proof is `sorry`. The theorem docstring follows all seven node steps in
order: universal GL family, actual exchange/pasting, scalar via degree-zero
full faithfulness, connected residue-field fibres, identity value, equality of
sections, and pullback along g. Every declaration has its source/blueprint
citation. There is no private definition, local notation or local instance.
All Lean lines are at most 100 characters. The node's `lean.statement` is
verbatim identical to the theorem signature (checked mechanically).

Mismatches and changes: none found. The Lean module and node record are left
unchanged; only this independent second-reading section is appended. No
statement correction, new definition node or dependency repair is called for.

Validation: the prescribed `scompile.py NL lem-amb-linear-trace-invariance` command
compiled the delivered module as sandbox and library files in 6.7 s and 9.9 s,
respectively, with no errors or warnings and without changing any resource limit.
