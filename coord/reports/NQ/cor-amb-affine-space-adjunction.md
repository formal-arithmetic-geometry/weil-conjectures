## Worker report

The new module `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction` states
`AlgebraicGeometry.Etale.nonempty_affineSpaceAmbientAdjunction`. Its sole theorem has
proof `sorry`. There are no new definitions, auxiliary theorems, dependency repairs,
or changes to the natural-language node. The statement is the existence of an adjunction
between the specified existing functors, expressed as `Nonempty (F ⊣ G)` because an
adjunction is data and a Lean theorem must assert a proposition. No unit, counit, or
normalization beyond the node's adjunction assertion is imposed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Positive integer N, including N = 1 | `(N : ℕ) (hN : 0 < N)` |
| Finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| NA = 0 | `(hA : (N : A) = 0)`; equivalent to N killing every element by multiplication with 1 |
| Noetherian scheme S admitting a finite Noetherian affine cover | `(S : Scheme.{u}) [IsNoetherian S]`; Mathlib `isNoetherian_iff_of_finite_iSup_eq_top` gives exactly the stated cover criterion |
| N invertible on S | `(hS : IsUnit (N : Γ(S, ⊤)))`; a global section is a unit exactly when it is a unit in every stalk |
| Arbitrary dimension d in the natural numbers | `(d : ℕ)` with no positivity restriction |
| Affine d-space over S | `AffineSpace (ULift.{u} (Fin d)) S`, exactly the coordinate specialization in `def-sbc-affine-space.mathlib_match` |
| Its projection p_d | `(AffineSpace (ULift.{u} (Fin d)) S ↘ S)`, the first projection of the defining base change |
| Ordinary small-etale constant-A module sheaves | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)` inside both functors, the recorded `DerivedCategoryModule A T` encoding |
| Entire ordinary unbounded derived categories | Existing `rightDerivedLowerShriek`, `mapDerivedCategory`, and `derivedTensorRight` all act on the full `DerivedCategory` of those sheaves |
| Rp_d! defined by compactification | `rightDerivedLowerShriek (ModuleCat.{u + 1} A) p_d`; its body is `rightDerivedLowerShriekOfCompactification` at the existing chosen compactification, the exact recorded candidate of `def-amb-etale-compact-support` |
| Compactification-independent identification | Import of `UnboundedEtaleCompactSupportComparisons`, whose canonical refinement isomorphisms identify that candidate with all other compactifications; the theorem requires no chosen compactification argument |
| p_d^* = p_d^-1, applied termwise | `(upperStar (ModuleCat.{u + 1} A) p_d).mapDerivedCategory`, the descent of exact inverse image, not an extra derived replacement |
| Ordinary finite Tate sheaves A_T(d), including A_T(0) | `Scheme.finiteEtaleTateTwist T N A hA d`, the recorded roots-of-unity scalar extension and nonnegative tensor powers |
| Regard the Tate sheaf as a degree-zero complex | `(DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateTwist T N A hA d)` |
| K(d) = K tensor^L_A A_T(d) | `derivedTensorRight (ModuleCat.{u + 1} A) T` applied to that degree-zero object; this is the flip of the recorded `derivedTensor` bifunctor |
| Cohomological shift [2d] | `shiftFunctor _ (2 * (d : ℤ))` |
| Rp_d! left adjoint to p_d^*(-)(d)[2d] | `Nonempty (rightDerivedLowerShriek ... ⊣ ((upperStar ...).mapDerivedCategory ⋙ derivedTensorRight ... ...) ⋙ shiftFunctor ... )` |
| No boundedness or constructibility on either argument | No bounded subcategory, object property, cohomological bound, or constructibility binder occurs; `Adjunction` provides natural Hom equivalences for every object of both full categories |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme form
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace` and
  `AffineSpace.over`, specialized to `ULift.{u} (Fin d)`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded ordinary
  `AlgebraicGeometry.Etale.DerivedCategoryModule` encoding, defined in its public import
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`; the resulting exact inverse image
  is used in the module-valued encoding as `Etale.upperStar` and its `mapDerivedCategory`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`, whose full construction was read.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor` and `derivedTensorRight` (its right-tensor variant).
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and its chosen-
  compactification wrapper `rightDerivedLowerShriek`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleCompactSupport_comparison_coherence`,
  `unboundedEtaleCompactSupport_refinement_normalization`,
  `unboundedEtaleLowerShriekCompIso` and the recorded
  `unboundedEtaleCompactSupport_baseChange` package. Their role here is to identify the
  chosen compact-support functor and provide its unbounded composition in the proof plan.

The module also imports every recorded proof-dependency module. In particular the
projective-line adjunction is `exists_projectiveLineFullAdjunction` in
`Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction`; twist transport is
`Scheme.etaleFiniteTwistPullback`; and the affine chart, projective properness, open
adjunction, inverse-image composition and finite-flat-twist modules follow the node's
six proof steps. `WeilConjectures.Compactification.Affine` supplies the existing
`HasCompactification.affineSpace_over` instance, which is discharged automatically rather
than added as a theorem hypothesis. There are no omitted proof imports or import cycles.
The declaration docstring gives the six-step natural-language proof, including the flat
Tate-tensor calculation, zero-dimensional case, and induction.

Edge cases checked mathematically before writing:

- `d = 0`: the coordinate type is empty and the projection is canonically an isomorphism;
  the Tate exponent and shift are zero. Thus the claimed adjunction is the identity
  adjunction under the canonical identifications. No `0 < d` is imposed.
- `d = 1`: the formula is exactly the projective-line/open-chart composite adjunction.
- `N = 1`: the annihilation condition forces A to be the zero ring, which is allowed;
  its module derived categories are zero categories and the assertion still holds.
- Arbitrary zero coefficient ring A and the empty scheme S are allowed. Neither a
  `Nontrivial A` nor a nonempty-scheme hypothesis occurs.
- The invertibility assumption excludes the characteristic dividing N case on nonempty
  schemes, where purity with these coefficients would fail. No extra residue-characteristic
  restriction is imposed.
- Unbounded complexes in either direction are included: no amplitude or Tor-amplitude
  assumption occurs. The Tate tensor is the unbounded K-flat construction already recorded.
- Explicit universe `u` is shared by S and the affine coordinate lift; coefficients and
  sheaf values use the recorded `u + 1` size convention. No new universe equality or
  auxiliary size hypothesis is added.

Searches made for an existing declaration (2026-10-16):

- `msearch.py ... leanfinder`, query: "The derived compact support pushforward of affine
  space is left adjoint to inverse image with Tate twist and shift twice the dimension".
  Eight hits: `CondensedMod.LocallyConstant.adjunction`,
  `SheafOfModules.pushforwardPushforwardAdj`, `LightCondMod.LocallyConstant.adjunction`,
  the ordinary scheme-module and sheaf-module pullback left-adjoint instances, their
  pushforward right-adjoint instances, and `TopCat.Sheaf.pullbackPushforwardAdjunction`.
  None is the compact-support/Tate-shift adjunction.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.AffineSpace, CategoryTheory.Adjunction`: zero hits.
- `msearch.py ... grep`, query:
  `affineSpace.*[Aa]djunction|[Aa]djunction.*affineSpace|[Aa]ffine.*[Ss]hriek`,
  directory `AlgebraicGeometry`: zero hits in Mathlib.
- Direct `rg` of the upstream `WeilConjectures` and side `lean/Sheaf` trees for
  `affineSpace.*[Aa]djunction|[Aa]djunction.*affineSpace|cor-amb-affine-space-adjunction`:
  only a natural-language citation in `Sheaf/Paper/EtaleGeometricBiduality.lean:294`;
  no existing declaration. The proposed declaration name is absent as well.
- A further upstream search for `AffineSpace|affineSpace` in compactification sources
  located `HasCompactification.affineSpace_over` in `WeilConjectures.Compactification.Affine`.
  Read and reused this construction instead of defining a compactification again.

No STATEMENT-DISPUTED issue or node fault was found. The earlier stage-1 correction's
explicit coefficient and Noetherian hypotheses are retained verbatim in mathematical content.

Validation: the delivered file compiled cleanly, both as a sandbox file and at its library
module path, through `scompile.py NQ cor-amb-affine-space-adjunction`. No errors or warnings
were emitted. The required `deliver2.py ... --no-push` dry run is the final check; no delivery
is pushed by this worker, and the independent second reader supplies the second reading.

## Second reading by NQ

Independent reading on 2026-10-16. I read the sandbox node and module, the source
blueprint paragraph and its unit section, and the recorded statement-dependency nodes
and the declarations used below. The checklist extracted from the node before assessing
the Lean is as follows. Each row is a separate object, hypothesis, convention, or conclusion;
all verdicts concern the complete signatures and definitions, not their names alone.

| Node checklist | Lean rendering and verdict |
| --- | --- |
| An integer N at least one | `(N : ℕ) (hN : 0 < N)`. Pass: these are exactly the allowed positive integers. |
| A finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`. Pass; no field, nontriviality, or characteristic instance is added. |
| N kills A | `(hA : (N : A) = 0)`. Pass: multiplying this equation by any element gives annihilation of A, and annihilation applied to 1 gives this equation. |
| A Noetherian scheme S, with the stated finite Noetherian affine-cover meaning | `(S : Scheme.{u}) [IsNoetherian S]`. Pass: Mathlib's class is locally Noetherian plus compact; `isNoetherian_iff_of_finite_iSup_eq_top` and `isNoetherian_iff_of_finite_affine_openCover` give exactly this cover criterion. |
| N invertible on S | `(hS : IsUnit (N : Γ(S, ⊤)))`. Pass: a global unit gives a unit in every stalk. Conversely `RingedSpace.isUnit_of_isUnit_germ` glues the local inverses, so no stronger condition is imposed. |
| Every natural dimension d | `(d : ℕ)`. Pass; there is no positivity condition on d. |
| The relative affine d-space and its projection p_d | `AffineSpace (ULift.{u} (Fin d)) S` and `(AffineSpace (ULift.{u} (Fin d)) S ↘ S)`. Pass: Mathlib defines the space by base change of the integral polynomial spectrum, and `AffineSpace.over` is `pullback.fst`. These are precisely `def-sbc-affine-space` and its recorded specialization. |
| Ordinary small-etale sites and constant-A module sheaves | All three functors specialize their coefficient category to `ModuleCat.{u + 1} A`. Pass: their source and target are `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`, the exact encoding recorded by `def-weil-pbc-derived-categories`. |
| The entire unbounded categories on the affine space and on S | The unqualified `DerivedCategory` in the source definitions. Pass: no `Plus`, `Bounded`, constructibility predicate, or restricted object quantifier is used. |
| Compact-support functor defined by compactification | `rightDerivedLowerShriek (ModuleCat.{u + 1} A) p_d`. Pass: its definition is `rightDerivedLowerShriekOfCompactification` for the existing chosen compactification; the latter is exact derived open extension by zero followed by unbounded total right derived direct image. It is not a right derivation of the underived composite. |
| Compactification-independent identification | The imported `UnboundedEtaleCompactSupportComparisons`, together with its existing comparison isomorphisms. Pass: the theorem fixes no additional compactification or normalization datum. Existence of the adjunction transfers across the recorded canonical comparison with any other compactification. |
| Exact inverse image p_d^* = p_d^-1 applied termwise | `(upperStar (ModuleCat.{u + 1} A) p_d).mapDerivedCategory`. Pass: this is the existing module-valued sheaf inverse image and its exact-functor descent; it introduces no exceptional inverse image or bounded derived substitute. |
| The roots-of-unity sheaf with its exponent action and scalar extension defining A_T(1) | `Scheme.finiteEtaleTateTwist T N A hA 1`. Pass: its body is `finiteEtaleTateLine`; this sheafifies `finiteEtaleMuModulePresheaf` followed by `ModuleCat.extendScalars (finiteEtaleTwistScalar N A hA)`. The presheaf uses the existing `rootsOfUnitySheaf` and its unique `ZMod N` action. |
| A_T(0) = A_T and positive tensor powers | `Scheme.finiteEtaleTateTwist T N A hA d`. Pass: its zero branch is the constant sheaf of `ModuleCat.of A A`, its one branch is the preceding line, and its successor branches tensor by that same line. |
| K(d) is derived tensor with A_T(d) | `derivedTensorRight ... T ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateTwist T N A hA d))`. Pass: `singleFunctor` places the actual sheaf in degree zero, and `derivedTensorRight` is `(derivedTensor ...).flip.obj`, hence tensors the varying K on the right with that object. |
| The cohomological shift [2d] | `shiftFunctor _ (2 * (d : ℤ))`. Pass: integer multiplication by two, with the positive sign specified in the node. |
| Rp_d! is left adjoint to p_d^*(-)(d)[2d], naturally for both unrestricted arguments | `Nonempty (rightDerivedLowerShriek ... ⊣ ((upperStar ...).mapDerivedCategory ⋙ derivedTensorRight ... ...) ⋙ shiftFunctor ... )`. Pass: functor composition applies inverse image, then tensor on the affine space, then shift. An `Adjunction` supplies the natural Hom equivalences for all objects. `Nonempty` asserts existence of this data without prescribing an extra unit or counit. |

Dependency and source checks:

- Opened `Mathlib.AlgebraicGeometry.AffineSpace` at its definition and `over` instance,
  and `Mathlib.AlgebraicGeometry.Noetherian` at the class and the finite affine-cover
  equivalences. These are the recorded Mathlib notions, with no private replacements.
- Opened `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `DerivedCategoryModule`
  abbreviates the full derived category of module-valued small-etale sheaves.
- Opened `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`, and upstream
  `SixFunctors.Etale.UpperLowerStar.Defs` at `upperStar`, its adjunction, finite-limit
  preservation, and homology preservation. The module-valued encoding used here is
  the permitted constant-ring-module encoding; `mapDerivedCategory` is its termwise
  exact descent. No arbitrary map or auxiliary exactness hypothesis is substituted.
- Read the full `FiniteEtaleTateTwist` construction. The roots-of-unity input is
  upstream `Scheme.rootsOfUnitySheaf`, the kernel of N on the multiplicative-group
  sheaf. Its module enhancement, scalar extension, and tensor powers give the node's
  sheaves. The symmetry identifying `A tensor μ_N` with `μ_N tensor A` is harmless.
  Checked Stacks `etale-cohomology.tex`, Section 03PK, lines 2819 onward, and
  `groupoids.tex`, Example 040M, lines 418 onward: the group is exactly units z with
  z^N = 1; Kummer exactness uses invertibility of N, already assumed here.
- Opened upstream `Derived.Tensor` at `derivedTensor` and `derivedTensorRight`:
  these are the existing K-flat unbounded tensor bifunctor and its right-tensor
  specialization. The sheaf tensor in the Tate construction is the corresponding
  canonical module-sheaf tensor, not a second coefficient tensor.
- Opened upstream `Derived.LowerShriek` at both compactification-specific and chosen
  compactification functors, and `Compactification.Affine` at
  `HasCompactification.affineSpace_over`. The required compactification is constructed
  for every finite coordinate type over every S and introduces no extra binder.
- Read the canonical composition, comparison coherence, and refinement normalization
  signatures in `UnboundedEtaleCompactSupportComparisons`. Checked Stacks
  `more-etale.tex`, Tags 0F7H/0F7I/0F7J, lines 3047 onward. The source explicitly gives
  whole unbounded categories when the coefficient ring is torsion. Positive N and
  `(N : A) = 0` supply precisely that condition. Noetherian bases and finite affine
  projections satisfy the quasi-compact, quasi-separated, separated finite-type
  hypotheses there; these are consequences, not additional assumptions.
- Opened `ProjectiveLineFullAdjunction.exists_projectiveLineFullAdjunction` and
  `EtaleAmbientAdjointLocality.derivedEtaleLowerShriekUpperStarAdjunction`. Their
  coefficient and base conditions are the ones present here. Compared all six proof
  paragraphs of the node with all six numbered docstring steps: geometry and
  compactification, open adjunction, affine-line composite, flat-twist calculation,
  zero dimension, and induction are all retained. The proof-dependency modules are
  imported, including affine compactification and ordinary twist transport.

Edge cases:

- `d = 0` is included literally: `ULift (Fin 0)` is empty, its affine projection is
  an isomorphism, the twist is the constant coefficient sheaf, and the shift is zero.
  This also checks the only empty index set in the statement.
- `d = 1` has the affine-line formula, with positive twist and shift by two.
- `N = 1` forces the coefficient ring to be the zero ring; neither `CommRing` nor
  `Finite` adds a nontriviality condition. The general zero ring is permitted too,
  and its zero objects and zero complexes are included in the full categories.
- The empty scheme is permitted; global-section invertibility has the correct
  vacuous stalk interpretation there. No nonempty-scheme hypothesis occurs.
- For a nonempty scheme, the invertibility condition rules out residue
  characteristics dividing N exactly as required; no characteristic-zero, field,
  connectedness, separatedness-over-a-field, or finite-type-over-a-field condition
  has been added to S.
- The explicit `universe u` is arbitrary. Coordinates use `ULift.{u} (Fin d)`,
  schemes have universe u, and coefficients and module values use the recorded
  u+1 convention. No independent lower test universe, equality of site universes,
  unbound variable, or extra smallness instance occurs. Arbitrarily unbounded
  complexes and both zero and nonzero objects are quantified by the adjunction.

Independent searches with words beyond the first worker's searches:

- `msearch.py NQ cor-amb-affine-space-adjunction leanfinder`, query
  `For affine n-space with finite torsion coefficients, compactly supported direct
  image is left adjoint to pullback tensored with the orientation sheaf in degree
  minus twice n`: eight ordinary sheaf/module pullback-adjunction hits, none the
  exceptional compact-support adjunction.
- `msearch.py ... loogle`, query `AlgebraicGeometry.AffineSpace, _ ⊣ _`: zero hits.
  An earlier query naming `AlgebraicGeometry.Etale.rightDerivedLowerShriek` was not
  usable evidence because Loogle does not index that upstream identifier; it was
  therefore replaced by the preceding Mathlib-only query.
- `msearch.py ... grep`, query `orientation|extraordinary|purity`: its 25 returned
  Mathlib hits concern unrelated orientation constructions. Direct `rg` of
  Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf` for affine-space
  adjunctions and affine purity identified the nearby declarations below, which
  I opened rather than dismissing by name. The proposed full declaration name
  has no hit in `dag/lean_names_upstream.json` or those source trees.
- Upstream `EtaleCohomology/Purity/Smooth/AffineSpace.lean` contains
  `nonempty_iso_rightDerivedUpperShriek_affineSpace`. Its signature assumes a
  separated finite-type scheme over a field, normalized abstract Tate data, and
  `boundedConstructibleFiniteTor` on K; its conclusion is an objectwise
  exceptional-inverse-image isomorphism. It is not this unrestricted adjunction
  with the specified finite-etale twists, so it cannot be recorded as an exact
  existing match.
- Side `AffineSpaceTopTrace.affineTraceAdjunction` is a literal iterated adjunction
  conditional on twist transport and projective-line adjunction data. Its functors
  use a recursively defined coordinate tower and iterated right functors; its
  signature does not assert the adjunction for the two specified functors here.
  It supplies useful proof constructions but is not an existing statement of this
  node. The other hits were ordinary affine quasi-coherent-module adjunctions or
  natural-language citations, not exact matches.

Mismatches found and changes: none in the Lean statement or node record. I retained
the correct module and verbatim `lean.statement`. Only this independent second-reading
section was appended. There are no new definition nodes or dependency modules in this
delivery to review, and no stage-2 `statement_change` requiring a citer audit. The
previous stage-1 refinement already made the source's coefficient and base hypotheses
explicit; this delivery preserves them.

H5/H6/H8/H9 check: the file contains no new definitions, no proof beyond its single
named theorem with `by sorry`, no local notation/instance or private helper, and no
line longer than 100 characters. Both module and theorem docstrings name the source
and blueprint id. The theorem docstring carries the complete six-step proof plan.
Its signature is byte-for-byte equal to the node's `lean.statement` before `:= by`.

Validation: `scompile.py NQ cor-amb-affine-space-adjunction
lean/Sheaf/AlgebraicGeometry/AffineSpaceAmbientAdjunction.lean`, run from the sandbox,
passed both its sandbox and library-path compiles (5.6 seconds each), with no errors
or warnings. No live source was edited and no global build was run.
