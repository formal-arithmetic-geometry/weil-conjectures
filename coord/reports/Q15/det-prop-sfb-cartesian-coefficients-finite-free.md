## Worker report

The module `Sheaf.Paper.CartesianCoefficientsFiniteFree` states
`AlgebraicGeometry.ProEtale.cartesianCoefficients_finiteFree`. Its sole postponed
proof is `sorry`. The natural-language proof in its docstring follows the node's
nine steps. The node's natural statement and dependency lists are unchanged.

Hypotheses and clauses, checked against the node and its current blueprint source:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Finite extensions inside the fixed algebraic closure:
  `{E F : PadicAlgCl.FiniteIntermediateField ℓ}`. This is the existing subtype of
  intermediate fields finite dimensional over `Padic ℓ`, with the inherited
  absolute value topology. Inclusion is `(h : E ≤ F)`. Equality is allowed, as it
  is in the coefficient-map dependencies.
- The degree d = [F:E]: `finiteCoefficientDegree ℓ h` specializes
  `Module.finrank` to the scalar action `Module.compHom F.1
  (IntermediateField.inclusion h).toRingHom`. No independent or arbitrary action
  is supplied.
- An integral basis: `finiteCoefficientIntegralBasis ℓ h` is Mathlib's
  `Module.Basis (Fin d) (PadicAlgCl.integers ℓ E.1)
  (PadicAlgCl.integers ℓ F.1)` for the actual integer inclusion. The abbreviation
  only supplies that inclusion's module instance. `Nonempty` asserts existence,
  explicitly established in steps 1--2 of the node's proof. The following `∀ b`
  covers every choice, rather than making the conclusion depend on a selected
  basis from an existence theorem.
- An arbitrary scheme: every family and compatibility clause binds
  `X : Scheme.{u}` explicitly. No geometric or Noetherian hypothesis is imposed.
- Integral finite freeness: `e₀ X` is an isomorphism in the category of internal
  modules from `Mod.finiteFree` of the integral coefficient ring to the regular
  upper integral ring restricted by `Mod.comap` along its canonical inclusion.
- Rational finite freeness: `e₁ X` is the analogous internal-module isomorphism
  along the existing `padicSubfieldRingObjMap X ℓ h`.
- Formula `(a_i) ↦ sum a_i b_i`: `finiteCoefficientPointSummand` postcomposes a
  continuous function with `a ↦ φ(a) * t`, section by section, including the
  universe lift. `finiteCoefficientIntegralSummand` and
  `finiteCoefficientRationalSummand` apply the existing `upperStarFromPoint X`
  to that actual additive sheaf morphism. The first two conjuncts prescribe
  `finiteCoefficientIntegralLeg ... i ≫ (e₀ X).hom.hom` and the rational
  counterpart to be precisely these maps. Here the legs are the existing
  biproduct injections. Additivity makes the values on those injections exactly
  equivalent to the displayed finite-sum formula; the isomorphisms are therefore
  specified rather than arbitrary.
- Compatibility with integral-to-field maps: the third conjunct is the square
  with `padicIntegersToPadicSubfield X ℓ E` and its F counterpart, after each
  integral coproduct injection. The missing diagonal leg in a full-power square
  is uniquely the coproduct map whose i-th component is the E integral-to-field
  map followed by the i-th rational injection. Thus the component equations state
  precisely the full square, with no extra condition.
- Compatibility with inverse image: the fourth and fifth conjuncts quantify over
  every `X`, `Y`, `f : X ⟶ Y`, and summand `i`. They compare `upperStar f` of the
  relevant basis component with the component on X using the existing
  `condensedPullbackHom`. Inverse image preserves these finite coproducts, so the
  component equations are exactly the two full inverse-image squares under the
  canonical coproduct comparison. This includes identity morphisms and all
  compositions, without assuming properness or finite type.
- Flatness of both coefficient rings: the final conjunct states
  `PreservesFiniteLimits (Mod.extendScalars ...)` for both the integral and the
  rational inclusion and for every X. The proof's final step explicitly defines
  the asserted flatness this way. Right exactness is already part of the existing
  scalar-extension adjunction; it is not added as a new clause.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, importing the full coefficient-extension
  constructions. The actual embedded valuation rings here use the already
  published `PadicAlgCl.integers`, `normedFieldOfAlgebra`, and `integersMap` from
  `WeilConjectures.NumberTheory.Padics.Extension` and `IntegersFinite`.
- `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingObjOfUniverse`, exports the existing
  `Profinite.continuousMapRingObj` used by the published coefficient interfaces.
  Our actual coefficient fields and their integer rings live in `Type 0`, so
  the upstream section construction with values in `Ab.{u+1}` applies. No
  coefficient-universe equality is imposed on the scheme site. This is the
  same continuous-function notion already listed in this dependency's upstream
  audit, not a redefinition of condensed rings.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`,
  `upperStarFromPointComp`, `condensedPullbackHom`, and the ring-map instances.
  `coefficientRing` is the bundled version of the very same transported monoid
  structure used by `condensedRingObj` in the statement.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj`, `Mod`, `Mod.regular`,
  `Mod.comap`, and module morphisms. This is the closed upstream binding for
  `sk-def-sfb-module-objects`, which has no `lean` field.
- `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`:
  `padicIntegersToPadicSubfield`, read using `scompile.py --source`; the recorded
  module is absent in the older local checkouts. It is exactly the pullback of
  the condensed subtype inclusion, and not a localization used as a definition.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `padicSubfieldRingObj` and `padicSubfieldRingObjMap`, with the condensed inclusion
  from `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars`, `extendRestrictAdjunction`, `coextendScalars`, and
  `restrictCoextendAdjunction`; these are the closed upstream declarations of
  `sk-def-sfb-change-of-scalars`, which has no `lean` field. The existing scalar
  extension is the balanced coequalizer, not an unconstrained functor.
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`: `Mod.finiteFree`, the
  actual finite biproduct of regular modules. The existing module categories
  and finite biproducts are used throughout.

The delivered helper abbreviations merely instantiate these existing constructions
for the inclusion h, and name its degree, basis type, injections, and explicit
multiplication maps. Their full names are in `lean.declarations`. All their data
are constructed. No object is selected from a sorried existence theorem. The
`IsMonHom` instance is the inherited ring-sheaf postcomposition instance, not an
additional mathematical assertion with a postponed proof. No new independent
notion or dependency repair was necessary.

All available statement-dependency modules and stated proof dependencies are
imported. The still-unstated proof dependency
`det-prop-sfb-qlbar-colimit-x-invert-ell` has no module to import and is mentioned
in the proof plan, without inventing a replacement construction. The exact
finite-free statement is not assumed from the downstream flatness lemma.

Edge cases checked before writing:

- E = F is included; d = 1 and any integral basis gives multiplication by a unit.
- No field has degree zero, so the rank in the statement is the positive actual
  field degree. The helper finite biproducts themselves handle rank zero normally.
- Empty profinite test spaces give the unique function on both sides, consistent
  with the componentwise formula and the condensed construction.
- The empty scheme is permitted, with zero underlying sheaves. No nonzero-object
  or nonempty-scheme hypothesis excludes it.
- Identity and arbitrary inverse-image morphisms are included in the same formulas.
- The prime 2 and ramified field inclusions are permitted. No choice or
  compatibility of uniformizers is required.
- The single explicit universe u is the arbitrary scheme/site universe. All
  finite coefficient subfields of the fixed `PadicAlgCl ℓ` are in `Type 0` by the
  recorded framework's definition, and sections are lifted into `Ab.{u+1}`.

Searches for an existing statement or needed helper:

- `msearch.py leansearch`, query: "Finite extensions of p-adic fields give
  finite free condensed coefficient sheaves compatible with pullback and integral
  to rational maps". Eight hits concern finite fields, `Condensed.free`,
  `Condensed.finFree`, the p-adic field/fraction ring, and general condensed
  colimits. None states the finite-extension sheaf theorem or its compatibilities.

- `msearch.py leanfinder`, query: "A finite extension of p-adic fields gives
  finite free pro-etale coefficient sheaves naturally in the scheme". Eight
  results, all about etale algebras/presentations; none gives the sheaf basis
  isomorphisms and both compatibility clauses.
- `msearch.py loogle`, query `Condensed, Module.Free`: zero hits.
- `msearch.py grep`, query
  `padic.*[Ff]ree|[Ff]ree.*padic|continuousMap.*[Bb]asis`: zero hits in Mathlib.
- `rg` in the source `WeilConjectures` tree and `lean/Sheaf` for the node id,
  `finiteFree`, `finite_free`, and coefficient-basis patterns: the published
  `Compatibility` module has rational flatness and a docstring explaining finite
  freeness, but no matching integral/rational basis theorem. The project's
  `CondensedFlatCoefficientCalculus` gives unspecified rational freeness under
  an extra Noetherian hypothesis and omits all integral and naturality clauses;
  it is not a match. `LocalFieldIntegralBasis` is an arithmetic basis-existence
  statement, not the sheaf theorem.
- Searching the padic sources for integer-ring inclusions found
  `PadicAlgCl.integersMap`; the delivered inclusion specializes that exact
  existing map using the h-induced algebra and scalar tower.
- Searching the condensed ring sources and project topology modules for additive
  continuous-function postcomposition maps found no existing basis-summand map.
  The small delivered helper constructs one directly from Mathlib's
  `AddMonoidHom.mulRight`, `compLeftContinuous`, and universe-lift equivalences.

No statement correction or disputed statement. The repair note attached to this
item concerns the resolved stage-1 split and does not withdraw a Lean interface.

Validation: `scompile.py` compiled the complete module, in both its sandbox and
module-path checks, with no errors or warnings. The helpers were also checked
before assembling the theorem. No global build, direct repository edits, or
Git commands were run by this worker.

## Second reading by Q15

Independent maintainer second reading, 2026-10-18, of immutable delivery
0d8d9940c78ca0f5ae43fd313dd1a746000414ea. This section replaces the delivered
placeholder; the independent reader did not write or previously review this delivery.

I read the item, all eight statement-dependency records and their actual interfaces,
the blueprint statement and proof, the complete delivered module and worker report,
and the framework manifest. The statement matches its source. Clause-by-clause:

- Prime ell is `Fact ℓ.Prime`; finite embedded fields are
  `PadicAlgCl.FiniteIntermediateField ℓ`, and `h : E ≤ F` gives the actual inclusion.
  No Noetherian, properness, finite-type or nonempty-scheme hypothesis is added.
- `finiteCoefficientDegree` uses finrank with the inclusion-induced module action;
  `finiteCoefficientIntegralBasis` is the existing Mathlib basis on `Fin d` for
  the actual integer-ring inclusion. The explicit `Nonempty` is the basis
  existence asserted in the source proof; the following universal quantifier
  covers every basis, without choosing unknown data from this existence claim.
- `e₀` and `e₁` are genuine module isomorphisms from `Mod.finiteFree` (the finite
  biproduct of the regular module) to the upper regular ring restricted by the
  canonical coefficient map. Their quantification over all schemes permits both
  naturality squares for the same family of maps.
- The first two component equations prescribe multiplication by the image of
  each basis vector. `finiteCoefficientPointSummand` constructs postcomposition
  by `a ↦ φ(a) * b`, and the scheme summands apply `upperStarFromPoint.map`.
  Hence additivity gives precisely the displayed sum formula, not arbitrary maps.
- The third component equation is exactly the integral-to-field square using
  `padicIntegersToPadicSubfield`. Finite coproduct injections jointly determine
  the complete square.
- The next two equations use the canonical `condensedPullbackHom` comparisons
  and quantify over every scheme morphism. Inverse image preserves finite sums,
  so these equations on injections state the full inverse-image squares.
- The final conjunction says both actual scalar-extension functors preserve
  finite limits. Since these are the balanced tensor left adjoints, this is
  precisely flatness of the two upper coefficient rings.

Dependency/interface checks: the integer rings are the published unit balls
`PadicAlgCl.integers`, with their restricted topologies. The condensed rings
have sections C(S,T), and their maps are postcomposition. The Type-0 specialization
of the upstream condensed interface is the existing audited construction for
these embedded fields; importing the universe-polymorphic dependency introduces
no second coefficient notion. `condensedRingObj` is `upperStarFromPoint.obj`, with
the transported monoid structure of `coefficientRing`. `Mod`, `Mod.regular` and
`Mod.comap` are Mathlib's internal module notions. `Mod.extendScalars` is the
published balanced coequalizer, and coextension is its recorded equalizer
construction. I read `padicIntegersToPadicSubfield` through `scompile.py --source`
because that module is missing from the older local copies. Its body is exactly
the pullback of the integer-to-field inclusion.

Edge cases: E=F (degree one), ell=2, ramification, arbitrary and identity scheme
morphisms, empty profinite test objects and the empty scheme are all retained.
There is no degree-zero finite field extension. The finite biproduct construction
itself permits zero rank. The arbitrary scheme universe u is preserved, with
small-site object universe u+1, morphism universe u, and coefficients in
`AddCommGrpCat.{u+1}`. The finite embedded fields are already Type 0 by definition;
no equality between distinct site universes is imposed.

Independent searches: grep/rg for coefficient-basis and finite-free condensed
statements in project and Mathlib sources, Loogle for the inclusion interface,
and LeanFinder for finite-rank integral/rational condensed coefficient basis
isomorphisms. The latter returned solid free functors and discrete locally
constant module comparisons, which do not state this result. The existing
`condensedFiniteCoefficientCalculus` only gives rational freeness, imposes a
Noetherian-space hypothesis and omits the specified maps and compatibility
clauses. Arithmetic integral-basis existence also is not the full sheaf statement.
No duplicate theorem or independent helper notion was found.

Findings and repairs: H11, the original second-reading section was a placeholder;
this section supplies the actual reading. H6, the helper integer inclusion had
an inline scalar-tower proof (`change`/`exact mul_assoc`); it now uses the existing
`Subalgebra.inclusion.isScalarTower_right` instance. The canonical integer map,
all helper signatures, the theorem signature, node statement and dependency
records are unchanged. All helpers contain real data; the sole postponed local
mathematical theorem remains `cartesianCoefficients_finiteFree := by sorry`.
Every declaration has a source/blueprint docstring; its theorem docstring follows
all nine recorded proof steps. There are no overlong Lean lines or unbound names.

The item has no route-pivot repair note: its note is the resolved 2026-10-17
stage-1 split note. None of its statement/proof dependencies is on the current
route-pivot dropped list, and the delivered construction uses no dropped machinery.
The proof-only inversion-of-ell input is not needed to type the statement; its
future proof status is not a missing statement prerequisite.

Validation: the immutable file passed `scompile.py Q15
 det-prop-sfb-cartesian-coefficients-finite-free <snapshot module>` in both sandbox
and module-path checks (20.9 s and 9.1 s), with no errors or warnings. The corrected
complete module also passed both checks through the same wrapper (30.9 s and
14.8 s), with no errors or warnings. The installed
wrapper uses the server side overlay and its isolated per-file compiler; it
reported a private `/dev/shm/nt-tmp/.../.lbuild` overlay. No direct ssh command,
global build, live Lean write, project-clone edit, delivery or Git mutation was
performed. `lean.statement` remains verbatim the theorem signature in both files.
