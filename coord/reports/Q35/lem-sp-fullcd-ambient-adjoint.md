## Worker report

The module `Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint` states
`AlgebraicGeometry.Scheme.sfAmbientCompactSupport_preservesCoproducts_and_hasAmbientDatum_of_fullCD`.
Its only theorem has proof `by sorry`; it introduces no definition, alternative coefficient
presentation, arbitrary comparison map, or new hypothesis. The declaration docstring carries
all ten natural-language proof steps of the node, including their named dependencies.

The source unit `sec-smooth-purity/sk-prop-sf-existence/_section.md`, clause (b), was read
from the project server, since the literature text is absent from this machine's shared
mirror. It states the conditional coproduct/right-adjoint conclusion and compactification
independence on the ordinary unbounded pro-etale categories. The node's refinement conclusion
uses the recorded ambient datum. The local and current server versions of that datum were
both read; they agree.

Hypothesis and conclusion correspondence:

- Prime: `(l : ℕ) [Fact l.Prime]`.
- Finite extension of the specified p-adic field: `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- Positive coefficient level: `(n : ℕ) (hn : 1 ≤ n)`. The ring is exactly
  `Padic.coefficientExtensionRing l E n`, using the recorded valuation ring and uniformizer.
  `Padic.finite_coefficientExtensionRing l E n hn` supplies the finite-ring instance
  explicitly to the existing functor; finiteness is not an added assumption.
- Scheme base and prime invertibility: `(S X Y : Scheme.{u})` and
  `(hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))`.
- Finite-type S-schemes: `[X.Over S] [Y.Over S]`, together with
  `[LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]` and the analogous Y instances.
- S-morphism: `(f : X ⟶ Y) [f.IsOver S]`.
- Finite type and separatedness of f: `[LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f]`.
- Chosen compactification: `(d : Compactification f)`. Its fields are the ambient scheme
  `d.Z`, open immersion `d.i`, proper map `d.g`, and equation `d.comm : f = d.i ≫ d.g`.
  The properness and openness fields are already instances, not extra hypotheses.
  Its S-structure is the composite through Y, exactly as in the dependency node.
- Nonnegative integer bound: `(c : ℕ)`. This is equivalent to an integer c ≥ 0 and includes c=0.
- FullCD hypothesis: `(hcd : sfFullCohomologicalDimension d.g
  (Padic.coefficientExtensionRing l E n) c)`. This is the recorded two-clause predicate
  on all original-source module sheaves and their pullbacks on pro-etale base changes;
  it is not the stronger upstream predicate on all base-changed sheaves.
- The compact-support candidate is the existing `sfAmbientCompactSupportCandidate` at
  d. Its definition is `(sfIntrinsicExtensionByZero d.i A).mapDerivedCategory ⋙
  proEtaleConstantDerivedDirectImage d.g A`. Thus it is precisely D(j_!) followed by Rp_*,
  on `proEtaleDerivedCategory X A` and `proEtaleDerivedCategory Y A`.
- Coproduct preservation is the first conjunct:
  `∀ I : Type w, PreservesColimitsOfShape (Discrete I) (...)`. The universe w is arbitrary,
  and I has no nonemptiness, finiteness, boundedness, or constructibility restriction.
  This is the usual preservation of all existing set-indexed coproduct cocones and
  their canonical comparison maps, not a choice of some isomorphism between objects.
- The second conjunct is exactly
  `HasAmbientExceptionalRightAdjointDatum l E n hn S X Y hS f d`, the recorded existence
  predicate for `SfAmbientExceptionalRightAdjointDatum A f d`. Its `rightAdjoint d` and
  `adjunction d` provide Rf_n^times and the natural Hom bijections at the distinguished d.
  It additionally supplies these functors and adjunctions at every compactification;
  `theta` and `rho` are natural isomorphisms for every refinement;
  `unit_compatibility` and `counit_compatibility` are exactly the two equations;
  `theta_id`, `rho_id`, `theta_comp`, `rho_comp` are the identity and cocycle equations.
  Its `fullCD` field asks for an existential nonnegative bound for the distinguished d;
  the supplied c and hcd give that witness. No bound on another compactification is assumed.
  The right-adjoint existence is already part of this conjunct, so it is not replaced
  by the weaker assertion of just an abstract left-adjoint instance.

Dependency declarations used (their full signatures and docstrings were read):

- `WeilConjectures.Compactification.Refinement`: `AlgebraicGeometry.Compactification.Refinement`
  and `AlgebraicGeometry.Compactification.category`, with the underlying
  `AlgebraicGeometry.Compactification` from `.Defs`.
- `Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension`:
  `AlgebraicGeometry.Scheme.sfFullCohomologicalDimension`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; this retains the small-site object
  universe u+1 and morphism universe u, with module values in u+1.
- `Sheaf.Paper.SfDerivedDirectImage` reexports the finite-level
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage` from
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`, which is the ordinary
  K-injective right derived functor used by the candidate, not its completed integral image.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting `Padic.coefficientExtensionRing`
  from `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over`, `Scheme.Hom.IsOver`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper` and
  `AlgebraicGeometry.IsSeparated` (via its imported module).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`:
  `AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate`,
  `AlgebraicGeometry.Scheme.SfAmbientExceptionalRightAdjointDatum`,
  `AlgebraicGeometry.Scheme.HasAmbientExceptionalRightAdjointDatum`.

The compatible stated proof dependencies are imported without `public`; a proof-only
dependency that is also a statement dependency has its statement import. Three proof
imports were omitted after the required compiler diagnosed a duplicate declaration between
the legacy `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` and current
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`. These are
`WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek`
(`prop-exc-open-adjoint`),
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.BaseChange`
(`lem-cbc-proetale-extension-zero-base-change`), and
`Sheaf.Paper.FiniteDirectImageComposition` (`lem-weil-derived-direct-image-composition`).
Their recorded legacy imports are incompatible with the statement dependencies. Their
proof steps and DAG edges remain unchanged. The statement uses the current finite-coefficient
framework through its recorded intrinsic operations, as required by the launcher
instruction for duplicate import repair. The intrinsic ordinary open adjunction is imported
from the current dependency module. The one unstated proof
node `lem-sp-proper-open-derived-support` has no declaration or module to import. It is
not needed to type this statement; it remains a named obligation in the copied proof
plan. The current server source of the newly recorded
`Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit` was also read.

Edge cases: I empty gives preservation of the initial/zero coproduct, and is included.
Infinite I and arbitrary unbounded complexes are included. Empty source, target or base
schemes are not excluded. Bound c=0 and coefficient level n=1 are included. n=0 is
excluded exactly by the source's positive-level hypothesis. Identity compactifications
and identity refinements are included by the recorded compactification category and
its datum's identity equations. There is no assumption that a FullCD bound exists for
a general proper morphism, no Noetherian or field-base restriction, and no requirement
that complexes have etale origin. All universes and variables are explicitly bound.
The shared u for schemes and the coefficient field is the recorded interface; any
finite-dimensional extension can be realized in a common enlarged universe.

Searches for an existing declaration:

- `msearch.py ... leansearch "Finite cohomological dimension proper pushforward on
  unbounded pro etale derived categories preserves arbitrary coproducts and admits a
  right adjoint"`: UNAVAILABLE, Internal Server Error; no semantic verdict inferred.
- `msearch.py ... leanfinder "A uniform finite cohomological dimension bound on a
  proper pro etale pushforward implies unbounded derived compact support preserves
  coproducts and admits a coherent right adjoint"`: eight hits, ordinary sheaf/module
  pushforward adjunctions including `SheafOfModules.instIsRightAdjointPushforward` and
  `CategoryTheory.Functor.sheafAdjunctionCocontinuous`; none states this derived conditional.
- `msearch.py ... loogle '"PreservesColimits", "rightDerived"'`: zero hits.
- `msearch.py ... grep 'FullCD|fullCohomological|AmbientExceptional|[Bb]rown[Rr]epresent'`:
  zero Mathlib hits.
- `rg` of the upstream `WeilConjectures` and project `lean/Sheaf` for the node id,
  `sfAmbientCompactSupportCandidate`, `sfFullCohomologicalDimension`, and
  `HasAmbientExceptionalRightAdjointDatum`: only the existing definitions and the
  weakly-contractible FullCD test in the project. No exact theorem.
- Read upstream `WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint`, especially
  `HasAmbientExceptionalRightAdjoint.isLeftAdjoint`: its bound is a different stronger
  predicate, its coefficients/category differ, and it states neither coproduct preservation
  nor a coherent family on all compactifications. It is not this statement.
- Read the nearby project `FiniteCohomologicalDimensionDirectImageCoproducts`: its
  theorem is for the etale site, so does not duplicate this pro-etale conditional.
- `rg` of `dag/lean_names_upstream.json` and upstream for the item id: no exact declaration.

No statement correction, new definition node, or dependency repair was necessary.
The recorded ambient interface is used intact. No STATEMENT-DISPUTED finding.

## Second reading by Q35

I reread the node statement, its source place (`sec-smooth-purity/sk-prop-sf-existence`,
clause (b)), all recorded statement dependencies, and
`lean/Sheaf/AlgebraicGeometry/FullCdAmbientAdjoint.lean` item by item.

- Prime and coefficient field: the node's prime `\ell`, finite extension `E/\mathbf Q_\ell`,
  and chosen coefficient construction are rendered by `(l : ℕ) [Fact l.Prime]`,
  `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  Verdict: exact recorded finite-extension interface; no extra field hypothesis.
- Positive level and coefficient ring: `n ≥ 1` is `(n : ℕ) (hn : 1 ≤ n)`, and the
  conclusion uses `Padic.coefficientExtensionRing l E n` with the canonical
  `Padic.finite_coefficientExtensionRing l E n hn` instance. Verdict: exact `A_{E,n}`;
  the finiteness instance is supplied by the dependency and is not an added assumption.
- Base and schemes: `S X Y : Scheme.{u}`, `[X.Over S] [Y.Over S]`, and
  `hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x)` render the scheme base and invertibility
  of `\ell`. The four instances `[LocallyOfFiniteType]` and `[QuasiCompact]` on the two
  structure morphisms render finite-type S-schemes. Verdict: exact hypotheses.
- Morphism: `(f : X ⟶ Y) [f.IsOver S] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f]` renders a separated finite-type S-morphism. Verdict: exact; no
  properness of `f` is added (properness belongs to the compactification's `d.g`).
- Compactification and FullCD: `(d : Compactification f)` supplies the ambient scheme,
  open immersion, proper map, and factorization, while
  `hcd : sfFullCohomologicalDimension d.g (Padic.coefficientExtensionRing l E n) c`
  with `c : ℕ` renders the nonnegative FullCD bound. Verdict: exact; `c = 0` is included.
- Coproduct conclusion: `∀ I : Type w, PreservesColimitsOfShape (Discrete I) (...)`
  applies to every set-indexed coproduct, with arbitrary index universe and including
  the empty index type. The functor is exactly the recorded
  `sfAmbientCompactSupportCandidate` (extension by zero followed by derived direct image).
  Verdict: exact candidate and quantifier; no constructibility or boundedness restriction.
- Ambient datum conclusion: `HasAmbientExceptionalRightAdjointDatum l E n hn S X Y hS f d`
  is the recorded datum, including right adjoints and adjunctions for every
  compactification, refinement isomorphisms, unit/counit compatibility, and identity and
  cocycle equations. Verdict: exact full conclusion, not a weaker isolated right-adjoint
  assertion.

Edge cases checked: empty coproduct index, infinite index sets, empty schemes, zero
objects, `c = 0`, `n = 1`, identity compactification/refinement, and arbitrary unbounded
complexes are covered. `n = 0` is excluded exactly by the source's `n ≥ 1` condition.
The explicit universes preserve the small pro-etale site's object/morphism size convention.

Searches were reread from `searches.jsonl` and repeated with `rg` over Mathlib, the
upstream `WeilConjectures` tree, and project `lean/Sheaf`; no exact theorem or duplicate
definition was found. The semantic searches (LeanSearch, LeanFinder, and Loogle) found
only generic sheaf adjunction or continuity results, not this conditional pro-etale
FullCD theorem. The recorded declarations for compactifications, FullCD, the pro-etale
derived category, coefficient finiteness, the candidate, and the ambient datum were
opened and match their node statements.

No mismatch was found, so no Lean or node repair was made. The module was compiled with
`scompile.py` and completed without errors or warnings beyond the permitted `sorry`.
