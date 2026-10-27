## Worker report

Delivered module: `Sheaf.Paper.SequenceKInjectiveComparisonShifts`.
Main declaration:
`WeilConjectures.SequenceKInjectiveComparison.sequenceKInjectiveComparisonShifts`.
All declarations are in `WeilConjectures.SequenceKInjectiveComparison`.
The theorem is the only postponed proof; every helper is real data or an explicit
Prop-valued formula belonging to this comparison, rather than a new independent notion.
The item changes only in `lean`; no statement correction or dependency repair is needed.

### Hypotheses and objects

- `D : FiniteFieldDatum.{t}` fixes the prime, positive exponent, finite field and
  its algebraic closure, using `Sheaf.Paper.FiniteFieldFiber`.
- `l : ℕ`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` are the prime and the
  characteristic exclusion. `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` are precisely the finite coefficient extension.
  The valuation ring, chosen uniformizer, actual quotient coefficient sheaves,
  completion and their projections are those already used by
  `coefficientSequenceModules` and `scalarReductionSource`; none is reconstructed.
- `W : Scheme.{t}` and `aW : W ⟶ Scheme.Spec.obj (op (CommRingCat.of D.k))`, with
  `[LocallyOfFiniteType aW]` and `[QuasiCompact aW]`, say exactly finite type over k.
  Mathlib expresses finite type as these two properties, rather than a `FiniteType` class.
- `coefficientSequenceModules l E W` is the existing category of module sheaves
  on the actual ringed sequence site. `n : ℕ` in that API means exponent `n+1`.
  `coefficientSequenceDerived` and `DerivedCategory (scalarReductionSource ...)`
  are the ordinary unbounded localizations, with cochain integer shifts.
- The supplied `S : CoefficientDerivedSystemCalculus l E W` and
  `_coherence : CoefficientDerivedSystemCoherence l E W S` retain the specified
  calculus. Its already fixed total-limit functor is `coefficientSequenceLimit`.
  No further property of reduction or of normalized inputs is required here.
- Scheme universe `t` and coefficient universe `u` remain independent throughout.
  The existing categories use coefficient size `max u (t+1)` on the small pro-etale
  site, whose object and morphism universes remain distinct. No equality is imposed.

### Each assertion

1. **Projection and its factorization.** `push` is the actual ordinary direct-image
   expression `coefficientSequenceRestriction l E W ⋙ lim`. Thus it uses the
   canonical p specified by the node through its module direct image: the constant-ring
   factor `a_*` is the recorded exact U, and `g_*` is the actual inverse-limit functor.
   This does not introduce an arbitrary direct image, ring map, or projection map.
   The underlying constant/limit geometric morphism is the existing
   `RingedToposMorphismOfUniverses` / sequence-site interface, imported from
   `Sheaf.Paper.SequenceSiteCompletionProjection`; only its module direct image
   enters the derived assertion. `restrict` and `limitComplex` merely name the
   termwise functors of the two recorded factors.
2. **Rp_* and canonical kappa.** The theorem produces `RP` with its natural comparison
   `η`, asserts `RP.IsRightDerivedFunctor η (HomologicalComplex.quasiIso ... (.up ℤ))`,
   and asserts that `η.app I` is invertible on every K-injective I. These identify
   RP as Rp_* with its canonical K-injective resolution identifications, rather than
   an arbitrary functor. The `∃! κ : RP ≅ coefficientSequenceLimit l E W` clause gives
   the canonical natural isomorphism to the *existing* `D(U) ⋙ Rlim`.
   The first clause of `Normalization` fixes its universal-unit equation on every
   complex using the actual exact-localization comparison and the actual limit unit.
3. **Every j on a K-injective I.** The second clause of `Normalization` quantifies
   over every K-injective I, K-injective J and quasi-isomorphism `j : UI ⟶ J`.
   It asserts `QuasiIso (limitComplex.map j)` and
   `η_I ≫ κ_QI ≫ replacementIso(I,J,j).hom = Q.map (lim j)`.
   This is precisely the normalized representation, after applying the canonical
   K-injective model identification on the target. It never assumes UI K-injective.
4. **Every supplied v.** `replacementIso N J v` is defined, with no postponed data,
   as `Rlim.mapIso(restrictionFactors.app N)`, then `Rlim.mapIso(asIso(Q.map v))`,
   then `lim.rightDerivedFunctorObjQIso J`. Thus it has the exact specified order:
   localization comparison, Rlim[v], canonical K-injective model comparison.
   It depends only on v and uses no chosen resolution of N over B.
5. **Unique homotopy class b and its formula.** `ArbitraryReplacement` quantifies
   over every N, I, i, J, v with exactly the node's K-injectivity and quasi-isomorphism
   conditions. Its `∃! b` is in the actual homotopy category and satisfies
   `q(Ui) ≫ b = q(v)`, precisely `b Ui ≃ v`. For every chain representative β of b
   it asserts both `QuasiIso β` and `QuasiIso (lim β)`. Its equation
   `η_I ≫ inv(RP.map(Q.map i)) ≫ κ_QN ≫ replacementIso(N,J,v).hom = Q.map(lim β)`
   is the desired representative formula in the Rp_* model supplied by i.
   Universal quantification over i with one fixed `replacementIso` expresses independence
   of that resolution, including non-monomorphic replacements.
6. **All derived morphisms.** `DerivedNaturality` quantifies over an arbitrary
   `f : QN ⟶ QN'`. It asks only that t and s represent its maps on the K-injective
   targets; their existence is the already recorded K-injective Hom bijection.
   It imposes no representative chain map N → N'. `restrictedMap f` transports f
   by the fixed exact-localization comparison. The conclusion is the homotopy
   `β ≫ s ≃ U(t) ≫ β'` and the naturality equation
   `L.map f ≫ c_v' = c_v ≫ Q.map(lim s)`. Kappa is itself a natural isomorphism.
7. **Change-of-resolution cocycles.** `ResolutionCocycle` gives the identity and
   triple-comparison homotopies for arbitrary simultaneous replacements, the
   corresponding identities after limit/localization, and compatibility with c_v.
   `SystemResolutionCocycle` gives the analogous homotopies and model identities
   for the B-system resolutions after ordinary p_*. These are formulas for arbitrary
   valid comparison representatives, not chosen comparison maps.
8. **Literal shifted representatives and signs.** `RepresentativeShifts` gives the
   degree-i identity `lim(j[r]).f i = (lim j).f (i+r)`, the differential formula
   `d_(lim(J[r])) = r.negOnePow • d_(lim J)` with indices shifted by r, validity of
   the supplied shifted replacement, and the shifted comparison homotopy for `β[r]`.
   Restriction uses its standard `commShiftIso`, whose components in every degree
   are identities; it is only the necessary transport between the equal degreewise
   models. Substituting N=I and v=j includes every j in the node's first normalization.
   Uniqueness in `ArbitraryReplacement` then identifies its shifted b with b[r].
9. **Derived shifts, all inputs and maps, and coherence.** `totalLimitCommShift` is
   actual instance data from the existing exact-derived restriction and standard
   right-derived limit. `sRP` supplies RP's coherent shifts, with
   `NatTrans.CommShift η ℤ` and `NatTrans.CommShift κ.hom ℤ` fixing the compatibility
   of the canonical unit and kappa. `ReplacementShifts` explicitly equates c_(v[r])
   with c_v[r] after Q, U, lim and L's canonical shift identifications. These are
   natural transformations on the whole derived categories. `Functor.CommShift`
   includes the zero and addition laws by definition; with r+(-r)=0 it also gives
   the inverse-shift laws. Thus these are coherent integer shifts, not unrelated
   isomorphisms for each r.
10. No hypothesis asserts preservation of K-injectives by U, exactness of arbitrary
    products, boundedness, or normalized systems. The only K-injectivity assumptions
    on representatives are the supplied targets I and J.

### Dependency declarations read and used

- `Sheaf.Paper.CoefficientRingedSequenceSite`: `coefficientSequenceModules`,
  `coefficientSequenceDerived`, `coefficientSequenceRestriction`, its exactness and
  additive instances, `coefficientSequenceDerivedRestriction`,
  `coefficientConstantTowerLimit`, `coefficientSequenceLimit`, and
  `coefficientConstantTowersKInjectives`. These supply all actual categories and functors.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective`, read as the homotopy-class interface.
- `Sheaf.Paper.SequenceSiteCompletionProjection`:
  `CategoryTheory.RingedToposMorphismOfUniverses`, its independent universe binders,
  induced module direct image and normalization; this is the recorded ringed-site interface.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and `DerivedCategory.Q`; `ExactFunctor`:
  `Functor.mapDerivedCategoryFactors`.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and its field/closure instances.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `coefficientDerivedSystemEvaluationCalculus`; its right-derived comparison helper
  `coefficientRightDerivedComparison` is from `Sheaf.Paper.CoefficientHomZeroClass`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `Functor.rightDerivedFunctorObjQIso`; `...Triangulated`: the standard right-derived
  `CommShift` instance. These are reused, not duplicated.
- Proof imports, all read: `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
  (`ringedToposDerivedPushforwardComposition`), `ExactFunctorDerivedFunctor`
  (`Functor.exactFunctor_derivedFunctor`), `KInjectiveTotalDerived`
  (`exists_rightDerived_of_enough_isKInjective`),
  `RingedSiteKInjectiveResolutionsOfUniverses`
  (`SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`),
  and `KInjectiveReplacementTriangulated`
  (`HomotopyCategory.KInjectives.replacement_triangulated`).
  The small-category composition theorem can be transported to small models in its
  proof application; no equal-universe specialization is imposed on this statement.

### Sources and edge cases

Read Stacks `sites-cohomology.tex`, lemma-derived-pushforward-composition (0D6E),
and the exact K-injective Hom/computation interfaces. Read the newest blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/`:
`fix-prop-coherence.proof.md`. The historical node source names the earlier package
location; the current coefficient-comparison paragraph is in compatibility.

Checked the empty scheme and zero complexes: all recorded categories and functors
are defined and all replacement identities reduce to the unique zero-object maps.
The tower is the fixed nonempty positive-level tower, so no fictitious level zero
is introduced. Identity replacements, identity derived maps and repeated resolutions
are included. Replacements are not required to be monomorphisms. Negative r and r=0
are quantified over ℤ, and the differential is the standard signed cochain differential;
the degree shift is i+r, including when i+r is negative. No boundedness is introduced.
Independent t,u remain in the compiled theorem. No statement dispute was found.

### Searches

All wrapper searches used group Q157 and item lem-pur-sequence-kinjective-comparison-shifts.

- `msearch.py ... leanfinder "Derived direct image of quotient sequence projection equals
  derived inverse limit scalar restriction with arbitrary K-injective replacements and
  coherent shifts"`: eight hits, including `DerivedCategory.quotientCompQhIso`,
  `Functor.mapDerivedCategoryFactorsh` / `Factors`, and generic resolution naturality.
  These give ingredients, not this full normalized quotient-projection theorem.
- `msearch.py ... loogle "Functor.rightDerivedFunctor, CochainComplex.IsKInjective"`:
  zero hits with `unknown identifier Functor.rightDerivedFunctor`; this first query
  was inconclusive. Follow-up `loogle "CochainComplex.IsKInjective"` returned
  twelve hits including the definition, shift stability, and homotopy comparison facts.
- `msearch.py ... grep "rightDerivedFunctorObjQIso|mapHomologicalComplex.*[Cc]ommShift"
  Algebra/Homology`: seven Mathlib hits, notably the standard identity-component
  shift comparison for termwise additive functors. Read its full definition/formulas.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, coefficient sequence
  pushforward/comparison and right-derived composition: found general composition APIs,
  exact-second-factor comparisons and other geometric comparisons; no declaration of
  the item. The upstream composition API assumes preservation of K-injectives by its
  first factor and is not used to silently add that hypothesis here.
- Read every statement dependency's node and recorded declaration or mathlib_match,
  including signatures and docstrings, before writing. The withdrawn CompactObject
  example currently has no declarations; module header conventions follow the active
  statement modules instead.

### Validation

`scompile.py Q157 lem-pur-sequence-kinjective-comparison-shifts <module>` passed both
sandbox and library module compilation without errors or warnings (24.3 s / 23.5 s).
No #check commands remain. All 16 owned declarations are listed in `lean.declarations`.
All lines are at most 100 characters. Only the main theorem has `sorry`.
No live files, launcher scripts, or repository Git state were edited directly.

## Second reading by Q157

This is a separate reread by the dispatched worker, not a claim of an independent
second agent: the dispatcher explicitly forbids starting agents and specifies the
maintainer's independent delivery review. I reread the node and the complete module
side by side. In particular I checked the order of all three factors of c_v, the
orientation `η_I ≫ (RP[ i ])⁻¹` in the Rp_* model, the homotopy-class rather than
chain-map uniqueness, arbitrary derived f in the naturality square, both cocycle
families, the i+r indexing and signed differentials, and compatibility of c_v with
all shifts. Earlier compiler probes exposed only newline-dot syntax, the absence of
a bundled `FiniteType` class, and the need to expose the existing composite shift
instance; these were repaired without changing the mathematical assertion. The final
statement includes all the node's hypotheses and clauses as mapped above. There are
no extra missing notions, dependency modules, statement corrections, or new nodes.
