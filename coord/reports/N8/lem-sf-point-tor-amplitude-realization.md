## Worker report

The delivery states `WeilConjectures.point_tor_amplitude_realization` in
`Sheaf.Paper.PointTorAmplitudeRealization`. Its sole theorem has proof `sorry`;
there are no new definitions or other postponed theorems. The statement and proof
of the natural-language node are unchanged. I add the already landed
`def-sc-module-total-hom-complex` to statement dependencies because the conclusion
uses its signed, module-valued Hom complex. No independent notion is introduced.
The earlier Q74 delivery was stage 1, not a Lean statement: the current node has
`status: split`, Q74's split review, and no `lean` record.

Hypotheses and clauses correspond as follows.

- The global finite-field datum is `F : FiniteFieldDatum.{u}`. Its closure is `F.k`,
  and the point is `Spec (.of F.k)`. The coefficient prime is `l` with
  `[Fact l.Prime]` and `hl : l ≠ F.p`.
- A finite extension is `E : Type u` with `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`. The coefficient ring is the existing
  `Padic.coefficientExtensionRing l E n`, with `(n : ℕ) (hn : 1 ≤ n)`. Its definition
  uses the recorded integer ring, chosen uniformizer, and power quotient; these are
  not replaced by an arbitrary finite local ring.
- The ordered interval is `(a b : ℤ) (_hab : a ≤ b)`. The node's endpoints u,v are
  renamed a,b to reserve u for the explicit universe variable.
- `N` belongs to the full subcategory of
  `intrinsicFiniteTorsionConstructible l E n hn (Spec (.of F.k))`. This is intrinsic
  bounded constructibility, with no extra finite-Tor assumption built into membership.
  The given interval is imposed separately by `_hTor : HasProEtaleTorAmplitude ...
  N.obj a b`, which tests every module sheaf, including infinite nonflat ones.
- `C = ((pointFiniteFibre F l hl E n hn).obj N).obj` specifies exactly the recorded
  ordinary module fibre. Quantification over C followed by this equality is an
  equality-bound name for the source's `C = Fib_s N`: it imposes no new restriction
  on N, and the theorem applies to the actual fibre by reflexivity. No alternative
  fibre, arbitrary map, or equivalence of the full pro-etale topos with modules is used.
- `pointFiniteCohomology ... C` gives finite cohomology in every degree and finite
  cohomological support. `torAmplitudeIn (ModuleCat ... ) a b C` is the ordinary
  derived tensor condition: for EVERY object M of ModuleCat, tensor with its
  degree-zero single complex has cohomology zero outside [a,b]. M has no finite,
  flat, projective, or finite-Tor hypothesis.
- `∃ P : CochainComplex ... ℤ` gives an actual cochain complex. The support clause is
  `∀ i, i < a ∨ b < i → IsZero (P.X i)`; finite free terms are
  `∀ i, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)`; the model comparison is
  `Nonempty (C ≅ DerivedCategory.Q.obj P)`. Rank zero is allowed.
- The equality-bound `A₀` is precisely `(CochainComplex.singleFunctor _ 0).obj
  (ModuleCat.of A A)`, the actual A-module A in degree zero. Its derived image is
  the target of `(ihom C).obj (DerivedCategory.Q.obj A₀)`, namely RHom_A(C,A).
  Here `ihom` is the existing closed structure on the ordinary module derived
  category induced by K-flat tensor and K-injective internal Hom. It is the
  ordinary-module presentation of the ringed-site derived Hom on the one-object
  site, not Hom on the entire pro-etale point topos. The recorded dependency
  `derivedInternalHomOfUniverses` supplies the general ringed-site construction;
  no second derived Hom functor is defined. The existing proof dependency
  `projective_hom_evaluation_model` already uses this same ordinary-module `ihom`
  and compares it to the same moduleHomComplex used here.
- The dual-model clause is the isomorphism from this derived internal Hom to
  `Q.obj (CochainComplex.moduleHomComplex P A₀)`. The witness `α i` is a linear
  equivalence from its degree-i term to `P.X (-i) →ₗ[A] A₀.X 0`, where A₀.X 0
  is canonically A. Its equation `α i f = (f.v (-i) 0 (neg_add_cancel i)).hom`
  fixes the actual surviving Hom coordinate, rather than an unrelated isomorphism.
  Its differential equation is exactly
  `α (i+1) (d f) = (i+1).negOnePow • (α i f).comp (P.d (-(i+1)) (-i)).hom`.
  This renders the signed Hom differential (-1)^(i+1) f composed with d_P.
- The two `IsPerfectRingComplex` conjuncts assert perfectness of C and its derived
  dual using the recorded bounded finite-projective predicate. The final
  `pointFiniteCohomology` and `torAmplitudeIn ... (-b) (-a)` give the dual's finite
  cohomology and the EXACT reversed Tor interval.

All ordinary modules here use `ULift.{u+1,u} (coefficientExtensionRing ...)`, exactly
as the recorded pointFiniteFibre target does. ULift is the canonical ring equivalence
with inverse down, preserving actions, tensor, Hom, freeness, finite generation and
finiteness. It changes the size presentation of A, not its mathematical ring. The
site object and morphism universes remain those of the recorded small pro-etale
site; no extra equality between those universes is imposed. The theorem has
`autoImplicit false` and an explicit universe u.

Statement dependencies read and reused:

- `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, importing the full coefficient-extension
  definitions (`coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionRing`).
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`, retaining the pro-etale
  `WeilConjectures.finiteTorConstructible` interface; its imported
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude` provides the specified interval
  predicate `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude`.
- `Sheaf.Paper.FiniteCoefficientPoint`, `WeilConjectures.pointFiniteFibre`, whose
  source and full signature fix the section functor, target, and coefficient lift.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `Q`, and the
  existing derived cohomology functors.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
  `DerivedCategory.IsPerfectRingComplex`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses`, with its K-injective construction,
  comparison and representative-independence signatures. Its ordinary-module
  derived closed presentation is used as explained above.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`,
  `CochainComplex.moduleHomComplex`; this is the existing node
  `def-sc-module-total-hom-complex` added to statement dependencies.

Every already stated proof dependency has its recorded module imported privately.
`lem-weil-valued-dvr-finite-quotients` has no Lean record and is not imported; its
ordinary-language role is retained in the complete proof docstring. No import of
an unstated dependency is fabricated. All five stages of the reviewed proof are
included: quotient finiteness/locality and section finiteness, arbitrary-module
Tor transfer, an initial bounded free model followed by exact-interval truncation,
projective signed Hom computation, and reversed dual Tor bounds and finiteness.

Edge cases checked mathematically before writing: N=0 (the zero model and empty
bases work); a=b (a single-degree model, with dual at -a); negative and mixed
endpoints (the index reversal and differential are still correct); n=1 (a field
quotient); n>1 with a residue module of infinite projective dimension (excluded by
the Tor hypothesis, not mistakenly declared perfect); arbitrary infinite and
nonflat test modules (both Tor conditions retain them). n=0 is explicitly excluded
by hn, as in the source. The coefficient prime equal to F.p is excluded by hl.

Searches actually run with msearch.py N8 lem-sf-point-tor-amplitude-realization:

- LeanFinder: “A constructible complex on a pro etale algebraically closed point
  with Tor amplitude u v has sections represented by finite free modules in degrees
  u v and its dual has amplitude minus v minus u”: 8 hits, including
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, derived projective source
  vanishing, and unrelated etale-locus results. No match to all clauses.
- Loogle: `DerivedCategory, "projective"`: 4 hits, projective-source vanishing,
  K-projective localization bijectivity, and projective-resolution Ext maps.
  None gives the point realization, interval-preserving finite-free model or dual.
- Mathlib grep: `torAmplitude|finiteTorAmplitude|finite.*free.*complex`: no hits.
- LeanSearch: “A perfect complex over a local ring with Tor amplitude a b has a
  finite free representative supported in those degrees and its derived dual has
  Tor amplitude minus b minus a”: 8 hits, including bounded arbitrary-term models,
  local freeness of finite flat modules, and finite-free reflexivity. I opened
  Mathlib DerivedCategory/TStructure.lean:180 and LocalRing/Module.lean:304;
  the former has no finite/projective terms, and the latter concerns one module.
- Source/project ripgrep for the exact node id: no upstream declaration. Concept
  searches for point Tor/amplitude in lean/WeilConjectures and lean/Sheaf locate
  the recorded point tensor model and point perfectness statements. I read
  WeilConjectures/EtaleCohomology/PoincareDuality/PointPerfect.lean and the generic
  DerivedCategory/TorAmplitude.lean: neither states this exact quantitative point
  realization and its signed model. ModuleHomComplex.lean does supply the existing
  signed complex, which is reused. No duplicate definition is needed.

No statement correction, new nodes, dependency-module repair or disputed statement.
Validation: the module compiled cleanly through scompile.py before adding proof
imports; the final full import set is compiled again, and the delivery dry run is
run before pushing. Only the expected sorry proof is postponed.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
