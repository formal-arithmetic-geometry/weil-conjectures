## Worker report

The module `Sheaf.TraceFormula.FrobeniusCompactPowerExchange` states
`WeilConjectures.FrobeniusCompactPower.frobenius_compact_power_exchange`, with a
single postponed theorem and its four-step natural-language proof. Its helpers are
specializations or composites of the published canonical constructions, with real data.
No dependency interface was replaced and no mathematical statement was corrected.
The previous worker's superseded-assignment message concerned the now-completed
stage-1 split; the live node is split, has no Lean record, and is queued for stage 2.
The original sandbox was empty.

Hypotheses and objects, matched in the namespace `WeilConjectures.FrobeniusCompactPower`:

- The global p,a,q,k₀,k datum, primality, positive a, cardinality q=p^a and algebraic
  closure are fields and instances of `D : FiniteFieldDatum.{u}`.
- The prime l is `(l : ℕ) [Fact l.Prime]`; `_hl : l ≠ D.p` retains the exact
  distinct-prime assumption. `E : Type u` has `Field E`, `Algebra ℚ_[l] E`, and
  `FiniteDimensional ℚ_[l] E`. The positive level is `(n : ℕ) (hn : 1 ≤ n)`.
  The coefficient ring throughout is literally `Padic.coefficientExtensionRing l E n`;
  it uses the recorded valuation ring and chosen uniformizer. Finiteness is supplied
  by `Padic.finite_coefficientExtensionRing l E n hn`, never assumed additionally.
- `X₀ : Over (Spec (.of D.k₀))` with `LocallyOfFiniteType X₀.hom`,
  `QuasiCompact X₀.hom`, and `IsSeparated X₀.hom` says exactly separated finite type.
  `c₀ : Compactification X₀.hom` retains the single open/proper factorization.
  `middle` is the existing middle model; `model` is the published geometric
  compactification, whose target is Spec k itself. These constructions preserve the
  chosen compactification for every r, rather than selecting one anew.
- `sourcePower`, `middlePower`, and `basePower` are powers in the category of schemes
  of the geometric Galois Frobenius maps and Spec of inverse field Frobenius. No
  binder requires these horizontal maps to be over k.
- `sourcePullback`, `middlePullback`, `basePullback` are exactly P_r,B_r,Q_r,
  using `proEtaleConstantRingDerivedPullback` on the ordinary unbounded intrinsic
  constant-module derived categories. `openExtension` is J, `properImage` is R,
  and `compactImage` is F=RJ. Lean functor composition writes the applied-first
  functor first, so `J ⋙ R` is the paper's RJ.
- `powerComposition A f m` is the inverse of the published canonical
  composite-to-iterated pullback comparison, followed by the equality of scheme
  powers `pow_succ`. At the source, middle, and base Frobenii it is c_m,d_m,t_m.
  End multiplication reverses diagrammatic composition, so f^m*f is f followed by
  f^m. No independent composition comparison is selected.
- `properExchange` is the published `finiteTensorExchange` on the actual proper
  square at power r, using its geometric semilinearity identity. `openExchange`
  is literally `constantOpenSquareExchange` on the geometric Cartesian square;
  its identity-on-the-open normalization comes from that definition. `compactExchange`
  is literally whiskering u_r by J followed by whiskering v_r by R, so it is e_r.
- `proper_pasting` quantifies over every m≥1 and every ambient K on W. In Lean's
  diagrammatic order it reads `t_m.app (R K) ≫ u_(m+1).app K =
  Q_1.map (u_m.app K) ≫ u_1.app (B_m K) ≫ R.map (d_m.app K)`, exactly the
  hypothesis in the node. It imposes no constructibility condition on K.

Conclusions, clause by clause:

- The first conjunct quantifies over r≥1 and gives `sourcePower r ≫ j = j ≫
  middlePower r` and `IsPullback (sourcePower r) j j (middlePower r)`.
  The pullback square has the specified two maps (g^r,j); its unique comparison
  to the canonical fibre product is their lift. Thus it is the stated Cartesian
  square with that pair, with no independently chosen identification.
- The second conjunct quantifies over r≥1 and every ambient M, and sends the
  recorded predicate `intrinsicFiniteTorsionConstructible ... M` to that same
  predicate on `sourcePullback r` applied to M. This is precisely preservation
  of D^b_c(X,A), with no restriction on the ambient intermediate objects.
- The final conjunct quantifies over m≥1 and M in that predicate's FullSubcategory.
  The first equality is `d_m.app (J M) ≫ v_(m+1).app M =
  B_1.map (v_m.app M) ≫ v_1.app (P_m M) ≫ J.map (c_m.app M)`.
  The second equality is `t_m.app (F M) ≫ e_(m+1).app M =
  Q_1.map (e_m.app M) ≫ e_1.app (P_m M) ≫ F.map (c_m.app M)`.
  These are the two displayed node equations in Lean's diagrammatic order.
  `openExchange` is a natural isomorphism and `compactExchange` is a natural
  transformation on the entire ambient categories; their components in these
  equalities therefore retain naturality for all maps of the full subcategory.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.geometricFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the recorded quotient ring.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `FiniteFieldDatum.geometricGaloisFrobenius`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingDerivedPullback`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`: the full general canonical
  comparison and its constant specialization, with
  `Scheme.proEtaleConstantRingPullbackComposition` from its public imports.
- `Sheaf.Paper.FrobeniusGeometricExchange`: the published finite recipes via
  `WeilConjectures.FrobeniusExchange.finiteTensorExchange`; the compact composite
  is the exact item-(2) recipe, with the same proper and open factors.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and `category`; the same
  `Compactification` data give the fixed open/proper factorization.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero`; its exact derived functor is the publicly
  imported `Scheme.sfIntrinsicDerivedOpen`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible` and its full subcategory.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`:
  `Scheme.constantOpenSquareExchange` with its unit-normalized transport.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`; the geometry is expressed by the
  equivalent `IsPullback` property with the explicitly specified pair of arrows.
- `def-weil-scheme-morphism-properties` is a convention node: its own record
  directs callers to `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`,
  `IsOpenImmersion` and `IsProper`; those are used here.
- Added existing landed statement dependency `def-weil-frobenius-cohomology-transport`
  to reuse `Sheaf.SixFunctors.FrobeniusCohomologyTransport` declarations
  `frobeniusCohomologyModelMap` and `frobeniusCohomologyCompactification`, which
  provide the already constructed compactification with literal target Spec k.
  This adds no hypothesis or new notion and avoids duplicating that construction.
- Proof-only imports are the recorded modules `Sheaf.AlgebraicGeometry.FrobeniusOpenSquare`,
  `Sheaf.SixFunctors.FrobeniusSquareCartesian`, and
  `Sheaf.Paper.IsomorphismDerivedPullback`.

Sources opened: Stacks `etale-cohomology.tex`, label `lemma-shriek-base-change`,
Tag 03S6; current blueprint `lem-trf-open-square-exchange.proof.md` and
`lem-trf-frobenius-operator-compact-description.proof.md`. The former proves the
normalization and pasting by the sectionwise localization equality and uniqueness
of adjoints, explicitly without geometric-stalk conservativity. The latter supplies
the compact-support iterate context. The item's source labels its conditional
assembly as an agent refinement, so no unconditional proper-pasting claim is made.

Edge cases checked: empty X₀ and empty open immersion are allowed, and the middle
compactification need not be dense. Zero complexes are allowed. n=1, r=1 and m=1
are included. n=0 is excluded exactly by hn, and r=0/m=0 are not asserted by the
node. The helper maps are nevertheless defined at zero as honest identity powers.
All maps live on scheme endomorphisms; no k-linearity assumption enters. The site
and module universes are unchanged from the published operations; no site-universe
identification is added. No algebraic closure of the coefficient field or embedding
of E in one is required by this item's finite-level statement.

Searches for an existing whole statement:

- msearch.py leanfinder, query `Frobenius powers pullback extension by zero proper
  compact support exchange composition pasting`: eight hits, chiefly compactly
  supported continuous maps plus `SheafOfModules.pullbackComp`; none is the
  finite pro-etale compact Frobenius power-pasting statement.
- msearch.py leansearch, query `Composition of proper pushforward base change exchange
  and extension by zero exchange for Frobenius powers`: eight hits, including
  module pushforward composition, exponentiable morphisms, and ring Frobenius
  naturality; none states this pro-etale derived compact power-pasting theorem.
- msearch.py loogle, query `"constantOpenSquareExchange"`: zero hits.
- msearch.py grep, query `frobenius.*[Pp]ower.*[Ee]xchange|compact.*[Pp]asting`,
  Mathlib CategoryTheory: zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id and candidate
  declaration names found no match. The broader Frobenius-power search found
  `CompactFrobeniusTransportComposition`, the downstream cohomology transport
  statement, not this standalone conditional exchange theorem. Its helpers were
  inspected but not imported; the direct published operation recipes are used.

Validation: scompile.py compiles the single delivered module in module mode against
published live artifacts. The initial pass found only a def-Prop lint on an alias of
an existing geometric proof; that redundant alias was removed and the theorem is
now referenced directly. The final compile and deliver2.py dry-run results are
recorded below. Every theorem in this delivery has proof `by sorry`; all helper data
are explicit.

Final standalone scompile.py: clean in both sandbox and library module modes
(12.6 s and 9.8 s respectively), with no warning.

deliver2.py --no-push: OK; server preflight and per-file compilation passed.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
