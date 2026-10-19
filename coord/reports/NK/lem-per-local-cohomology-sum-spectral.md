## Worker report

The module `Sheaf.Algebra.Homology.LocalCohomologySumSpectral` states
`ModuleCat.idealPowerTorsion_sum_spectralSequence`, with its whole proof `sorry`.
It introduces no definitions. Only the item's `lean` record changes.

Clause correspondence:

- A commutative Noetherian ring is `{A : Type u} [CommRing A] [IsNoetherianRing A]`.
- The finitely generated ideals are `(I J : Ideal A) (_hI : I.FG) (_hJ : J.FG)`.
  These explicitly retain the hypotheses even though Noetherianity implies them.
- An arbitrary A-module M is the argument of each endofunctor of
  `ModuleCat.{u} A`. The conclusion is uniformly natural in all such M,
  rather than supplying unrelated spectral sequences one module at a time.
- `H_K^n` is exactly `(ModuleCat.idealPowerTorsion K).rightDerived n`.
  Mathlib computes these functors by injective resolutions and cohomology.
  No Ext-colimit substitute or additional acyclicity hypothesis is used.
- Existence of a cohomological first-quadrant spectral sequence starting at
  page two is `∃ E : E₂CohomologicalSpectralSequenceNat
  (ModuleCat.{u} A ⥤ ModuleCat.{u} A), ...`. Its indices are pairs of naturals;
  its page-r differential has bidegree (r, 1-r), and it includes the
  homology-to-next-page isomorphisms.
- The page-two identification is the natural isomorphism under `Nonempty` in
  `∀ p q : ℕ, Nonempty ((E.page 2).X (p,q) ≅
  (idealPowerTorsion J).rightDerived q ⋙ (idealPowerTorsion I).rightDerived p)`.
  Composition is in the required order: first H_J^q, then H_I^p.
  Because these are isomorphisms of functors, they are natural in M.
- The abutment is `E.AbutsTo (fun n : ℕ ↦
  (idealPowerTorsion (I ⊔ J)).rightDerived n)`. The supremum of ideals is their
  sum, so this is H_{I+J}^n. `AbutsTo` is `Nonempty (E.Abutment H)` and
  `Abutment` supplies subobjects F(n,p), consecutive inclusions, F(n,0)=top,
  F(n,n+1)=bottom, and isomorphisms from the cokernel of each inclusion to
  `E.pageInfinity (p,q)` whenever p+q=n. `pageInfinity` is page p+q+2.
  Thus for p=0,...,n these are exactly E_infinity^{p,n-p}, including both
  endpoints. In the functor category this is a filtration by subfunctors
  with natural graded isomorphisms; evaluation preserves kernels and
  cokernels, so evaluation at M gives precisely the node's finite module
  filtration. No convergence convention for arbitrary unbounded exact
  couples is imposed.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`: every ideal is
  finitely generated, as in `def-weil-pbc-noetherian-ring`. Also read
  `isNoetherianRing_iff_ideal_fg` and `Ideal.fg_of_isNoetherianRing`.
- `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`,
  `ModuleCat.idealPowerTorsion` and its additive instance, from
  `def-sbc-ideal-power-torsion-functor`. Its object is the actual
  `Ideal.primaryComponent M J`; its maps restrict the given linear maps.
- `Mathlib.CategoryTheory.Abelian.RightDerived`, `Functor.rightDerived`:
  injective resolution followed by the homology functor, exactly as the
  dependency's final sentence requires.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`,
  `E₂CohomologicalSpectralSequenceNat` / `SpectralSequence`, already carried
  by the Mathlib node `def-sp-spectral-sequence`.
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`,
  `SpectralSequence.AbutsTo`, `SpectralSequence.Abutment`, and
  `SpectralSequence.pageInfinity`, already carried by `sk-def-groth-ss`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory` supplies the pointwise
  abelian structure; `Mathlib.Algebra.Category.ModuleCat.Abelian` and
  `ModuleCat.EnoughInjectives` supply the module-category structures. No
  extra instances occur as hypotheses.

Source read: `literature/stacks-project/dualizing.tex`,
`lemma-local-cohomology-ss` (Tag 0BJC), and
`lemma-local-cohomology-noetherian`, part (3) (Tag 0955).
The former gives the support spectral sequence and derived support
composition; the latter identifies it with derived ideal-power torsion.
The item's node carries the five-step split proof (stage-1 split of
2026-10-19); the theorem docstring renders those five steps
(maintainer review FIX: the delivered docstring followed the earlier
0955(3)/derived-support route instead).

Edge cases checked before writing: n=0 has the single quotient F0/F1;
I=bottom makes Γ_I the identity (some positive power is zero), J=bottom
behaves analogously; I=top or J=top makes the corresponding torsion functor
zero and forces the sum-support abutment zero. The zero module and the
zero ring are included: no nonzero, domain, local, field or characteristic
hypothesis occurs. Neither M nor either ideal is required to be proper or
nonzero. The explicit universe u agrees with the dependency's module
universe; every variable and universe in the delivered signature is bound.

Searches for an existing statement:

- msearch.py LeanFinder, `natural first quadrant spectral sequence right
  derived ideal torsion for sum of ideals`: eight hits on localCohomology
  diagrams and IdealFilter torsion quotients, no spectral sequence theorem.
- msearch.py LeanSearch, `Natural convergent local cohomology spectral
  sequence for a sum of ideals`: localCohomology Ext-colimit functors,
  radical/final comparisons and unrelated ideal sums; no exact theorem.
- msearch.py Loogle, `CategoryTheory.E₂CohomologicalSpectralSequenceNat,
  ModuleCat.idealPowerTorsion`: zero hits; idealPowerTorsion is project-only.
- msearch.py grep, `localCohomology|idealPowerTorsion|pageInfinity` in
  `Algebra/Homology`: only localCohomology declarations. Read its file:
  its future-work list explicitly separates the derived-torsion comparison.
- rg of the slopmaster2 `WeilConjectures` tree and shared `lean/Sheaf` for
  `lem-per-local-cohomology-sum-spectral`,
  `idealPowerTorsion_sum_spectralSequence`, `localCohomology.*[Ss]pectral`,
  and `[Ss]pectral.*localCohomology`: no existing item declaration.
- rg for `idealPowerTorsion`, `SpectralSequence`, `AbutsTo`, `Abutment`, and
  `pageInfinity` found the reusable torsion and first-quadrant convergence
  definitions above. Read their complete signatures, fields and docstrings.
  Searches and msearch responses are also in the launcher's searches.jsonl.

No statement correction, new node, dependency repair, or
STATEMENT-DISPUTED issue is needed.

## Second reading by NK

Self-check with the node and module open: the spectral sequence is
cohomological, first quadrant, and begins at E2; the inner functor is Γ_J,
the outer functor is Γ_I, and the abutment uses the sum I sup J. The finite
filtration includes F0=Hn and F(n+1)=0 and all n+1 graded pieces. Naturality
is encoded by functor-category pages and filtration, including graded
isomorphisms, not only objectwise existence. The Noetherian and both finite
generation hypotheses remain explicit; no condition on M was introduced.
The first compile identified a missing import of ModuleCat.Abelian; this
was added without altering the statement. This is a self-reading, not an
independent reviewer attestation: the dispatcher brief prohibits starting
other agents and assigns the independent reading to the maintainer.
