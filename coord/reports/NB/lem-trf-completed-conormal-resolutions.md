## Worker report

The delivery states `AlgebraicGeometry.completedConormalResolutions` in
`Sheaf.TraceFormula.CompletedConormalResolutions`. Its only postponed proof is this named
theorem. The node's statement, dependencies and proof are unchanged. There are no new nodes
or dependency repairs. The helper `IsCompletedConormalSheafResolution` is a fully written
predicate spelling out this node's sheafified two-term augmentation assertion, not an
existence assumption or a replacement definition of a conormal module.

For the correspondence below, A denotes `Localization.AtPrime p`, R denotes
`Algebra.LocalCompletion A`, N denotes `KaehlerDifferential k A`, and M denotes
`Algebra.CompletedDifferentials k A = R ⊗[A] N`. These are explanatory names only;
the theorem has no local notation or hidden let binders. The shared Mathlib convention puts
the extending ring first. Tensor symmetry identifies this with the node's N ⊗_A R.

Hypotheses, individually:

- A perfect field k is `[Field k] [PerfectField k]`. Reduced finite-type S is
  `[CommRing S] [Algebra k S] [Algebra.FiniteType k S] [_root_.IsReduced S]`.
  `RingHom.finiteType_algebraMap` identifies this typeclass with the dependency's
  `(algebraMap k S).FiniteType` predicate; it is the same finite-type hypothesis.
- The nonnegative dimension is `d : ℕ`; pure dimension is
  `hpure : (Spec (.of S)).IsPureDimension d`. The local complete intersection condition
  is precisely `hlci : Algebra.IsLocalCompleteIntersection k S`.
- The chosen maximal ideal is `p : Ideal S` with `[p.IsMaximal]`. Residue field k is
  `hresidue : Nonempty ((S ⧸ p) ≃ₐ[k] k)`, equivalently the residue field of the localization
  since p is maximal. A is literally the prime localization, and R literally the completion
  at `IsLocalRing.maximalIdeal A`. Reducedness of R is an explicit `_root_.IsReduced` instance.
- `P : Algebra.Extension.{u} k A` retains the actual surjection P.Ring → A, its kernel
  `P.ker`, and Mathlib's quotient conormal module `P.Cotangent`. In particular it does not
  replace I/I² by a free module. The extension API's set-theoretic section is its standard
  surjectivity encoding; no property of this section is assumed in this theorem.
- `m`, `q : Ideal (MvPolynomial (Fin m) k)`, `[q.IsMaximal]`, `hq`, the polynomial-algebra
  instance on P.Ring, its scalar tower, and `[IsLocalization.AtPrime P.Ring q]` say exactly
  P.Ring = k[u₁,…,u_m]_q at a k-rational maximal ideal, without choosing a different action
  of k. This formulation permits any representative of the localization.
- `hdm : d ≤ m`, `h : Fin (m-d) → P.Ring`, `hh : Sequence.IsRegular … (List.ofFn h)`,
  and `hI : P.ker = Ideal.span (Set.range h)` give exactly the specified regular equations.
  The inequality expresses that the displayed number m-d is an ordinary nonnegative
  codimension, as it is in the source's regular local presentation.
- `n c : ℕ`, `hcd : c + d = n`, and the k-algebra map π give the formal presentation and
  its dimension equation. `hπ`, `hlocal`, and `hcontinuous` express surjectivity, locality,
  and continuity for the power-series topology over discrete k and the extended maximal
  ideal's adic topology on R. There is no restriction n ≥ 2.
- `g : Fin c → MvPowerSeries (Fin n) k`, `hg`, `hgin`, and `hJ` say the kernel is generated
  by the given regular sequence and every relation lies in the variable ideal.
- The only derived-category binder is the shared
  `HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))`.
  This chooses localization morphism size; it adds no geometric hypothesis. All base
  rings and schemes use one ambient universe u, as in the shared affine tilde functor.
  The testing field L has an independent universe v, and derived morphisms an independent w.

Conclusions, individually:

- The first three conjuncts are `IsNoetherianRing S`, `IsNoetherianRing A`, and
  `IsNoetherianRing R`. The next two are `(algebraMap A R).Flat` and surjectivity of
  `PrimeSpectrum.comap (algebraMap A R)`. Together these are exactly the specified meaning
  of faithful flatness, including the spectrum clause.
- `Module.Finite A N` gives finiteness of N. The following `Submodule.span … = ⊤` uses
  exactly the differentials of the images of the localized polynomial coordinates.
- The existential D is a `Derivation k R M`. The recorded
  `Algebra.IsCompletedDifferentialExtension k A D` is used verbatim; it asserts both
  extension of a ↦ 1 ⊗ da and the ideal-power continuity criterion. The following
  universal implication `… D' → D' = D` gives uniqueness independently of either row.
- The algebraic left arrow is `LinearMap.baseChange R P.cotangentComplex`; its source is
  R ⊗_A (I/I²), and its target is R ⊗_A (A ⊗_P Ω[P/k]). Mathlib's
  `Extension.cotangentComplex_mk` sends [h] to 1 ⊗ dh, so this is the node's specified d.
  The augmentation is `LinearMap.baseChange R P.toKaehler`, the canonical quotient
  differential map, not an arbitrary map onto an isomorphic module. Its coordinate
  formula is also written explicitly in the theorem: du_i maps to d(ubar_i) ⊗ 1,
  in the common reversed tensor convention.
- The formal module J/J² is literally
  `(Algebra.Extension.ofSurjective π hπ).Cotangent`. The existential δ is constrained
  on EVERY `z` of its kernel, not merely on the chosen generators: its i-th coordinate
  is π(pderiv k i z.val). The existential qT is constrained on EVERY coordinate basis
  vector by `qT (Pi.single i 1) = D (π (MvPowerSeries.X i))`. These characterizations
  specify the actual canonical arrows; surjectivity and bases are conclusions.
- Each row has all three short-exact clauses, separately: `Function.Injective`,
  `Function.Exact`, and `Function.Surjective` for precisely those arrows.
- The next four existential `Module.Basis` clauses have index types Fin (m-d), Fin m,
  Fin c and Fin n. Their basis-vector equalities identify the algebraic equation
  classes tensored with 1, the localized coordinate differentials tensored with 1,
  the formal equation classes, and `Pi.single i 1`, respectively. Finite index types
  provide both finiteness and freeness with the asserted ranks, including rank zero.
- `IsCompletedConormalSheafResolution` is asserted for each specified row. Open its
  definition: C is a cochain complex in the shared O_(Spec R)-module category, zero
  off -1 and 0; eNeg and e₀ identify these terms with the tildes of the actual modules;
  the differential is the tilde of the actual arrow. Its chain augmentation ε has
  its degree-zero component equal to tilde(q) under e₀ and the canonical single-term
  identification. `QuasiIso ε` and `IsIso (DerivedCategory.Q.map ε)` assert both the
  quasi-isomorphism and invertibility of this very augmentation in D(O_(Spec R)).
  The chain-map condition and concentration also determine its other components.
- Finally the theorem quantifies over ANY field L in universe v and any R-algebra
  structure compatible with its k-algebra and A-algebra structures. These scalar
  towers encode a k-algebra map R → L and its restriction, not flatness. The antecedent
  identifies the kernel of A → L with a minimal prime a of A and requires its point
  over Spec S to lie in an open with `SmoothOfRelativeDimension d` over k. This is the
  stated generic point in the smooth d-dimensional locus. Both tensor rows again
  have injectivity, middle exactness, and surjectivity. Their augmentations are
  explicitly composed with Mathlib's canonical `AlgebraTensorModule.cancelBaseChange`
  so their LITERALLY COMMON target is L ⊗_A N, not an unspecified isomorphic cokernel.
  `FiniteDimensional L (L ⊗[A] N)` and `Module.finrank L … = d` give its dimension d.
  No instance or hypothesis asserts flatness of R → L.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`,
  `RingHom.finiteType_algebraMap`, and `Algebra.FiniteType.isNoetherianRing`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection` and `Algebra.IsLocalCompleteIntersection`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and
  `IsLocalization.AtPrime`; residue quotients are read together with the node's
  `Ideal.ResidueField` record. `Mathlib.RingTheory.AdicCompletion.Basic`:
  `AdicCompletion`, used through `Algebra.LocalCompletion` from
  `Sheaf.RingTheory.FormalLocalPresentation` (publicly imported by the comparison module).
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
  `Mathlib.RingTheory.MvPowerSeries.Basic` and `.Derivative`: `MvPowerSeries`,
  `MvPowerSeries.X`, `MvPowerSeries.pderiv` (the derivative dependency is a Mathlib leaf).
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `.D`, `.mapBaseChange`,
  `.kerCotangentToTensor`, `.exact_kerCotangentToTensor_mapBaseChange`.
  `Mathlib.RingTheory.Extension.Cotangent.Basic`: `Algebra.Extension.Cotangent`,
  `.cotangentComplex`, `.CotangentSpace`, `.toKaehler`, using the actual quotient extension.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`, `LinearMap.baseChange`,
  `AlgebraTensorModule.cancelBaseChange`; `.RightExactness`: tensor exactness.
- `Sheaf.RingTheory.CompletionKaehlerDifferentialComparison`:
  `Algebra.IsCompletedDifferentialExtension` and its completion comparison theorem;
  `Sheaf.RingTheory.CompletedJacobianPresentation`: `Algebra.CompletedDifferentials`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`, the
  shared category carrier and `HasDerivedCategory` convention; Mathlib
  `DerivedCategory.Q`, `QuasiIso`, `CochainComplex.singleFunctor` are used directly.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`.
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`;
  `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, realized here by specified
  `Module.Basis` witnesses.
- The stated proof modules are imported privately: completion Noetherianity, regular
  sequence conormal freeness, reduced Noetherian total fractions, tilde finite limits,
  and completed Jacobian differentials. The Mathlib proof leaves are also imported.
  `lem-trf-generic-completed-differential-rank` has no Lean record in the read DAG,
  so there is no module to import for that proof-only dependency; it is retained in
  the node and the complete proof docstring. No duplicate assertion of it is introduced.

Sources opened: the node's seven-step proof; Algebra 00LN
`lemma-regular-quasi-regular`, 00RX `lemma-differentials-polynomial-ring`, 00RT
`lemma-differentials-localize`, 00RU `lemma-differential-seq`, 00MC
`lemma-completion-faithfully-flat`, and 02LX
`lemma-total-ring-fractions-no-embedded-points` in the local Stacks source.
The existing completion, Jacobian and determinant-comparison modules were read for the
continuous topology and map conventions. The latest blueprint ancestor proof
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`
was read; this delivery does not change its statement or route.

Edge cases checked before writing and on rereading:

- d=0 and m=d: Fin 0 allows the empty algebraic relation basis. c=0 is also allowed.
  n=0 forces c=d=0 through c+d=n, and the zero-variable power series ring is k.
  There is no dummy-variable bound inherited from `FormalLocalPresentation`.
- The zero ring S has no maximal ideal, so the local situation cannot arise from it;
  no extra nonzero hypothesis is imposed. Empty components in pure dimension keep
  their shared definition. Empty regular sequences retain the usual nonzero quotient
  condition from `Sequence.IsRegular`.
- For a smooth local chart with no equations both rows are the expected free
  differential module in degree zero. For the node xy=0, the relation differential
  is (y,x), which is injective over the reduced ring though neither coordinate is
  a nonzerodivisor; the proof uses generic fields and both coordinates, not either alone.
- Dropping reducedness would fail: in k[x]/(x²), multiplication by the derivative
  2x has nontrivial kernel (and is zero in characteristic 2). The stated reducedness
  hypotheses are retained, with no restriction on characteristic added.
- Generic field maps need not be flat; all six exactness clauses are conclusions.
  FiniteDimensional accompanies finrank, so d=0 cannot accidentally describe an
  infinite-dimensional vector space through Mathlib's finrank convention.
- No statement correction or STATEMENT-DISPUTED flag was needed.

Searches actually run for this delivery:

1. `msearch.py … leanfinder "Algebraic and formal conormal complexes resolve completed
   Kahler differentials over a reduced completion"`: eight hits, including
   `Algebra.Extension.exact_cotangentComplex_toKaehler` and formally smooth conormal
   criteria. They provide the algebraic row, not the completed two-presentation
   theorem with continuous maps, bases, sheaf resolutions and generic fibres.
2. `msearch.py … loogle "KaehlerDifferential.kerCotangentToTensor"`: seven hits,
   including the conormal arrow, its formula on classes, exactness and smoothness
   criteria. Used the existing extension interface; no theorem matching the item.
3. `msearch.py … grep "completedConormal|conormal.*completion|completion.*conormal"
   RingTheory/`: zero Mathlib hits.
4. `rg -n 'lem-trf-completed-conormal-resolutions|completedConormal|conormal.*completion'
   lean/WeilConjectures lean/Sheaf`: no statement of this node. The downstream
   `Sheaf.TraceFormula.CompletedConormalDeterminantComparison` has related data,
   but its theorem assumes a canonical adjunction system and concludes determinant
   comparison, not this lemma. Importing that consumer would also obstruct the
   required bottom-up dependency direction. Its definitions are not copied here.
5. Direct Mathlib searches/readings located `Algebra.Extension`, its actual conormal
   and canonical differential arrows, affine tilde, `QuasiIso`, and the single-complex
   identifications used by the helper. No independent new mathematical notion was needed.

Validation: all compiles use the prescribed scompile.py wrapper. The first draft had a
parser error at a subscript-minus identifier; it was renamed `eNeg`. Subsequent server
compiles succeeded in 4.6 and 5.4 seconds. The wrapper reported local temporary-storage
exhaustion and automatically used its current-server-source fallback successfully.
The exact final file and delivery preflight are checked again by deliver2.py.

## Delivery reread

I reread the final signature and helper against the node. This is a worker self-check;
the maintainer supplies the independent review. The reread made the polynomial
augmentation's coordinate formula explicit and added finite dimensionality alongside
finrank. It also composed both specialized augmentations with the same canonical
base-change cancellation, making N ⊗_A L their exact common codomain. The statement
retains the four equation/coordinate bases, both genuine conormal modules, continuity
and uniqueness independently of the exact rows, and the degree-zero component of
both derived augmentations. No hypotheses or conclusions from the determinant
comparison were substituted for this lemma.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
