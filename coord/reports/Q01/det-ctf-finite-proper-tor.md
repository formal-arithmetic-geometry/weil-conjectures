## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude` states
`AlgebraicGeometry.Etale.isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper`.
Its only proof is `by sorry`, as required for stage 2. The node changes only in `lean`.
The source read was the current main-20261015 blueprint's
`sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-tor.md`.
The resolved stage-1 repair note was read: it requested proof-route splitting while
keeping this statement unchanged. The docstring follows the current five-step node proof.

Hypothesis and clause correspondence:

- The prime ℓ is `(ℓ : ℕ) (hℓ : ℓ.Prime)`.
- Characteristic p > 0, unequal to ℓ, is `(p : ℕ) (hp : 0 < p)
  (hpℓ : p ≠ ℓ) (k : Type u) [Field k] [CharP k p]`.
- Schemes X and Y in the standing scheme setting are `{X Y : Scheme.{u}}`
  with `[X.Over (Spec (.of k))]` and `[Y.Over (Spec (.of k))]`.
  Their structure morphisms have `IsSeparated`, `LocallyOfFiniteType` and
  `QuasiCompact` instances. The last two together mean finite type.
- The proper k-morphism p_X is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [IsProper f]`.
- A finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A]
  [Finite A]`, the project's ordinary constant-coefficient module-sheaf encoding.
- ℓ^r A = 0 for some r ≥ 1 is
  `hA : ∃ r : ℕ, 1 ≤ r ∧ (ℓ ^ r : ℕ) • (1 : A) = 0`.
  Killing the unit is equivalent to killing every element by distributivity.
- A uniform nonnegative integer bound is `(d : ℕ)`; its image in integer
  cohomological degrees and interval endpoints is explicitly `(d : ℤ)`.
- Every geometric point is quantified in `hd` as `(Ω : Type u) [Field Ω]
  [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)`. The geometric fibre is the
  scheme-theoretic `pullback f y`, with its own `smallEtaleTopology`.
- Every abelian sheaf on this fibre is
  `F : Sheaf (pullback f y).smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The parenthetical definition of ℓ-power torsion is unpacked literally:
  `∀ (U : (pullback f y).Etale) (s : F.obj.obj (op U)),
  ∃ n : ℕ, (ℓ ^ n) • s = 0`. The exponent can depend on both the object
  and the section. There is no fixed-exponent or constructibility requirement on F.
- Vanishing of H^i for every i > d is `∀ i : ℤ, (d : ℤ) < i → IsZero ...`,
  using `cohomology AddCommGrpCat.{u + 1} (pullback f y) i` applied to
  `(_root_.DerivedCategory.singleFunctor _ 0).obj F`.
- Integers a ≤ b are `(a b : ℤ) (hab : a ≤ b)`.
- C belongs to the ordinary derived category by `C : DerivedCategoryModule A X`.
  Its membership in Dctf and its specified Tor interval are rendered together by
  `hC : DerivedCategory.isBoundedConstructible A X C` and
  `hCab : DerivedCategory.hasTorAmplitudeIn A X a b C`.
  Specifying a finite interval already gives finite Tor amplitude; a second existential
  interval condition would be redundant.
- The total derived direct image is the canonical existing functor
  `(rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj C`.
- The two conclusion clauses are `DerivedCategory.isBoundedConstructible A Y ...`
  and `DerivedCategory.hasTorAmplitudeIn A Y a (b + (d : ℤ)) ...`.
  Together they give exactly membership in Dctf(Y_et,A) with the asserted interval.
  No replacement constructibility predicate or new tensor construction is introduced.

Dependency declarations and interfaces read:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  with separatedness and universal closedness as its recorded component classes.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`; these are among the
  recorded declarations of the derived-category and Tor-amplitude dependencies.
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` publicly exposes the latter and its
  lower-bound variant. The definitions were read in full.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, using the recorded
  finite-stalk constructibility notion. Its public import closure already supplies the
  ordinary derived-category declarations through `Sheaf.AlgebraicGeometry.DerivedCategories`.
  Importing the synonymous upstream derived-categories module in addition would duplicate
  `torsionCohomology`; that unused torsion predicate is not needed by this statement.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` was read to check
  the recorded unbundled geometric-point convention.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its documented
  scheme base change is `pullback`; the full signatures/docstrings were read, including
  the geometric-fibre definition. This theorem uses the arbitrary chosen geometric point
  directly, rather than replacing it by only a residue-field algebraic closure.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology`, with a sheaf placed in degree zero as documented.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; the ordinary unbounded total derived functor is
  exposed by `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` as
  `AlgebraicGeometry.Etale.rightDerivedLowerStar`.
- `sk-def-sfb-dc-setting` has no Lean record. This item needs only its explicit standing
  geometric hypotheses, all written above with existing Mathlib declarations. It does
  not use the pro-etale condensed-coefficient category or a chosen compactification
  defined later in that setting node, and introduces neither of those notions.

All currently recorded proof-dependency modules are imported without `public` unless
already required publicly by the statement. The two Mathlib proof leaves are imported via
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` and
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`, with
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective` for the latter's second clause.
The current five-step natural-language proof is included in the theorem docstring:
constructibility; constant-module projection formula; proper-base-change stalk formula;
fibre spectral sequence and finite filtration; arbitrary sheaves tested by geometric stalks.

Edge cases checked before writing:

- Empty X, empty Y and empty geometric fibres are admitted: there is no nonemptiness
  hypothesis. On an empty fibre the sheaf/cohomology vanishing requirement is consistent.
- The zero ring is admitted (`Finite`, without `Nontrivial`); hA holds there, and the
  corresponding module categories have only zero objects up to isomorphism.
- The zero complex and a = b are admitted. Negative a or b are allowed.
- d = 0 is admitted and gives the unchanged output interval [a,b].
- ℓ = 2 and positive characteristic different from ℓ are allowed. Positive characteristic
  is not replaced by characteristic zero or by an invertibility assumption alone.
- The test F need not be finite, constructible, or killed by one uniform power of ℓ.
  Its zero section is already killed by ℓ^0 = 1, so allowing exponent zero changes nothing.
- No modules used to test the Tor predicate are required to be finite or flat.
- The geometry lives in universe u, geometric fields in u, and coefficient modules/groups
  in u+1, following the recorded small-etale-site convention. There is no independent
  lower universe for geometric test fields, and every variable and universe is bound.

Searches for reuse:

- `msearch.py ... leanfinder "proper etale derived direct image preserves finite Tor
  amplitude with geometric fibre cohomological dimension bound"`: eight hits on étale
  morphisms and base change, no matching theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.rightDerivedLowerStar,
  DerivedCategory"`: unknown project identifier, zero hits; replaced by a valid query.
- `msearch.py ... loogle "DerivedCategory"`: twelve hits on the generic derived category,
  single functors and structural instances, no proper Tor-amplitude statement.
- `msearch.py ... grep "torAmplitude|finiteTorAmplitude|rightDerivedLowerStar"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg -n "torAmplitude.*[Pp]roper|[Pp]roper.*torAmplitude|hasTorAmplitudeIn.*rightDerived|
  finiteTorAmplitude.*rightDerived"` in the upstream `WeilConjectures` and side
  `lean/Sheaf`: only unrelated generic flat-model lemmas; no matching theorem.
- `rg -n "det-ctf-finite-proper-tor"` in upstream `WeilConjectures`: no attachment.
- Read upstream `Derived/Coefficients.lean`, `Derived/LowerShriek.lean`,
  `UpperLowerStar/Defs.lean` and `Derived/UpperLowerStarCoherence.lean`, plus the
  recorded side modules, to verify signatures rather than relying on search names.
- Checked `dag/lean_names_upstream.json` for the statement/expected Tor-proper names:
  no existing declaration for this node.

No new nodes, dependency modules, statement corrections, or disputed statements.

Validation: the prescribed `scompile.py Q01 det-ctf-finite-proper-tor <file>` compiled the
published derived-tensor-stalk dependency in its isolated overlay, then this delivery
as both sandbox and library module. Both delivery compilations passed without errors
or warnings (3.4 s and 3.6 s). No global build or live-source edit was run.

## Second reading by Q01

Author's self-check for the direct-dispatch workflow; the maintainer provides the
independent review. Reopened the node and module and checked every correspondence above:
positive characteristic and prime are explicit; separated finite-type schemes and the
k-morphism are explicit; hA includes the exponent positivity; hd quantifies over every
geometric point, every abelian sheaf with the stated sectionwise torsion condition and
every degree above d; the Tor predicate quantifies over arbitrary module sheaves;
the conclusion preserves bounded constructibility and has exactly upper endpoint b+d.
The Dctf condition is expanded as bounded constructibility plus the specified finite
Tor interval, avoiding a different upstream constructibility convention. There was no
mathematical mismatch requiring a node change. The source, node and Lean all admit
zero rings, zero complexes, empty schemes and d = 0.
