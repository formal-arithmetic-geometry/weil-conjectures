## Worker report

The module `Sheaf.AlgebraicGeometry.NormalInseparableNormalizationRadicial` states
`AlgebraicGeometry.normal_inseparable_normalization_radicial`. Its only theorem has
proof `sorry`. Six auxiliary declarations provide real canonical constructions owned
by this statement: the reduced field base change, its normalization projection, the
reduced affine tensor ring R, its integral closure D in Frac R, and the maps C to R
to D. They are recorded in `lean.declarations`. They do not replace any existing
notion: every construction uses the dependency's existing definition directly.
No definition contains postponed data or a postponed proof.

The node is unchanged except for `lean`. No correction or disputed statement is needed.
Sources read: Stacks `varieties.tex`, lemma-normalization-and-change-of-fields (0C3N),
including its affine proof and fixed-power monic-polynomial argument; and `algebra.tex`,
lemma-p-ring-map (0BRA) and lemma-p-ring-map-field, including their proofs.
The normalization source and its finiteness and affine-normal-locus interfaces were
read in `WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean`.

Clause-by-clause translation:

- A field k and a finite purely inseparable extension l/k are `(k l : Type u)`,
  `[Field k] [Field l] [Algebra k l] [Module.Finite k l] [IsPurelyInseparable k l]`.
- The normal integral finite-type k-scheme is `S`, its named structure map `pS`,
  `[IsIntegral S] [LocallyOfFiniteType pS] [QuasiCompact pS]`, and `hnormal`, which
  requires `IsDomain` and `IsIntegrallyClosed` for every local ring. No smoothness,
  separatedness, projectivity or geometric normality is assumed.
- T is exactly `inseparableBaseChangeReduction k l S pS`, namely the nilradical
  subscheme of `pullback pS (Spec.map (CommRingCat.ofHom (algebraMap k l)))`.
  The first existential assertion is `IsIntegral T`; its witness is then available
  for the existing `Scheme.normalization` construction. The next assertion is
  `IsIntegral T.normalization`, so B is the specified normalization, not a freely
  chosen normal model.
- q is `normalInseparableProjection k l S pS`, defined by `fromNormalization`,
  `nilradical.subschemeι`, and `pullback.fst`, in precisely that order.
  Its three global properties are `IsFinite`, `Surjective`, `UniversallyInjective`.
  Mathlib's radicial equivalence is the one recorded in def-weil-radicial-morphism.
- The induced function-field extension is specified, not arbitrary: `hq` says the
  generic point maps to the generic point, and the existential algebra has its
  `algebraMap` equated to `stalkSpecializes (specializes_of_eq hq)` followed by
  `q.stalkMap`. The next two conjuncts are its `Module.Finite` and
  `IsPurelyInseparable` properties.
- Positive characteristic is quantified as `∀ (p : ℕ) [CharP k p], p.Prime → ...`.
  For fields these are exactly the positive characteristics. The first conjunct
  supplies `∃ N : ℕ, ∀ a : l, a ^ (p ^ N) ∈ Set.range (algebraMap k l)`.
  The following `∀ N` accepts EVERY prescribed exponent with this property.
  It does not replace N by a larger number.
- The uniform function-field bound uses `∀ z : B.functionField`, membership of
  `z ^ (p ^ N)` in the range of the specified induced function-field map.
- The residue-field bound uses `∀ b : B, ∀ z : B.residueField b`, membership of
  `z ^ (p ^ N)` in the range of `(q.residueFieldMap b).hom`. This is the node's
  bound at the unique point over each prime, expressed globally on all source
  points; the affine prime formula below supplies the point identification.
- Every nonempty affine open is quantified by `(U : S.Opens) (hU : IsAffineOpen U)`
  and `Nonempty U`. Its presentation is any k-algebra C with
  `e : Spec (.of C) ≅ U.toScheme` and `e.hom ≫ U.ι ≫ pS = Spec.map (algebraMap k C)`.
  This equation merely says that the named affine presentation has its given
  k-structure. There is always the canonical presentation C = Γ(S,U).
- R is the actual quotient `(C ⊗[k] l) ⧸ nilradical (C ⊗[k] l)`, bundled by
  `inseparableAffineReduction`. D is `integralClosure R (FractionRing R)`, bundled
  by `inseparableAffineNormalization`. `toInseparableAffineReduction` is the
  tensor inclusion followed by the quotient map; `toInseparableAffineNormalization`
  composes this with R's canonical map into its integral closure.
- The inverse image q⁻¹U is Spec D through the existential isomorphism `j`.
  Its displayed equation over S identifies its structural map with precisely
  `Spec.map (toInseparableAffineNormalization k l C)` followed by the given chart.
  Thus the inverse-image assertion includes the canonical C to D map.
- Injectivity is `Function.Injective (toInseparableAffineNormalization k l C)`;
  finiteness is that same ring map's `.Finite` property, not finiteness of an
  unrelated algebra. The next conjunct quantifies EVERY d in D and requires its
  `p ^ N` power to lie in this same map's range.
- For every `P : PrimeSpectrum C`, the existential `J : PrimeSpectrum D` has
  contraction `Ideal.comap ... J.asIdeal = P.asIdeal`. The next conjunct quantifies
  every other J' with this contraction and requires J' = J. The last conjunct is
  exactly the prime formula: `d ∈ J.asIdeal ↔ ∃ c : C, c ∈ P.asIdeal ∧ map c = d^(p^N)`.
  Injectivity makes this the literal formula `{d | d^(p^N) ∈ P}` under C ⊆ D.
- Characteristic zero is `∀ [CharZero k], Function.Surjective (algebraMap k l) ∧ IsIso q`.
  Surjectivity of the field embedding says l=k as an extension, without requiring
  literal equality of carriers of the two fields.

Dependency declarations used (the recorded interfaces were read, including docstrings):

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`.
- def-weil-field: Mathlib's `Field`.
- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`; and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact`.
- def-pc-base-change: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, whose
  scheme base-change convention explicitly uses `Limits.pullback`, `pullback.fst`,
  `pullback.snd`; its primary module-pullback declaration is not the scheme construction.
- def-weil-pbc-scheme-reduction: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
  `Scheme.nilradical`, `Scheme.IdealSheafData.subscheme`, `subschemeι`.
- def-sc-normalization: `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`,
  `Scheme.normalization` and `Scheme.fromNormalization` for integral schemes.
- def-weil-finite-integral-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `IsFinite`.
- def-weil-surjective-morphism: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `Surjective`.
- def-weil-radicial-morphism: `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`,
  `UniversallyInjective`, whose recorded TFAE identifies it with radiciality.
- def-sc-function-field: `WeilConjectures.AlgebraicGeometry.FunctionField`, whose arbitrary
  integral-scheme clause reuses `Mathlib.AlgebraicGeometry.FunctionField`, `Scheme.functionField`.
- def-weil-pbc-normal-ring: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` together with `IsDomain`, written inline as recorded.
- def-weil-pbc-finite-purely-inseparable-extension:
  `Mathlib.FieldTheory.PurelyInseparable.Basic`, `IsPurelyInseparable`, `Module.Finite`.

Plain proof imports also include the recorded homeomorphism theorem in
`WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`, componentwise
normalization in `Sheaf.AlgebraicGeometry.ReducedNormalization`,
`Mathlib.RingTheory.LocalProperties.IntegrallyClosed`, and
`Mathlib.RingTheory.Algebraic.Integral`. Normalization finiteness/existence and affine
function fields are already in public imports. The proof-only node
lem-sfb-normalization-affine-total-fractions has no recorded declaration or mathlib match
in the read DAG, so there is no module to import for it. It supplies no missing notion
needed to type this statement; its future proof interface belongs to stage 3's plan.

Edge cases checked before writing: S empty is excluded exactly by IsIntegral; nonempty
zero-dimensional schemes and S = Spec k are included. Empty affine opens are excluded by
Nonempty U, as in the node, since their rings are zero rings. For N=0 the power is 1:
the hypothesis forces l=k and all chart, residue and function-field maps are surjective.
For l=k the statement reduces to normality of S and its identity normalization. In
characteristic zero the field equality is equality as an extension, expressed through
surjectivity of its canonical embedding. Nonreduced tensor products are allowed and
are actually reduced by the nilradical quotient; geometric reducedness is not assumed.
All universes and variables are explicit, with `autoImplicit false`.

Searches actually run using msearch.py (NI and this item):

- leanfinder: `Normalization of a normal scheme after finite purely inseparable base change
  is finite radicial with a uniform Frobenius exponent`: eight hits, including relative
  normalization, integrality and its universal factorization. None states the theorem.
- loogle: `AlgebraicGeometry.Scheme.normalization, IsPurelyInseparable`: zero hits,
  unknown identifier for the upstream-only normalization abbreviation.
- grep in Mathlib/AlgebraicGeometry: `normalization.*inseparable|inseparable.*normalization`:
  zero hits.
- leansearch: `normalization of purely inseparable base change of normal scheme Frobenius
  bound`: eight hits including purely inseparable normal extensions and element-exponent
  bounds; no scheme statement with the requested affine and prime formulas.
- rg of live WeilConjectures and Sheaf: `normalInseparable|normal_inseparable|inseparable.*[Nn]ormali|[Nn]ormali.*inseparable|lem-sfb-normal-inseparable-normalization-radicial`:
  related NormalizationInseparableBaseChange, NormalAlterationConstantRegularization and
  NormalizationGeonormalInsep, but none states the item. Read the first two relevant
  modules: the former compares successive normalized base changes under geometric
  normality; the latter uses a radicial normalization in a much larger alteration theorem.
- rg in both project roots: `normalization.*[Ff]robenius|[Ff]robenius.*normalization|normal_inseparable_normalization`:
  only unrelated Frobenius normalization conventions, no duplicate statement.
- `grep -rn 'lem-sfb-normal-inseparable-normalization-radicial' lean/WeilConjectures`:
  no hits. No exact existing declaration was found.

Validation uses only scompile.py and deliver2.py, never a local or global build.
The initial compiler probe found missing TensorProduct scope; adding `open scoped
TensorProduct` fixed the parse errors. The complete theorem and all actual definitions
then compiled cleanly, first as a sandbox module and then by the actual module name.

## Second reading by NI

This is the worker's self-audit with the node and complete module open. No independent
reader was started: the dispatcher explicitly forbids additional agents and assigns
independent review to the maintainer. The clause-by-clause audit above checked every
hypothesis and conclusion, including the same fixed N on D, residues and the function
field, uniqueness and the literal membership formula for primes, and the characteristic
zero extension equality. No mathematical mismatch or statement correction was found.
