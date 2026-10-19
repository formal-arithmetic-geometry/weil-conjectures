## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds` states
`AlgebraicGeometry.Etale.strictLocal_etale_dimension_bounds` with proof `sorry`.
It introduces no definitions or auxiliary theorems. The node is unchanged except for `lean`.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XVII,
Propositions 3.2.1 and 3.2.2, printed pp. 268--269. Proposition 3.2.1 gives the
support-sensitive punctured bound and the supported consequence; Proposition 3.2.2
gives the generic-point bound. The node supplies the extension to prime-power
coefficients and its full proof plan; the module docstring carries that proof.

Hypotheses and clauses, in order:

- The local scheme is `Spec R`, with `R : CommRingCat.{u}`. This is the usual
  coordinate-ring presentation of a local scheme, rather than an additional
  affine restriction: a scheme with a unique closed point specializing every
  point is affine, since any affine neighbourhood of that point is the whole
  scheme. All sheaves below are on this presentation. No regularity, normality,
  finite-type or constructibility assumption is introduced.
- Noetherian: `[IsNoetherianRing R]`. Excellent: `hR : IsExcellent R`.
  Strictly henselian local: `[IsStrictlyHenselianLocalRing R]`, whose parent
  `HenselianLocalRing R` supplies the local-ring instance.
- Prime ell: `hℓ : ℓ.Prime`. Positive exponent: `hn : 1 ≤ n`.
  Invertibility on the scheme: `hunit : IsUnit (ℓ : R)`.
- Finite dimension d: `d : ℕ` and `hd : ringKrullDim R = (d : WithBot ℕ∞)`.
  Ring Krull dimension equals the topological dimension of its spectrum.
- Closed point: `IsLocalRing.closedPoint R`. Puncture: `U : (Spec R).Opens`
  with `hU` equating its underlying set to the complement of this singleton.
  Specifying this unique open does not add geometric data or exclude d = 0.
- Coefficients: every module category is over `ULift.{u + 1} (ZMod (ℓ ^ n))`.
  The lift is the standard ring lift, with the same ring operations and elements;
  it puts the finite coefficient ring in the universe of the recorded
  `derivedSupportedEtaleSections` interface. This is still exactly Z/ell^n.
- Arbitrary F on the puncture: `F : Sheaf U.toScheme.smallEtaleTopology
  (ModuleCat.{u + 1} ...)`. No finiteness condition is imposed on F.
- Nonnegative integral support bound: `e : ℕ`. For every algebraically closed
  field `Ω : Type u` and geometric point `t : Spec (.of Ω) ⟶ U.toScheme`,
  `¬ IsZero (pointedEtaleStalk F t)` implies that
  `topologicalKrullDim (closure ({U.ι (t (IsLocalRing.closedPoint Ω))} :
  Set (Spec R))) ≤ (e : WithBot ℕ∞)`. The closure is in S, not just U.
  Testing geometric points in the scheme universe suffices, since algebraic
  closures of every residue field can be chosen in that universe; changing the
  chosen algebraically closed geometric field does not change stalk vanishing.
- First conclusion: for every `q : ℤ` with `(2 * e : ℤ) ≤ q`, the ordinary
  étale cohomology of the underlying abelian sheaf is `IsZero`. Explicitly it is
  the recorded `Etale.cohomology AddCommGrpCat.{u + 1} U.toScheme q`, applied to
  `DerivedCategory.singleFunctor _ 0` of the scalar-forgotten F. The inequality
  forces q nonnegative, matching ordinary sheaf cohomology.
- Second conclusion: for every arbitrary module sheaf G on S and every integer
  q satisfying `(2 * d : ℤ) < q`, apply the recorded
  `derivedSupportedEtaleSections ... (Spec R) U` to
  `DerivedCategory.Plus.singleFunctor _ 0` of G, and assert `IsZero` of its
  q-th `DerivedCategory.homologyFunctor`. Thus the support is exactly {s},
  and the functor is the right derived kernel of restriction to U.
- Third conclusion: the final conjunct quantifies over `[IsIntegral (Spec R)]`
  locally to that conjunct. The generic scheme is
  `Spec (.of (Spec R).functionField)`; Mathlib defines the function field as
  the stalk at the generic point and identifies it with the affine fraction
  field. Every module sheaf L on that scheme is included. Its ordinary abelian
  étale cohomology, defined just as in the first clause, is `IsZero` for
  `(d : ℤ) < q`. Integrality is not imposed on the first two clauses.

Dependency declarations used (all recorded interfaces read):

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and the recorded
  `DerivedCategory`/`DerivedCategory.Plus`/`DerivedCategory.homologyFunctor`
  encoding, using the corresponding single functors for degree-zero sheaves.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`:
  `AlgebraicGeometry.Etale.derivedSupportedEtaleSections`, built from
  `supportedEtaleSections` as its right derived functor on D+.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`,
  imported by `Mathlib.AlgebraicGeometry.FunctionField`, which also supplies
  `Scheme.functionField` and its affine fraction-field interpretation.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded sheaf-category
  conventions, namely `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`
  and abelian sheaves in `AddCommGrpCat.{u + 1}`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`:
  `AlgebraicGeometry.pointedEtaleStalk`, exactly the pointed-neighbourhood colimit.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology`, derived global sections followed by homology.

Recorded proof-dependency modules are ordinary (non-public) imports. The affine
open strict-local dimension bound currently has no recorded declaration and is
therefore not imported. No downstream punctured bound is imported, since it uses
this item and would create a cycle. No dependency repair or new node was needed.

Edge cases checked: e = 0 forces the punctured sheaf to be zero (every point of
U has a nontrivial specialization to s and hence closure dimension at least 1).
For d = 0, the puncture is empty, including for nonreduced local rings; all its
cohomology vanishes, supported positive cohomology vanishes by strict-local
acyclicity, and in the integral case S is the spectrum of a separably closed
field. Zero sheaves satisfy all three conclusions. n = 1 is included, and
ell = 2 and mixed/equal characteristic cases are included whenever ell is a unit.
The zero ring is correctly excluded by the strictly henselian local-ring class.
Nonintegral S is included in the first two clauses. Thresholds are q >= 2e,
q > 2d, and q > d respectively, with no accidental vanishing at the latter
endpoints. The module declares its universe and turns off auto-implicit variables.

Searches:

- `msearch.py ... leanfinder`, query “Etale cohomological dimension punctured
  spectrum excellent strictly henselian local scheme support dimension bound”:
  eight unrelated algebraic support-dimension and étaleness hits, no match.
- `msearch.py ... loogle`, query `ringKrullDim, IsStrictlyHenselianLocalRing`:
  no hit; the latter name is upstream rather than Mathlib.
- `msearch.py ... grep`, query `strict.*local.*dimension|punctured.*cohomology`:
  no Mathlib hit.
- `msearch.py ... leansearch`, query “Etale cohomology of a punctured excellent
  strictly henselian local scheme vanishes in degrees at least twice the
  dimension of support closures”: eight étale geometry hits, no match.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, the Mathlib
  sources and `dag/lean_names_upstream.json`: no existing full three-clause result;
  no occurrence of this blueprint id in the source repository.
- `rg` in `lean/Sheaf`: found
  `AlgebraicGeometry.Etale.isZero_cohomology_punctured_of_support_dimension_le`
  in `Sheaf.AlgebraicGeometry.PuncturedSupportCohomologicalBound`. Its signature
  and docstring were read: it covers only n = 1 and only the first conclusion,
  and explicitly derives that conclusion from this node. It is not an existing
  match for this item and cannot be a proof import of this item.

Validation: prescribed `scompile.py Q110 lem-per-strict-local-etale-dimension-bounds
<module>` passed both sandbox and library-name compilations, approximately
3.6 and 3.7 seconds, with no errors or unexpected warnings. No statement dispute.

## Second reading by Q110

Author's separate clause-by-clause rereading, not an independent review; the
maintainer supplies the independent review under this dispatch's brief.
Reopened the node, the Lean file and ILO pp. 268--269. Confirmed that support
closures are taken in the full local spectrum, every module sheaf is quantified,
and the three inequalities have the source endpoints. Checked that the integral
instance is confined to the last conjunct, that the generic scheme is a field
spectrum and that supported cohomology uses the supplied right derived
closed-support functor rather than global sections or ordinary cohomology.
The universe lift preserves the actual coefficient ring up to its canonical
ring equivalence. The explicit Spec presentation is the usual presentation of
an arbitrary local scheme. Checked d = 0, e = 0, n = 1, zero sheaves and
nonintegral schemes as above. No mismatch or correction was found.
