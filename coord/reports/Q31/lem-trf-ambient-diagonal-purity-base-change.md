## Worker report

The module `Sheaf.Paper.AmbientDiagonalPurityBaseChange` states the ordinary,
unbounded finite-coefficient smooth-purity theorem with its specified diagonal
orientation, exceptional tensor map, base-change equations, composition and
exceptional internal-Hom map. The primary declaration is
`AlgebraicGeometry.Etale.AmbientDiagonalPurity.ambientDiagonalPurityBaseChange`.
All theorem proofs are `sorry`; all definitions have explicit data. The helper
statements concern clauses of this same node: existence and uniqueness of its
normalized orientation, existence of an annihilating exponent, trace composition,
and the dimension-zero normalization. No statement correction is made.

Hypothesis and conclusion correspondence (names below are in
`AlgebraicGeometry.Etale.AmbientDiagonalPurity` unless qualified):

- The prime is `ell : ℕ` with `[Fact ell.Prime]`. A finite extension of Q_ell is
  `E : Type u`, `[Field E]`, `[Algebra (Padic ell) E]` and
  `[FiniteDimensional (Padic ell) E]`. `Coefficient ell E n` is the universe lift
  of the existing `Padic.coefficientExtensionRing ell E (n + 1)`;
  `n : ℕ` thus ranges over every positive coefficient level exactly. It is the
  same quotient used by `TraceFormulaCoefficientConventions.coefficientRing`,
  not a new valuation ring or coefficient quotient. The lift permits the usual
  `ModuleCat.{u+1}` small-etale convention; it changes no ring operations.
- `m`, `hm : 0 < m` and `hA` expose any annihilating prime power. This is an
  auxiliary presentation of the coefficient sheaf, not a restriction on a finite
  coefficient ring: `coefficient_annihilator` asserts its existence for every
  permitted coefficient field and positive level.
- `Y : Scheme.{u}`, `[IsNoetherian Y]`, and
  `_hExcellent : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U.1)` render the excellent
  Noetherian base. `hEll : IsUnit (ell : Γ(Y, ⊤))` renders invertibility of ell.
  `IsNoetherian` is the standard locally-Noetherian plus quasi-compact predicate,
  equivalently the finite affine-cover convention in the node.
- `h : X ⟶ Y`, `[SmoothOfRelativeDimension d h]`, `d : ℕ`,
  `[IsSeparated h]`, and `[QuasiCompact h]` render separated smooth finite type
  and pure relative dimension d ≥ 0. Smoothness already includes local finite
  presentation, so quasi-compactness is exactly the remaining finite-type
  condition. `[IsNoetherian X]` and `[HasCompactification h]` expose consequences
  of these hypotheses (finite-type permanence and Nagata). They add no geometric
  restriction. The analogous source and compactification arguments in the
  base-change and composition clauses have the same meaning.
- Every object belongs to `Etale.DerivedCategoryModule A T`, namely the ordinary
  unbounded derived category of `Sheaf T.smallEtaleTopology (ModuleCat A)`.
  `rightDerivedLowerShriek`, `rightDerivedUpperShriek` and their recorded
  adjunction provide compact supports and h^times. `dualizingComplex` is
  h^times of the coefficient unit. No pro-etale operation is substituted.
- The existing `ordinaryFiniteLine` is the scalar extension of the roots-of-unity
  sheaf. `affineLinearBaseCoefficient A N hA X d` is its ordered shifted tensor
  power, the existing model of A_X(d)[2d], including the zero-fold tensor.
  `twistedPullback` is h* followed by tensor with this object, hence h*M(d)[2d].
  `ExponentIndependent` gives normalized identifications for larger annihilating
  moduli: its root map is specified by multiplication by N'/N, and its line map
  by the pure-tensor equation. Tensor powers and evaluation fix all other twists.
  For two exponents of ell, compare to their maximum; this gives the stated
  independence of m. `twistTransport` reuses the normalized finite Tate
  transport from `p1DecompositionTwistTransport`, with no new sheaf construction.
- `DiagonalNormalized` specifies the inverse orientation theta. Its first factor
  is `diagonalRestriction`: exceptional self-base-change pulled back along the
  diagonal. The two identical factors of the categorical pullback can be
  interchanged; the projection named p1 in the mathematical description is
  `pullback.snd h h` in this presentation, and p2 is `pullback.fst h h`.
  Its second factor is the actual `NoetherianSectionSpecialization.specialization`
  for the diagonal, with `Normalized` fixing its value at one. The normal-cone
  comparison is over X and preserves zero, followed by the actual
  `FiniteRingSectionDeformation.coneBundleIso` induced by Sym(I/I²) → gr(I).
  `normalSectionComparison` is the canonical exceptional section comparison;
  `c.hom = normalSectionComparison ...` fixes it, rather than postulating an
  arbitrary line isomorphism. The last factor is `bundleOrientation`, the
  restriction of inverse Kummer-normalized bundle purity to zero. This gives
  the tangent bundle via its conormal-module relative-Spec presentation.
  `existsUnique_orientation` asserts the existence and uniqueness of precisely
  this theta; `inverseOrientation` chooses that unique object. Thus its data
  are determined up to equality, as required by the no-hollow-definitions rule.
- `gamma` first tensors with `inverseOrientation ... .inv` (a_h), then uses
  `smoothTensorDualityMap` with its canonical inverse-projection/counit formula.
  `Conclusions` asserts `IsIso` for every M and the exact naturality equation
  for every map `k : M ⟶ M'`. No boundedness, constructibility, finite Tor or
  dualizability binder is present.
- In `Conclusions`, Y' is any excellent Noetherian scheme, and `v : Y' ⟶ Y`
  is arbitrary. X' is `pullback h v`, u is `pullback.fst h v`, and h' is
  `pullback.snd h v`. The unit proof `hX'` is transport of invertibility along
  the scheme map and imposes no additional condition. The first equality is
  orientation base change. The next is exactly
  `u*.map (gamma ... M) ≫ smoothExceptionalBaseChangeMap ... M =
  gammaBaseChangeIso.hom ≫ gamma ... (v*.obj M)`.
  `smoothExceptionalBaseChangeMap` is the published transpose of inverse
  compact-support exchange followed by the pulled-back counit; this is c_M,
  with the same direction as the node. `gammaBaseChangeIso` uses the existing
  tensor/pullback, pullback-composition and normalized Tate identifications.
- `trace` is defined by the inverse hom-equivalence of the actual compact-support
  adjunction. The final equality under each base change identifies v* of this
  trace with compact-support exchange, the source identification, and trace h'.
  Thus the orientations, tensor maps and traces all have explicit base-change
  equations.
- The final two clauses of `Conclusions` give tensor-map and orientation
  composition. `exceptionalCompositionIso` is right-adjoint uniqueness for the
  actual unbounded compact-support composition isomorphism, preserving the
  composite counit. `coefficientCompositionIso` and `gammaCompositionIso` use
  only associativity, unit, pullback and the ordered Tate tensor product.
  `trace_composition` states the resulting trace equality with the actual tower
  isomorphism and successive traces. This is the node's composition clause.
- `etale_trace_normalization` says the rank-zero trace is the recorded derived
  etale sum/evaluation counit, using `zeroTwistIso`, the normalized compact-support
  comparison, and the canonical exact/derived pullback comparison. Its parameter
  `ν : EtaleCompactSupportNormalization A` is any normalized presentation of
  the already available comparison, not an arbitrary functor or new adjunction.
  By the same adjunction this fixes gamma and, at the unit, the orientation.
- Separable closures, all extensions of separably closed fields, and geometric
  fibres of excellent traits are instances of the unrestricted excellent
  Noetherian Y' clause: fields are excellent Noetherian and v need not be finite
  type. Identity and nonflat base changes are included.
- `exceptionalHomComparison A h L M` uses the recorded `derivedHom` and
  `derivedTensorHomAdjunction`. Its defining pairing is exceptional tensor
  followed by evaluation, with the necessary tensor symmetries for the published
  left-tensor adjunction convention. `Conclusions` asserts this precise map is
  an isomorphism for all L,M. This records both the direction and normalization
  of H_h and imposes no dualizability condition.

Dependency declarations read and reused:

- `def-trf-coefficient-conventions`: `Sheaf.Paper.TraceFormulaCoefficientConventions`,
  `WeilConjectures.TraceFormulaCoefficientConventions.coefficientRing`; its body is
  the existing `Padic.coefficientExtensionRing`. The module imports the dependency module and
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, which exposes exactly
  that coefficient construction and `Padic.finite_coefficientExtensionRing`.
  The unrelated finite-field/pro-etale package is not made a hypothesis of this
  ambient theorem.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension` (and its `Smooth` instance);
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`.
- `def-weil-pbc-derived-categories`: the recorded ordinary encoding
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, defined in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `def-amb-etale-compact-support`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`; the chosen
  `rightDerivedLowerShriek` uses this construction for the selected compactification.
- `thm-amb-etale-exceptional-adjoint`:
  `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`,
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  the existing `rightDerivedUpperShriekAdjunction` is the usable adjunction interface.
- `def-kun-derived-tensor`:
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor` and `derivedTensorRight`.
- `def-pur-derived-internal-hom`:
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, which now publicly exposes
  the recorded ordinary specialization `AlgebraicGeometry.Etale.derivedHom` and
  `derivedTensorHomAdjunction` from the upstream Hom module. No private copy is needed.
- Further canonical interfaces are those already recorded for proof nodes:
  `FiniteRingSectionDeformation` (geometry, normalized specialization, bundle
  orientation), `SmoothExceptionalBaseChange` (actual mates),
  `OrdinaryFiniteP1Decomposition` (normalized Tate transport), and
  `UnboundedEtaleCompactSupportComparisons` (actual tower isomorphism).

Edge cases checked in the node and definitions: d=0 uses the empty ordered tensor,
unit constraints, and rank-zero deformation; positive coefficient level 1 is
`n=0`; empty X is not excluded; arbitrary unbounded L,M and zero complexes are
included; identity, nonflat and non-finite-type base changes are included. The
scheme universe is arbitrary u and coefficients are lifted to u+1, as required
by the ordinary small-etale category. The proof docstrings follow all twelve
steps of the node's finite-ring proof. No mathematical statement dispute found.

Searches (the saved `searches.jsonl` preserves the msearch results of the earlier
attempt, which this repair retained):

- LeanSearch: `Smooth etale purity diagonal deformation normalization and
  exceptional internal Hom comparison`: eight normalization-related hits,
  none stating this theorem.
- LeanFinder: `Smooth purity on ordinary unbounded etale derived categories
  with diagonal deformation and exceptional internal Hom`: eight algebraic
  smooth/etale hits, no match.
- Loogle: `"purity"`: twelve compiler-purity hits, no mathematical match.
- msearch grep: `smooth.*purity|purity.*smooth|diagonal.*orientation`: no Mathlib hit.
- `rg` on upstream WeilConjectures and project `lean/Sheaf` for the same concepts
  found the existing abstract orientation, smooth tensor/base-change, finite
  section-deformation and vector-bundle interfaces used here. None gives the
  complete normalized diagonal theorem with all these equations.
- Exact item-id search and `DiagonalNormalized|ambientDiagonalPurityBaseChange|
  ExponentIndependent|inverseOrientation` in those two source trees found no
  existing declaration of this module. The existing notions are imported.

## Second reading by Q31

This is a second pass by the same dispatcher worker; the dispatcher explicitly
forbids starting another agent, and the delivery receives independent maintainer
review. I reread the node, all eight statement-dependency records and their
implementations, the finite-stage smooth-purity proof, the diagonal-orientation
proof and the base-change-factor proof, with this module open.

The first paragraph matches the prime, finite extension, positive level,
excellent Noetherian base, invertible prime, smooth separated finite-type map,
and ordinary unbounded categories as detailed above. The positive level is
reindexed by n+1 and the coefficient universe lift is explicit. Source
Noetherianity and compactifiability are consequences, not extra restrictions.
The orientation direction is checked: theta goes from omega to the shifted
Tate tensor, gamma uses theta.inv, and the deformation's cone-to-bundle section
comparison is inverted. Self-base-change uses the two projections consistently
with this chosen ordering. The tensor and internal-Hom maps are actual counit
and evaluation mates. The base-change equations include the source twist
identification and the trace equation. Both composition clauses and the
companion trace theorem use the actual counit-preserving adjoint comparison.
The rank-zero companion fixes the sum/evaluation normalization. The last
paragraph matches arbitrary L,M and the given direction of H_h. No silent
boundedness or finite-Tor assumption was found.

The resumed packet contained its node record and report. I retained them and repaired
only the compiler diagnostics. No new nodes or dependency replacements are introduced.

The original dry run and its server confirmation both timed out. A temporary diagnostic
copy with a smaller heartbeat budget isolated the kernel timeout to the use of the
monoidal-syntax exceptional tensor map inside `exceptionalHomComparison`.
`exceptionalTensorMap` now expresses the same canonical map directly through the recorded
`derivedTensor` bifunctor: inverse compact-support projection, tensoring its counit, then
`rightDerivedUpperShriekAdjunction.homEquiv`. It uses the inverse components of `asIso`
of the actual projection transformation, so no component-invertibility assumption is
introduced. This removes the expensive comparison between two tensor presentations.
The internal-Hom comparison uses this helper followed by the same symmetry and evaluation.

The base-change clause now exposes `[IsNoetherian (pullback h v)]`, a consequence of the
smooth finite-type map `pullback.snd h v` over Noetherian Y', just as the existing source
Noetherian and compactification binders expose consequences of the geometry. This includes
all base changes in the node; it does not assert Noetherianity for an arbitrary pullback
without the finite-type hypothesis. Its proof is the existing
`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType (pullback.snd h v)`.
The ring in `Nat.cast_pow` is explicit in `invertiblePower`; the etale normalization
selects the existing coefficient-category adjunction with `ModuleCat A` and its etale
proof. The proposition-valued transport definition is retained with its real proof data;
its definition-style linter is disabled only for that declaration.

Verification: the prescribed `scompile.py` checked both the sandbox module (19.4 seconds)
and its library-path consumer (18.2 seconds), with no warnings or errors. The delivery
contains no diagnostic options or commands. Every postponed theorem remains `sorry`;
the new helper contains the canonical construction, not postponed data.
