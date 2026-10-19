## Worker report

The module `Sheaf.Paper.IntegralModelSurjectiveClosedReflection` states
`AlgebraicGeometry.ProEtale.integralModel_surjective_closed_reflection`, with its proof
postponed by `sorry`. The node is unchanged except for its `lean` record. Two structural
helpers specialize the existing continuous coefficient construction to the recorded integer
ring, and export its existing pointwise commutativity. Their data and instances contain no
`sorry`; they introduce neither an arbitrary map nor an arbitrary coefficient choice.

Hypothesis and clause correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_ell: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- A = O_E: `Padic.coefficientExtensionIntegers l E`, with the extending valuation
  topology supplied by `spectralNorm.normedField (Padic l) E` and the subring's
  inherited topology inside the coefficient helper. No user-supplied topology or
  extra continuity hypothesis is introduced.
- Condensed A: `integralModelCondensedCoefficients l E` is `Mon.mk` of the existing
  `Profinite.continuousCoefficientRingObj` of A; its sections are ULift C(S,A),
  restriction is precomposition, and ring operations are pointwise. This is the
  topological condensed ring, not the constant discrete ring sheaf.
- Schemes and immersion: `{X Z : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i] [Surjective i]`.
- The small pro-etale sites: `Scheme.ProEt.topology X` and the same construction
  for Z and each cover member. Objects have universe u+1, morphisms universe u;
  the value category is `Ab.{u+1}`. All universe variables are explicitly bound.
- B_T = p_T^* condensed A: `condensedRingObj
  (integralModelCondensedCoefficients l E).X T`.
- F is a B_X-module sheaf: the `F : Mod ... (condensedRingObj ... X)` binder.
- Clause (a): `HasFiniteConstantLocalModel ... X F`.
- Clause (b): `HasFiniteConstantLocalModel ... Z
  ((CondensedRing.upperStar ... i).obj F)`.
- Equivalence: `↔` between these clauses.

Expanding the recorded `HasFiniteConstantLocalModel` declaration gives an existential
`Scheme.Cover.{u} Scheme.proetalePrecoverage`, followed by a separate existential model
for every cover index. The model is a finite presentation of the regular condensed
A-module on the point, pulled to the cover member by `upperStarFromPoint.mapMod`.
`Mod.IsFinitelyPresented` is explicitly the cokernel of a map between finite sums of
regular A-modules. Such maps are matrices of global sections of A, and the global
sections of the continuous condensed A at the singleton are exactly A. Therefore the
model is exactly B_U tensor over the constant A_U with a finitely presented scalar
A-module. Since the recorded integer ring is a DVR and hence Noetherian, finitely
generated scalar A-modules are exactly finitely presented scalar A-modules. Both
implications hold: every module in the node has a finite presentation over A; every
finite scalar matrix gives a finitely generated scalar module. Inverse image preserves
this cokernel presentation. Thus this is the dependency's existing rendering of the
displayed tensors through the constant-section map, not a replacement by arbitrary
locally finitely presented B_U-modules. A need not act discretely on B_U. Torsion and
variation of the scalar module with the cover index are both allowed.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` imports the complete recorded
  coefficient constructions, including `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionAbsoluteValue` and `Padic.extension_integers_dvr`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective` (exported by the closed-immersion import).
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` exports
  `Profinite.continuousCoefficientRingObj` and
  `Profinite.isCommMonObj_continuousCoefficientRingObj`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`,
  `upperStarFromPoint`. This is the shared 51-module framework, not the older checkout.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar` and its composition interface.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`.

The public imports expose the statement dependencies. The non-public proof imports
include `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement`,
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`, and
`Sheaf.Paper.CondensedSurjectiveClosedEquivalence`. The last two Sheaf proof modules
were absent from the local snapshot: their actual published sources and complete
signatures/docstrings were read using `scompile.py --source`. The still-unstated
`sk-def-sfb-change-of-scalars` and `sk-prop-sfb-cartesian-coefficients` have no module
to import; their constructions/untwisted comparisons are already in the module-object
framework. No theorem from an unrecorded private substitute is assumed.

Edge cases checked before writing: i = identity; X = Z empty, where an empty covering
is allowed; Spec k into Spec k[epsilon]/epsilon^2; a general surjective closed immersion
without a bounded nilpotence exponent; scalar modules 0, A, A/varpi and A/varpi^2;
a cover with different ranks and torsion exponents on different members. Neither
Noetherianity of X nor invertibility of ell on X is assumed. No nonempty cover-index
condition, finite-length condition or finite-free condition was added. The finite
presentation characterization includes n=m=0. There is no statement dispute.

Searches for an existing statement:

- `msearch.py leansearch`, query `Finite constant scalar module models reflected by
  surjective closed immersions on the proetale site`: 8 hits about ordinary closed
  immersions and scalar restriction; no matching reflection theorem.
- `msearch.py leanfinder`, query `Surjective closed immersion reflects finite constant
  local models for modules over a condensed valuation ring`: 8 hits about epimorphisms
  of condensed modules, solid modules and adic completion; no matching statement.
- `msearch.py loogle`, query `CategoryTheory.Sheaf.IsConstant`: 12 general constant-sheaf
  hits. Inspected its definition and equivalence invariance in ConstantSheaf.lean:
  these do not state reflection of scalar models over the nonconstant B_X.
- `msearch.py grep`, query
  `HasFiniteConstantLocalModel|condensedSurjectiveClosed|finite.*constant.*model`:
  no Mathlib hits.
- `rg` in upstream WeilConjectures and shared lean/Sheaf for integral models,
  `HasFiniteConstantLocalModel`, coefficient integer topology and the proposed
  declaration names; `grep -rn` of the item id in upstream WeilConjectures:
  no existing theorem of this statement. Found and reused the current constant-model
  predicate; read its definition and `CategoryTheory.Mod.IsFinitelyPresented` in Free.lean.
  The existing equivalence and cover-refinement theorems are proof tools, not this theorem.

Validation: the prescribed `scompile.py Q58 lem-sfb-integral-model-surjective-closed-reflection`
compiled the sandbox module and its library-name form cleanly (25.7 s and 6.8 s), with
no errors or non-sorry warnings. No global build or direct git operation was run.

## Second reading by Q58

Re-read the finished signature against the node, including every clause of (a) and (b),
and re-opened the actual finite-presentation definition. The initial point to check was
finitely generated versus finitely presented: these are equivalent over this DVR,
without imposing finite freeness or excluding torsion. The existential finite matrices
are chosen on the point, so their entries are scalar elements of A, rather than
arbitrary local functions on a scheme. Verified the coefficient helper uses the
spectral valuation topology, and that module pullback is the recorded extension after
monoidal inverse image. The equivalence retains both directions and arbitrary covers.
All variables/universes are bound; no statement correction, new node or dependency
repair was needed. This is the worker's second pass; the maintainer's independent
review is separate, as required by the dispatch brief's no-other-agents instruction.
