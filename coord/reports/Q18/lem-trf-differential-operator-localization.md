## Worker report

The delivery states `LinearMap.existsUnique_differentialOperator_atPrime` in
`Sheaf.RingTheory.DifferentialOperatorLocalization`. Its sole postponed proof is `sorry`;
the full eight-step natural-language proof is in its docstring. The order predicate is
an actual recursive definition, with no postponed data or auxiliary proof.

Clause-by-clause correspondence:

- A homomorphism of commutative rings R → B is `[CommRing R] [CommRing B] [Algebra R B]`.
  Every such homomorphism supplies this algebra structure; no injectivity is assumed.
- The prime ideal is `(p : Ideal B) [p.IsPrime]`.
- The ordinary localization is Mathlib's `Localization.AtPrime p`; its canonical map j
  is `algebraMap B (Localization.AtPrime p)`. The R-algebra structure on this localization
  is Mathlib's canonical restriction through R → B → Bₚ, inferred without a new hypothesis.
- The node's order definition for any commutative R-algebra C is the new
  `LinearMap.HasDifferentialOrderLE R C`, specialized to M=N=C. Its zero branch asserts
  `∀ c x, D (c • x) = c • D x`, exactly C-linearity since D is already additive. On C itself
  scalar multiplication is multiplication. Its successor branch recursively applies to
  `D.comp (Algebra.lsmul R R M c) - (Algebra.lsmul R R N c).comp D`, which at x is
  D(cx) − cD(x). The general module version is Definition 09CI verbatim.
- A nonnegative bound is `(r : ℕ)`; the given R-linear map is `(D : B →ₗ[R] B)`.
  The bound hypothesis is `(hD : HasDifferentialOrderLE R B r D)`.
- Existence and uniqueness are `∃! E : Localization.AtPrime p →ₗ[R] Localization.AtPrime p`.
  The property being uniquely satisfied is the conjunction of
  `HasDifferentialOrderLE R (Localization.AtPrime p) r E` and the equation
  `∀ b : B, E (algebraMap B (Localization.AtPrime p) b) =
  algebraMap B (Localization.AtPrime p) (D b)`.
  Thus uniqueness applies among extensions with the stated order bound, exactly as the node says.

Dependency declarations read and used:

- `def-weil-pbc-localization-at-prime` records `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, imported publicly. The full abbreviation
  is `Localization p.primeCompl`; its source docstring identifies the complement localization.
  The dependency's residue-field/fibre-ring clauses are not needed here.
- New `def-trf-differential-order` records `LinearMap.HasDifferentialOrderLE` in
  `Sheaf.RingTheory.DifferentialOrder`, imported publicly.
- The new definition's algebra dependency `def-weil-pbc-algebra-hom-quotient` has a
  `mathlib_match` identifying `[CommRing C] [Algebra R C]` and `AlgHom` in
  `Mathlib.Algebra.Algebra.Hom`; this is available through its public import of
  `Mathlib.Algebra.Algebra.Tower`. The full `AlgHom` structure and the source signature and
  docstring of `Algebra.lsmul` were read. The latter is the canonical scalar representation.
- Proof dependency `lem-trf-differential-operator-composition-order` has no Lean record,
  mathlib_match or upstream audit declaration in the read repository, so there is no
  proof module to import. It is explicitly cited in the proof docstring; its node and proof
  dependency remain unchanged.

Edge cases checked before writing: r=0 means multiplication by D(1), which extends by
multiplication by j(D(1)); it does not assert that every extension is unique without an order
bound. The zero operator works at every order. Arbitrary characteristics and arbitrary
commutative base rings are retained. Zero rings have no prime ideals, so there is no lost
prime-localization case. Zero source/target modules are included by the general predicate.
No domain or reducedness assumption is present: for example localization of ℤ/6 at (2) has
nonzero kernel, and both the statement and the fraction-refinement argument cover it.
If B is a field and p=0, this is ordinary localization at all nonzero elements. Universes
u,v (and w,z for the definition's modules) are explicit and independent. No automagic
implicit variables, file-local notation or extra scalar-tower hypotheses occur in the item.
The scalar towers in the general definition express precisely restriction of scalars.

Searches (full structured search outputs are recorded in the new definition node):

- grep: `DifferentialOperator|differential operator|differentialOrder` in `Mathlib/RingTheory`. 0 hits: none. No exact match.
- loogle: `DifferentialOperator`. 0 hits: loogle: unknown identifier 'DifferentialOperator'. No exact match.
- leanfinder: `Finite order differential operators extend uniquely to localization at a prime ideal`. 8 hits: KaehlerDifferential.isLocalizedModule_map, BDeRham, KaehlerDifferential.isLocalizedModule_of_isLocalizedModule, KaehlerDifferential.isLocalizedModule, Algebra.IsSmoothAt, Algebra.H1Cotangent.isLocalizedModule, Algebra.IsSmoothAt.exists_notMem_smooth, KaehlerDifferential.span_range_map_derivation_of_isLocalization. No exact match.
- grep: `DifferentialOperator|differential operator|differentialOrder` in `Mathlib/Algebra`. 0 hits: none. No exact match.
- leansearch: `Recursive differential order bound for linear maps between modules over a commutative algebra, defined by commutators`. 8 hits: LinearMap.instLieRingModule, Derivation.recOn, LieDerivation.recOn, Derivation.instBracket, ContinuousLinearMap.norm_iteratedFDeriv_comp_left, LinearMap.compDer, Derivation.coe_comp, Derivation.rec. No exact match.
- leanfinder: `Linear map has finite algebraic differential order at most n defined inductively by scalar commutators`. 8 hits: LineDeriv.iteratedLineDerivOpCLM, Differential, SchwartzMap.iteratedPDeriv, Derivation, DifferentialAlgebra, Differential.ContainConstants, ContDiffMapSupportedIn.structureMapLM_apply_withOrder, Differential.differentialAlgebraFiniteDimensional. No exact match.

Direct rg searches of Mathlib, WeilConjectures and Sheaf found no algebraic order predicate
or extension theorem. The project hits concern analytic differential operators.
`grep -rn` of the item id in WeilConjectures found nothing. Searches of the DAG for
`differential operator` / `differential order` found the composition and localization
statements but no definition node. `tools/blueprint_refs.py search` for both phrases found
zero blueprint nodes. Full-name searches for the new names found no collisions.

The source was opened locally: Stacks `algebra.tex`, Definition 09CI and Lemmas 0G35/0G36.
It agrees with the node, including uniqueness; the node supplies the uniqueness argument
that Stacks omits. There is no statement correction or STATEMENT-DISPUTED issue.

Validation: both delivered modules were compiled separately using scompile.py against the
published live server library, cleanly and under the standard 60-second limit.

## New nodes

`def-trf-differential-order` defines the recursive differential order bound for R-linear
maps between C-modules, with compatible restricted R-actions, exactly as Stacks Definition
09CI. It supplies the notion the assigned node describes in prose. The generic module form
also admits the composition node's eventual use. It uses canonical `Algebra.lsmul` maps,
not a new scalar-multiplication construction. LeanSearch, LeanFinder, Loogle, Mathlib grep,
project grep and DAG/blueprint searches above found no existing declaration or definition
node for it. Its node has only the prescribed new-definition fields, and the assigned
item gains this id in stmt_deps; every other preexisting field is preserved.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
