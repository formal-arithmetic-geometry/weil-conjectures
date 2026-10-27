## Worker report

The module `Sheaf.Algebra.Lie.ChevalleyOppositeRationalCollection` states
`LieAlgebra.ChevalleyCollection.exists_opposite_rational_collection`, with its
whole proof `sorry`. Six helper definitions supply real, canonical data for the
same node's constructions; there are no further postponed theorems. No natural
language statement, dependency list or proof plan has been changed.

Hypotheses, clause by clause:

- The rational vector space is `V`, with `AddCommGroup`, `Module ℚ` and
  `FiniteDimensional` instances. Roots and coroot functionals are `R` and `c`.
  `hfinite`, `hne`, `hspan`, `htwo`, `hint`, `hreflect`, `hreduced` are respectively
  finiteness, nonzero roots, spanning, normalization 2, integral Cartan integers,
  reflection permutations, and the reduced-line intersection axiom. These are the
  same explicit conventions as the two recorded rational root-system interfaces.
- `P` and `hP` specify exactly the integral-value weight lattice, rather than an
  arbitrary chosen lattice or a lattice of a smaller isogeny type.
- The rational semisimple Lie algebra is `g` with `HasTrivialRadical`; `H`,
  `IsLieAbelian H`, `hmax`, `θ`, `e`, `he`, `hdecomp` express the splitting Cartan,
  its maximal abelianness and dual identification, the nonzero root vectors with
  their eigenvalues, and the Cartan plus one-dimensional root decomposition.
- The simple base is `b : Module.Basis (Fin r) ℚ V`; `hb` puts it in `R` and
  `hbase` asserts integral coordinates of uniform sign for every root. The
  Chevalley basis is `B`, with values fixed by `Bh` and `Be`. `hopp`, `hadd`, and
  `hzero` state the opposite-root bracket, root-string constant with sign ±1 and
  maximal string length, and vanishing when the nonzero sum is not a root.
  These conditions are transcribed from the recorded admissible-representation
  declaration, not replaced by a weaker arbitrary family of nilpotent matrices.
- The representation is the actual `LieModule ℚ g W`, with finite dimensionality
  and `LieModule.IsFaithful`. `Λ` has the recorded `Submodule.IsLattice ℚ` and
  `Module.Free ℤ` structures. `Ω`, `hΩP`, `hΩne`, `hW`, `hgenerate`, `hΛ` specify
  the finite integral weights, nonzero weight spaces, rational weight direct sum,
  generation of all of `P`, and integral weight direct sum. `latticeWeightSpace`
  is literally the intersection with the recorded `LieModule.weightSpace`.
- `n` and `hn` choose an arbitrary nilpotence exponent of each root operator.
  This is the witness form of the given `IsNilpotent` condition; no bound or
  uniform extra restriction is imposed. `hstable` is preservation by every
  rational divided power, including exponent zero.
- `β` enumerates exactly roots whose simple coordinates are nonnegative, so its
  length `N` is their cardinality. `horder` orders them by nondecreasing sum of
  coordinates. `negative` with `hnegative` labels their actual negatives, without
  depending on a chosen negation function or adding any new root-system axiom.
- `F` has independent universe `t`, `Field F`, `IsAlgClosed F`. There is no
  characteristic-zero assumption, characteristic exclusion, or reduced test ring.

Conclusions and their precise affine interpretation:

- `d : MvPolynomial (Fin N ⊕ Fin N) F` uses `Sum.inl` for the a coordinates and
  `Sum.inr` for b. `hd` asserts exactly `d(0,0)=1`.
- `A B : Fin N → Localization.Away d` are the coordinate functions of the two
  morphisms from `Spec F[a,b,1/d]` to `Spec F[X_1,...,X_N]`. Their contravariant
  coordinate maps are `MvPolynomial.aeval A` and `MvPolynomial.aeval B`, and their
  scheme maps are `Spec.map` of these algebra maps. Thus this is a morphism
  statement, not a statement only about rational functions or field-valued points.
- `h : AddMonoidAlgebra F P →ₐ[F] Localization.Away d` is exactly the coordinate
  map of the morphism into `T=Spec F[P]`. The existing additive monoid algebra
  has basis `single μ 1` and the prescribed multiplication. Its group-like Hopf
  structure is equivalently the character-group functor of points: each basis
  element is a unit with inverse `single (-μ) 1`. No arbitrary torus or map into
  the full diagonal group is substituted.
- `latticeDividedPower` restricts the actual rational divided power using
  `hstable`. `rootExponential` tensors these integer operators and sums their
  scalar multiples up to `n`. By `hn` the omitted terms are zero, so this is
  exactly equation (153), not exponential division in positive characteristic.
  The tensor convention is `C ⊗[ℤ] Λ`, canonically symmetric to `Λ ⊗[ℤ] C`.
- Each `List.ofFn ... |>.prod` is in the prescribed order. The displayed equality
  is exactly `p_+(b) * p_-(a) = p_-(A) * h * p_+(B)` as endomorphisms of the
  universal base-changed lattice. `torusAction` is the finite sum of the actual
  weight projections, scaled by `h(single μ 1)` on the μ weight summand.
  Its construction uses the inverse of the canonical direct-sum isomorphism,
  not an arbitrary decomposition or a choice from an unproved existence result.
- `origin` is the canonical `IsLocalization.Away.liftAlgHom` extending zero
  evaluation; `hd` supplies the required unit. The next conjunct asserts A=B=0
  at that point; the following conjunct asserts h=1 on every weight monomial,
  i.e. precisely the torus identity point.
- Equality over the universal coordinate algebra is equality of matrix-valued
  morphisms. For any commutative F-algebra C of any universe and parameters with
  d(a,b) a unit, `IsLocalization.Away.liftAlgHom` extends their evaluation, and
  applying it gives the displayed identity over C. This does not require that
  C be reduced or a domain. `torusAction` and `rootExponential` are defined for
  arbitrary commutative coefficient rings, with independent universes.
- The final implication explicitly supplies the empty-root choice d=1, zero
  coordinate tuples, and the constant-one character. The empty products are
  identities; `R=∅` forces `N=0`, `V=0`, and `P=0`. No nonempty index or nonzero
  lattice hypothesis has been added. No generated group, reductivity conclusion,
  or open-immersion assertion occurs.

Dependency declarations read and used:

- `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding`:
  `RootDatumLattice.lattice_embedding` and its explicit rational coroot, root-span,
  and weight-lattice definitions. This module is publicly imported through the
  recorded admissible-representation module; the arbitrary V version uses that
  module's same explicit root-system axioms, not a newly defined root system.
- `Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation`:
  `LieAlgebra.exists_chevalley_admissible_representation`; its full signature and
  proof docstring supply the exact input conditions, repeated as binders since
  this item concerns all such data, not only a chosen existential witness.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` and `Field` (the latter
  from `Mathlib.Algebra.Field.Defs`). The algebraic-closure node's recorded
  `AlgebraicClosure` is for a chosen closure; here only its recorded `IsAlgClosed`
  component is needed.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, and their `GrpObj` convention;
  the conclusion is the affine coordinate version of the stated morphisms and
  uses no subgroup assumption. `Mathlib.CategoryTheory.Monoidal.Grp.GrpObj`
  is the recorded general group-scheme convention.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `additive`,
  `multiplicative` read for the standard affine group convention. The polynomial
  parameters are the underlying affine coordinates of the additive groups.
- `Mathlib.RingTheory.Localization.Away.Basic`:
  `Localization.Away`, `IsLocalization.Away.liftAlgHom`; the recorded
  monoid-localization abbreviation has the ring structure from this import.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map` for the exact affine
  contravariant interpretation, available through the group scheme imports.
- Proof imports: `Sheaf.Algebra.Lie.KostantIntegralPBW`, declaration
  `LieAlgebra.exists_kostant_integral_pbw_basis`, and
  `Mathlib.LinearAlgebra.RootSystem.BaseExists` for the recorded
  `RootPairing.Base.mk'`, `toWeightBasis`, `toCoweightBasis`,
  `span_int_root_support`, `span_int_coroot_support` match. The two proof-only
  nodes `lem-sfb-chevalley-unipotent-polynomial-coordinates` and
  `lem-sfb-block-gauss-scheme-chart` have no recorded modules at inspection,
  so there is no import to add for them. Neither is a statement prerequisite.

Searches made (the msearch wrapper also records its raw output in searches.jsonl):

- LeanFinder: "Opposite Chevalley root exponential products have a rational Gauss
  factorization regular near zero over arbitrary characteristic". Eight hits,
  mostly Witt polynomial denominator clearing and Lindemann-Weierstrass polynomial
  approximation, none matches.
- Loogle: "DirectSum.IsInternal, LinearMap.baseChange, IsNilpotent". Zero hits.
- LeanSearch: "Chevalley root subgroup Gauss decomposition of opposite unipotent
  products near the identity". Eight opposite-subgroup identities, none matches.
- msearch grep: "chevalley|Chevalley|rootExponential|weightTorus". Twenty-five
  hits concern Chevalley's constructible-image theorem and Lie Jordan-Chevalley
  decomposition, not opposite root products.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `rootExponential`, `weightTorus`, `opposite_rational`, and opposite collection:
  no existing statement or helper. A broader Chevalley search found the recorded
  admissible-representation and integral-model modules; the latter concerns an
  integral group model rather than this local matrix identity.
- `rg` in `dag/lean_names_upstream.json` and both libraries for the introduced
  names found no conflicts. Direct source reads located `LinearMap.restrict`,
  `LinearMap.baseChange`, `DirectSum.component`, `DirectSum.coeLinearMap`,
  `LinearEquiv.ofBijective`, `MvPolynomial.aeval`, `AddMonoidAlgebra.single`,
  and the localization lift used for real helper constructions.

Edge cases checked before writing: empty roots and zero rational vector space;
N=0 and empty ordered products; zero-dimensional representation (nilpotence bound
zero is then permitted and its endomorphism ring has 0=1); zero weights in Ω;
negative weight integers; m=0 divided power; arbitrary nilpotence bounds; positive
characteristics 2 and 3; nonreduced F-algebras; unrelated universes for root space,
Lie algebra, representation, field and helper coefficient algebra. No statement
fault or disputed mathematical claim was found. The original agent-expanded proof
and Milne pp.510--511 were read; the seven proof steps are included in the theorem
docstring.

Validation: scompile.py compiled both its sandbox and named-library probes cleanly
on the server (21.1 s and 3.6 s in the final initial run). The only postponed
proof is the main theorem; all helper data are fully constructed.

## Second reading by Q87

Re-read the node and full file after compilation. Checked the individual root-system
axioms, the simple-basis sign and integral conditions, every Chevalley bracket,
faithfulness, both weight decompositions, the integral lattice and divided powers,
the full weight lattice and its generation, and the prescribed positive-root order.
The conclusion uses the universal localization, not merely field-valued solutions;
the torus point comes from F[P], not from the full diagonal torus. Checked the
left/right parameter convention and product order against the displayed formula,
both zero normalizations, arbitrary characteristic and nonreduced evaluation, and
the explicit empty-root choice. Fixed a parser issue by moving `open Classical in`
before the docstring and renaming a reserved lambda token. Fixed the elaborator's
decidable-equality mismatch by exposing `[DecidableEq ι]` on the projection and
torus-action helpers; all mathematical inputs and conclusions are unchanged.
