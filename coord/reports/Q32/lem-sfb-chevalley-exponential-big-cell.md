## Worker report

Module `Sheaf.AlgebraicGeometry.ChevalleyExponentialBigCell` states
`AlgebraicGeometry.ChevalleyExponential.exists_open_cell`, with one postponed proof.
It includes real coordinate constructions for the ordered multiplication map,
character evaluation, integral divided powers, and finite exponential matrices.
Every helper belongs to the construction already described by this node; no
independent notion or new definition node is introduced. The existing landed
`def-sfb-diagonalizable-group` was added to stmt_deps to cite its actual character torus.
The statement, proof, source and all other node fields are unchanged.

Source read: Milne, Algebraic Groups (2017), printed pp.510--511 (PDF pp.522--523),
(152), (153), Theorem 23.72 and Corollary 23.73. The detailed open-cell assertion is
explicitly agent-stated in the DAG, not asserted to be a verbatim theorem of Milne.
The full seven-step DAG proof is transcribed in the theorem docstring.

Clause and hypothesis correspondence:

- Rational V and finite-dimensionality: `V`, `[Module ℚ V]`,
  `[FiniteDimensional ℚ V]`. The finite, nonzero, spanning, normalized,
  integral, reflection-stable, reduced root system is exactly
  `hfinite`, `hne`, `hspan`, `htwo`, `hint`, `hreflect`, `hreduced`.
- The weight lattice is `P : Submodule ℤ V` with the exact membership iff `hP`.
  This matches the admissible-representation dependency's arbitrary rational-V
  interface, rather than imposing the special rationalization of an integral datum.
- The split semisimple Chevalley algebra is `g`, `hss`, `H`, `hab`, `hmax`,
  `θ`, `e`, `he`, `hdecomp`, `B`, `hB`, `hopp`, `hstring`, `hzero`.
  These reproduce the recorded dependency's root-space direct sum, Cartan duality,
  simple coroot basis, opposite brackets, root-string constants, and zero brackets.
  Diagonalizability of adjoint Cartan operators follows from that eigenbasis.
- The faithful finite-dimensional representation is the `LieRingModule`,
  `LieModule`, and `FiniteDimensional` instances on W together with `hfaithful`.
  `LieModule.toEnd ℚ g W` is rho, with no second representation definition.
- The lattice and its decomposition are `Λ`, `hlattice`, `hfree`, `Ω`,
  `hweights`, `hW`, `hgenerate`, `hΛ`. They give the nonzero integral weight
  spaces, full integral lattice, and both rational and integral internal sums.
- Nilpotence is expressed by arbitrary bounds `n` and `hn`; divided-power stability
  is exactly `hdiv`. The explicit integer basis `bΛ` is an arbitrary coordinate
  choice on a full finite free lattice. `dividedPower` restricts the rational
  operator before taking its integer matrix. `exponentialMatrix` reduces integer
  coefficients in the test ring, and never divides by a factorial there.
- The simple-root base is `δ`, `hδ`, `hbase`, and the compatible Chevalley basis
  is `B`, `hB`. Positive roots are precisely `hpositive`. The injected enumeration
  `β : Fin N → R` exhausts them, `ν` labels their negatives by `hν`, and
  `horder` is nondecreasing height. These choices permit every order the node permits.
- F is arbitrary `[Field F] [IsAlgClosed F]`, with no characteristic restriction.
  The scalar extension of Λ is represented in its integral-basis coordinates:
  integer coefficient matrices extended to F act on F^d, canonically Λ tensor F.
  Matrix indices are `ULift.{u} (Fin d)`, so no equality u=0 is imposed.
- T is exactly `(diagonalizableGroup F P).X`, Spec of AddMonoidAlgebra F P,
  with the already existing Hopf structure e^lambda -> e^lambda tensor e^lambda,
  counit one and antipode e^(-lambda). `characterValue` evaluates that basis monomial.
  `tGL` is fixed by the displayed weight-eigenvector equation over every A.
  Its closed-subgroup condition is part of the node's embedding assertion.
- `xGL` is fixed over every commutative F-algebra by the exact finite exponential
  equality using `hdiv` and `n`. Its additive homomorphism law is `IsMonHom`.
  No arbitrary root maps or unexplained comparison is assumed.
- K, its closed inclusion iK, and factorizations tK,xK are existential, with
  `tK ≫ iK = tGL` and `xK a ≫ iK = xGL a`.
  The clause quantifying over J,iJ states minimality among ALL closed subgroup
  schemes containing T and every root image; no reducedness or reductivity occurs.
- The source is `cellSource F P N`, the parenthesized product of polynomial
  N-space, T, and polynomial N-space in Over Spec F. `cellMap` uses ordered
  `List.finRange N` products of the coordinate projections. `IsOpenImmersion`
  is applied to its underlying scheme morphism. The next equation sends
  (0,1,0) to one, hence its image contains the identity.
- The full equivariance equation quantifies over every test algebra A, s,t,a,b.
  Conjugation scales negative coordinates by e^(nu j), positive by e^(beta j),
  and leaves the middle t literally unchanged.
- `v a` is explicitly nonzero and its tangentPoint is xK_a(epsilon*1), so this
  is dx_a(1), with 1 the unit tangent vector at zero of Ga, not a point at one.
- The linear equivalence D is exactly the differential of the chart: its
  tangentPoint is the product of negative epsilon coordinates, the torus
  tangentPoint followed by tK, and positive epsilon coordinates. Under the
  tangent-group addition law this is the direct sum in the node. Bijectivity
  gives both independence of all root axes and the full tangent decomposition.
- The subsequent equation gives every root vector its actual character on
  constant dual-number torus points. The torus tangent is explicitly fixed.
  The final distinct-character clause separates every pair of different roots
  by an F-point of the split torus; over algebraically closed F this is precisely
  distinctness as characters. Characters are never replaced by their differentials.
- For R empty, the source has N=0 and V=P=0. The final clause says tK and the
  chart are isomorphisms. Since the map is literally the empty products times tK,
  this is the identity on the trivial torus under the canonical identifications.
  No spurious W=Q or Omega={0} hypothesis is imposed on arbitrary input data.

Dependency declarations read and used:

- `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding`: `RootDatumLattice.lattice_embedding`,
  its complete explicit reflection axioms and lattice construction; imported publicly
  through `Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation`.
- `Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation`:
  `LieAlgebra.exists_chevalley_admissible_representation`; the exact supplied data
  in its conclusion become universally quantified inputs here. This theorem's
  existence choice is not used to choose an unspecified lattice.
- `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (via dependency imports).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, group laws on Hom;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsSubgroupScheme`, publicly through StandardGroupSchemes.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `additive` and
  its canonical additive group law (the definition node also records Gm).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`: `diagonalizableGroup`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`:
  `GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv` for actual matrix points.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential` and its public
  imports: `GrpObj.Lie`, `GrpObj.tangentPoint`, `points.map`, the tangent-point
  interpretation and existing scalar module. No Lie algebra definition is copied.
- Proof leaves imported privately: `Mathlib.LinearAlgebra.FreeModule.PID`
  (`Module.basisOfFiniteTypeTorsionFree'`),
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` (`Scheme.Hom.image`),
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
  (`IsImmersion.instIsOpenImmersionToImageOfQuasiCompact`).
  Proof-only construction nodes unipotent-polynomial-coordinates, block-gauss-chart,
  opposite-rational-collection, generic-matrix-locus-subgroup-closure have no Lean
  records in the base; their names and arguments are retained in the docstring.
  They are not statement prerequisites and no unstated interface is assumed.

Edge checks: R empty includes arbitrary trivial-representation W and the zero W case;
N=0 gives empty list products and polynomial zero-space; d=0 gives GL(0)=1;
a nilpotence bound zero is allowed exactly for the zero module; a larger bound only
adds zero divided powers. Polynomial test rings are not restricted to fields,
reduced rings or nontrivial rings. In characteristics two and three, divided powers
are reduced from integers and character distinctions are tested on torus points.
All indices and universes are bound explicitly; `autoImplicit` and
`relaxedAutoImplicit` are false. No definitions contain sorry or choice from
underdetermined existence. All proofs remain postponed.

Searches performed with msearch.py (full results in searches.jsonl):

- LeanFinder: "Ordered Chevalley root exponentials and weight torus form an open
  immersion into the generated group scheme": 8 unrelated generic open-immersion hits.
- Loogle: "RootPairing, GeneralLinearGroup": no hits, GeneralLinearGroup unknown
  to that service. Direct source reading found and uses the upstream group scheme.
- Mathlib grep: "Chevalley|chevalley|bigCell": 25 hits on Chevalley-Warning,
  Jordan-Chevalley and constructible images, no root-group open-cell theorem.
- LeanSearch: "Chevalley exponential root subgroup big cell open immersion weight
  lattice": root-system combinatorics and Lie weight spaces, no matching statement.
- rg on lean/WeilConjectures for Chevalley/chevalley/rootExponential/weightTorus:
  constructibility and Beck-Chevalley hits; no such root-exponential construction.
  rg for this node id gave no result there.
- rg on lean/Sheaf found the admissible representation and an integral-root-model
  theorem that assumes an already reductive pinned group and uses this item in its
  proof. It cannot supply the present pre-reductivity construction. Existing
  DiagonalizableGroup, GeneralLinearGroup and tangent interfaces were reused.
- Searched all helper names in the upstream declaration inventory and relevant
  Lie/group-scheme sources. No exact helpers for this ordered map or its integral
  exponential exist. `rootPoint` is merely the composite of existing polynomial
  substitution and a given root morphism; no additive parameter notion is redefined.

No STATEMENT-DISPUTED flag or source-based statement correction is needed.

## Second reading by Q32

The dispatcher prohibits starting other agents. This is a separate in-thread
second pass over the actual node and final file, not a claim of an independent agent.
The maintainer's independent review remains the delivery review.

I checked every block above against the node. The first draft omitted explicit
triviality on the torus tangent and distinctness of the root characters; both are
now stated as point equations. I replaced a redundant additive-parameter helper
with `rootPoint`, the composite already needed for tangent evaluation. Matrix
indices were lifted rather than specializing the field universe. I checked that
(1) character evaluation uses AddMonoidAlgebra.single, not the obsolete Finsupp
encoding; (2) negative and positive lists have the same height order; (3) no
redutivity or smoothness is a hypothesis; (4) the differential uses dual-number
points at zero; (5) K is the smallest closed subgroup scheme, not an abstract
subgroup of F-points. The only postponed theorem is exists_open_cell, with exactly
the node's proof plan. The final module compiles cleanly in both wrapper checks.
