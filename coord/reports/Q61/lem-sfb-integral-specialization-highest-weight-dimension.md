## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.IntegralSpecializationHighestWeightDimension`
states `AlgebraicGeometry.integral_specialization_highest_weight_dimension` with one
postponed proof (`sorry`) and no new definitions. The original natural-language statement
and proof are unchanged. The two additional statement dependencies are existing landed
notions: `def-sfb-rational-highest-weight-data` and `def-sfb-semisimple-group-scheme`.
No dependency interface needs repair and no new node is introduced.

Sources read: Milne, Algebraic Groups (2017), Theorem 22.52, printed p.480;
Theorem 22.53, p.481; Section 23h, pp.509--511, especially the admissible lattice,
(152), (153), Theorem 23.72 and Corollary 23.73. The erratum on p.480 explicitly
restricts the simple-representation character formula to characteristic zero.
The docstring follows all ten accepted proof steps: rational root data and auxiliary
faithful representation; rational highest-weight module and characteristic-zero
formula; cyclic integral PBW lattice; finite homogeneous generation and primitive
top summand; finite-free reduction preserving rank and top vector; root-exponential
action; root-datum identification with G; all-algebra Borel eigenline;
trivial character on the radical; assembly and rank zero. The statement does not
use positive-characteristic simplicity or identify W with an induced module.

Hypothesis and clause correspondence:

- `[Field F] [IsAlgClosed F]` gives the algebraically closed field. `(p : ℕ)` with
  `[Fact p.Prime] [CharP F p]` specifies precisely prime positive characteristic.
- `G : Grp (Over (Spec (.of F)))` is the actual F-group scheme, with its multiplication,
  identity and inverse. `hG : IsSemisimpleGroupScheme G.X` includes smoothness,
  connectedness, affineness, finite type and triviality of every smooth connected
  solvable normal closed subgroup. Its solvability predicate is termination of
  the scheme-theoretic commutator series.
- `hsc` quantifies every semisimple F-group scheme G' and group homomorphism f.
  `Surjective f.left` is surjectivity, `IsFinite (GrpObj.ker f).hom` is finiteness
  of the scheme-theoretic kernel, and the equality of products for every test
  F-algebra A says that kernel is central scheme-theoretically. `IsIso f` is
  exactly the required isomorphism. The kernel is the actual categorical kernel,
  not the kernel on F-points.
- `T`, `B`, `iT`, `iB`, `j`, `hj` give the torus and Borel inclusions with
  T contained in B. `hT` is maximal torus, `hsplit` is an isomorphism with an
  actual `MultiplicativeType.splitTorus F r` for arbitrary natural r (including 0),
  and `hB` is a maximal smooth connected solvable closed subgroup.
- The two `IsCommMonObj` witnesses expose the abelian Hom-group structures from
  the Borel-pair theorem. `aG`, `aB`, `haG`, `haB` pin tangent actions to the
  conjugation maps of these actual inclusions.
- `Φ` is a finite set of actual torus characters, written additively.
  `P : RootDatum Φ ...` uses actual additive character and cocharacter Hom groups.
  `[P.IsReduced]` and `b : P.Base` give the reduced root datum and simple base.
  `hroot` fixes root vectors as their character values; `hpair` fixes the integer
  pairing by composition with the integer power morphism; `hweights` specifies
  exactly all nonzero tangent characters of G. `hpositive` says the positive
  roots are precisely the characters in Lie(B). Thus arbitrary combinatorial
  root data or differentials of characters cannot replace the specified data.
- `[IsAffine G.X.left] [IsAffine B.X.left]` register the affine structures needed
  by the canonical coordinate-Hopf API. They add no mathematical restriction:
  affineness is in hG, and the closed immersion in hB makes B affine over G.
- `U`, `iU`, `hU` specify the largest smooth connected normal unipotent closed
  subgroup of B, by factorization of every such inclusion, exactly R_u(B).
  The same radical specification is the conclusion of the recorded Borel-pair
  theorem, so this is presentation data rather than an extra group restriction.
- `eta` is in the actual character lattice. `hdom` is nonnegative integer pairing
  with every simple coroot (`α ∈ b.support`), including equality on walls.
- `etaB` is the group-scheme extension to B; `hetaB` fixes its restriction to T
  and `hetaU` its trivial restriction to U. These are precisely the stated extension
  trivial on the radical. The identity `1` here is the trivial character morphism.
- `ρ` is in the rationalized character lattice. `hρ` fixes it to half the finite
  sum of positive roots, using `1 ⊗ root` and rational scalar multiplication.
  Tensor symmetry canonically identifies Q tensor_Z X with X tensor_Z Q.
- `((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot' α)).liftBaseChange ℚ`
  is exactly rational extension of the integer coroot functional, not a selected
  functional or an independent root pairing.
- The first conclusion says each positive-root denominator is a positive natural
  number cast to Q. This renders the node's explicit positive-integer-denominator
  clause and excludes reliance on division-by-zero conventions.
- The existential `W : Type u`, `AddCommGroup W`, `Module F W`,
  `FiniteDimensional F W` gives the requested finite-dimensional vector space.
  This universe loses no existence cases: any finite-dimensional module is
  isomorphic to F^n in the field's universe. The linear map c together with
  `HopfAction.Coassociative` and `HopfAction.Counital` is exactly the stipulated
  rational coaction into W tensor_F F[G], with its canonical coordinate Hopf maps.
- `∃ v, v ≠ 0` is the nonzero vector. The equation
  `(coordinateMap iB).toLinearMap.lTensor W (c v) = v ⊗ₜ[F] characterElement etaB`
  is the required identity after restriction to B. `coordinateMap` is the actual
  pullback of regular functions, and `characterElement` pulls back the Laurent
  coordinate along etaB. Evaluating this tensor identity at any algebra-valued
  point gives the displayed eigenvector identity. Conversely its universal
  coordinate-valued point detects the identity. Hence every scalar extension,
  including rings with nilpotents, is included without a point-density assumption.
- The final equality casts `Module.finrank F W` to Q and takes the finite product
  over exactly `b.IsPos`. Its numerator is the rational coroot pairing at
  `1 ⊗ eta + ρ` and denominator the same pairing at ρ. No cast to F occurs.
  The empty product is the ordinary Mathlib empty product, namely 1.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, full class signature and docstring at 172--180.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, full class and root-equivalence
  docstring at 58--64 (the recorded algebraic-closure leaf includes this predicate).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, `Grp.Hom`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` supplies their scheme
  specializations and the actual kernel, closedness and finiteness terminology.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`. The full signature/docstring
  was read. The input root actions, root/pairing/weight equations, and radical
  maximality specification repeat the interface of its conclusion rather than
  defining a second notion.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `AlgebraicGeometry.IsSemisimpleGroupScheme`, `IsSolvableGroupScheme`,
  `GroupSchemeDerivedLength`, and `IsDerivedGroupScheme`; full definitions read.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `coordinateAlgebra`, `coordinateHopf`, `coordinateOverGroup`, `coordinateMap`,
  `characterElement`, all in `AlgebraicGeometry.RationalHighestWeight`; full
  signatures and docstrings read. Rationality is reused from `HopfAction.Coassociative`
  and `HopfAction.Counital` in `Sheaf.RingTheory.HopfActionModuleData`, whose
  associator/comultiplication and counit equations were read.
- Mathlib `RootDatum`, `RootPairing.Base`, `RootPairing.coroot'`,
  `LinearMap.liftBaseChange`, tensor products, and `Module.finrank` provide
  the integral root datum, rational coroot extensions and ordinary dimension.

All currently stated proof dependencies are imported without `public`:
BruhatLongestCellCharts, ChevalleyAdmissibleRepresentation, KostantIntegralPBW,
RationalHighestWeightModules, RootDatumLatticeEmbedding,
SimplyConnectedCharacterLattice, and Mathlib LinearAlgebra.FreeModule.PID
(`Submodule.basisOfPid` for the free subgroup leaf). The Borel-pair module is
already a public statement import. The remaining proof-only nodes
characteristic-zero-weyl-dimension, chevalley-root-exponential-group,
regular-cocharacter-borel-description, root-datum-isogeny-realization have no
recorded Lean declaration on the input base, so there is no module to import.
No missing statement notion is deferred to those proof-only prerequisites.

Edge cases checked before writing: rank-zero/trivial group (empty roots, empty
simple base, ρ=0, vacuous denominator assertion, product=1 and the trivial
one-dimensional representation); eta=0; dominant weights on walls; SL2 with
highest weight m (the sole denominator is 1 and dimension m+1, even for m ≥ p);
characteristic 2 (all halves and denominators are in Q); nonreduced test algebras
(the equality is of coactions); and product root systems. Zero W is correctly
excluded by v≠0, as the node requires. There is no statement dispute or source
correction: Milne's erratum is respected by using the Weyl formula only before
integral reduction, and the statement makes no simplicity claim about W.

Searches actually run, with results (the wrapper records are in searches.jsonl):

- msearch leanfinder, “A semisimple simply connected algebraic group in positive
  characteristic admits a rational highest weight module with Weyl dimension”:
  eight hits on Lie-module weights, nilpotent/solvable weight spaces, the Weyl-group
  representation and Geck Lie modules; none is this algebraic-group existence theorem.
- msearch loogle, “Module.finrank, Coalgebra, Comodule”: no hits, unknown identifier
  Comodule; it does not supply the required rational representation theorem.
- msearch grep, “highest.weight|Weyl.dimension|RationalModule”: two comments, the
  highest-weight semistandard tableau and an unrelated Lie-basis induction; no match.
- msearch leansearch, “highest weight module rational algebraic group Weyl dimension”:
  eight hits on the Weyl-group module and Lie weight-space decompositions, no rational
  highest-weight algebraic-group module or integral dimension preservation.
- rg of WeilConjectures and Sheaf by the exact item id, integral specialization,
  highest-weight/dimension and coaction/character names: no exact theorem; located
  the reusable RationalHighestWeightData, SimpleModuleDualHighestWeight and
  rational-representation/comodule dictionary. The simple-module theorem has
  neither the positive-characteristic Weyl dimension assertion nor the required
  existence without simplicity. The dictionary constructs no prescribed weight.
- rg of Mathlib RootSystem and project group-scheme/Lie modules for halfSum,
  WeylVector, rho and ρ found the existing RhoRegularWeylOrbit theorem using the
  same pinned half-sum presentation, but no reusable definition or this existence
  statement. The half sum and coroot extension are written using existing tensor
  and linear-map operations, with no second definition. The final declaration
  name was searched in dag/lean_names_upstream.json, Mathlib and WeilConjectures:
  no collision.

Validation: scompile.py compiled the delivered module against the published server
library with exit code 0, no errors and no unexpected warnings. It checked the sandbox
and the final library module (the latter took 11.4 s, below the 60 s file limit).
The preliminary wait for a concurrent compile was scheduling time, not a Lean timeout.
The prescribed deliver2.py --no-push dry run passed both the server preflight and
compilation: “OK (dry run): commit dcf93b5d750 passes the preflight and compiles;
nothing pushed”. A source/record check confirms the signature is verbatim, the
only node fields changed are lean and the two added landed stmt_deps, and the
module has exactly one sorry and a longest line of 95 characters.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
