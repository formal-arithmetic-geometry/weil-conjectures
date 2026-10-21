## Worker report

The module `Sheaf.AlgebraicGeometry.PicardRiemannRoch` states the whole node as
`AlgebraicGeometry.Scheme.picard_riemannRoch`. Its conclusion is the explicitly defined
`picardRRConclusions`, which supplies derived Noetherian and regular instances internally.
The theorem has exactly one `sorry`. All five helper definitions have actual bodies.
The item statement is unchanged. Two new definition nodes record existing upstream
constructions; no new Lean definition is introduced for them.

The current blueprint unit and its `sk-thm-picard-rr-duality.md` detail were read locally.
The item is itself the unit statement; its statement remains unchanged.

Clause-by-clause comparison:

- The field is `(k : Type u) [Field k]`; the curve is `(C : Scheme.{u})` with
  `[C.Over (Spec (.of k))]`, `[IsSmoothProjectiveCurve (C ↘ Spec (.of k))]` and
  `[GeometricallyConnected (C ↘ Spec (.of k))]`. The upstream curve class includes
  integral, dimension one, finite type, separated, smooth and projective. Neither
  algebraic closedness nor perfectness is assumed. The parenthetical proper-to-projective
  observation is covered by the imported `ProperProjective` proof dependency.
- The genus is `arithmeticGenus k C`, defined upstream as `finrankH k O 1`.
  Every genus expression in integer formulas is explicitly cast to `ℤ`.
- The invertible sheaf is quantified as `∀ (L : C.Modules) [L.IsInvertible]`.
  `L.eulerChar k = L.degree k + 1 - (arithmeticGenus k C : ℤ)` is line-bundle RR.
  The next equality records `chi = h0 - h1` using upstream `finrankH`.
- `Function.Bijective (Modules.cupPairing (picardRRResidueTrace k C) L)` states
  that the actual trace-pairing map `H0(L-dual tensor omega) → H1(L)-dual` is an
  isomorphism. Inverting it and applying tensor symmetry gives exactly the displayed
  `H1(L)-dual ≃ H0(omega tensor L-inverse)`. This uses the dependency's sheaf dual,
  which is the tensor inverse for an invertible sheaf. No arbitrary pairing or
  unnormalized existence of an isomorphism replaces the trace pairing.
- `relativeDifferentials.degree k = 2 * (arithmeticGenus k C : ℤ) - 2` is the
  canonical degree formula. The canonical module is exactly `relativeDifferentials`.
- Strict large degree is `2*g-2 < L.degree k`. Its conclusion is
  `Subsingleton (L.H 1)` and the integer equality for `L.finrankH k 0`.
  Subsingleton expresses zero of a vector space without imposing an `IsZero`
  structure on its underlying type.
- For every finite closed-point divisor `D`, an isomorphism `D.associatedModule C ≅ L`
  implies `L.degree k = D.sum (fun x n ↦ n * f.degreeOver x.val)`.
  `degreeOver` is the residue-field degree, so nonrational closed points are weighted.
  A separate universally quantified principal-divisor clause says this weighted sum
  is zero for `C.div (Additive.ofMul f)` for every nonzero rational function `f`.
  Thus the cohomological degree used elsewhere is explicitly identified with the
  divisor degree, not substituted for it without a comparison.
- For every `F.IsQuasiCoherentFiniteType`, the conclusion is
  `F.eulerChar k = (torsion F).finrankH k 0 +
  (exteriorSheaf (torsionQuotient F) F.rank).degree k + F.rank*(1-g)`.
  The upstream rank is the function-field dimension of the generic stalk; torsion
  is the sheaf of locally torsion sections (the generic-stalk kernel on an integral
  scheme), and torsionQuotient is its cokernel. The dependency's sectionwise
  sheafified exterior power is used for the determinant, including rank zero.
  This expands exactly the node's coherent degree formula.
- `∀ (K : Type u) [Field K] [Algebra k K], picardRRFieldExtension k C K` records
  the field-extension clause. This predicate asserts smooth projectivity and geometric
  connectedness of `C_K`, equality of genus, equality of line-bundle degree and Euler
  characteristic, and bijectivity of the canonical cohomology comparison in every degree.
  It also gives the canonical isomorphism of the pulled-back differential sheaf with
  `omega_{C_K/K}`, specified by `1 tensor da → d(p-sharp a)` on all opens and sections.
  Finally the residue trace of the image of every `z ∈ H1(omega)` equals the scalar
  image of its original residue trace. The isomorphism of differential sheaves is
  therefore specified by universal differentials, and trace compatibility is an
  equation of the actual canonical maps. Naturality of cup product and evaluation
  then gives exactly scalar extension of the trace-duality isomorphism, rather than
  just an equality of dimensions.
- Complement (G) is `0 < L.degree k → IsAmple (C ↘ Spec (.of k)) L`.
- Complement (H) separately quantifies an arbitrary proper `k`-scheme `X`, an ideal
  `J : X.IdealSheafData` and `J.IsInvertible`, together with ampleness of
  `J.toModulesᵛ = O_X(D)`. It concludes affineness of `J.support.compl.toScheme`.
  It is not restricted to curves, nonempty divisors or reduced schemes.

Canonical transports:

`picardRRResidueTrace` specializes existing `residueTrace` to `functionFieldAlgebra`,
with `isFunctionFieldAlgebra_functionFieldAlgebra`; no extra algebra hypothesis is added.
`picardRRPullbackIso` uses the existing `tensorPullbackSectionAdjunction p`, owned
by `def-pc-module-pullback`, and compares it with `pullbackPushforwardAdjunction p`
by `leftAdjointUniq`. The owning definition chooses the unique adjunction whose unit
is the actual inverse-image/tensor/sheafification section `1 tensor m`. The module
publicly imports `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`; there
is no independent choice of an adjunction in this delivery.
`picardRRBaseChange` composes the existing `H.baseChange` with the cohomology map of
this comparison's inverse, so every geometric pullback in the statement uses the
required tensor pullback. The legacy pullback occurs only in this canonical API bridge.
The displayed `HOver` target retains the base-change structure morphism and hence its
canonical coefficient action. The local instances in definition bodies are proved,
canonical facts; there is no file-local instance and no `let` binder in the theorem.

Dependency declarations read and used (module abbreviations below start with
`WeilConjectures.AlgebraicGeometry` unless another root is written):

- `Curve.SmoothProjective`: `IsSmoothProjectiveCurve` and its parent curve classes.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` and `.Connected`:
  `GeometricallyIntegral`, `GeometricallyIrreducible`, `GeometricallyReduced`,
  `GeometricallyConnected`. The geometric-connectedness class is imported explicitly.
- `Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Cohomology.EulerChar`: `Scheme.arithmeticGenus` and `Scheme.Modules.degree`.
- `Cohomology.Defs`: `Scheme.Modules.H`, `finrankH`, `eulerChar`, `H.mapLinearMap`.
- `Modules.Differentials`: `Scheme.Hom.relativeDifferentials` and its universal derivation.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree` and `IsFiniteLocallyFreeOfRank`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`: `Scheme.Modules.exteriorSheaf`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`.
- `EffectiveCartier`: `J.toModulesᵛ`, `Scheme.Modules.dual` and the associated
  invertibility theorem, exactly the recorded divisor-line-bundle convention.
- `Modules.VeryAmple`: `AlgebraicGeometry.IsAmple`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.RegularCurveDivisorCalculus`:
  `Scheme.regular_curve_divisor_calculus`, using `Divisor.associatedModule`.
- `Modules.Torsion`, `Modules.GenericRank`: `torsion`, `torsionQuotient`, and
  `rank`, now owned by `def-pc-module-torsion-generic-rank`.
- `Curve.ResidueTrace`: `Scheme.residueTrace`; `Cohomology.CupProduct`:
  `Scheme.Modules.cupPairing`; `Curve.AdelicStructureSheaf`:
  `functionFieldAlgebra`, `isFunctionFieldAlgebra_functionFieldAlgebra`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`, with the publicly imported
  upstream `Scheme.Modules.tensorPullback`, owned by `def-pc-module-pullback`.
- `Cohomology.FlatCohomologyComparison`: `HOver`, `H.baseChange`,
  `baseChangeFst`, `baseChangeSnd`; this existing node was added to statement dependencies.
- `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `Hom.relativeDifferentialsPullbackGenerator`; this landed node was added to statement
  dependencies. The existing degree node was also added to record reuse.
  `lem-sc-riemann-roch` has been dropped: it owns numerical theorems rather than
  the torsion and generic-rank definitions used by this statement.
- All recorded proof-dependency modules are imported privately, including arbitrary-field
  proper-to-projective, zero-dimensional-support, torsion, determinant, separation,
  base-change and ample-complement inputs. The unstated `sk-thm-picard-duality` and
  `det-picard-rr-duality` have no module to import; their already-existing upstream
  trace definitions are used directly, and their content is incorporated in the package.

Edge cases checked before and after writing:

Genus zero uses integer `2*g-2 = -2`, including degree -1; there is no natural-number
subtraction truncation. In genus one the vanishing threshold is strict positive degree.
Rank-zero coherent torsion sheaves use the zeroth exterior power, whose value is the
structure sheaf. Negative divisor coefficients and nonrational closed points remain
in the weighted finite sum. No perfectness or separability assumption excludes inseparable
residue fields: the existing trace is Tate's residue trace. The identity field extension
and arbitrary algebraic or transcendental extensions are quantified. The empty curve
is excluded by the node's curve hypotheses, while the arbitrary proper scheme in (H)
may be empty. The empty divisor is included whenever its associated module is ample.

Searches:

- `msearch.py ... leanfinder "Riemann Roch and Serre duality for smooth projective curves"`:
  eight hits on Weierstrass affine ideals/points and function-field class numbers;
  no general scheme RR/Serre-duality package.
- `msearch.py ... loogle '"eulerChar"'`: twelve graded-object/complex Euler-characteristic
  hits; no scheme RR package.
- `msearch.py ... grep 'RiemannRoch|SerreDuality|riemann_roch'`: zero Mathlib hits.
- `rg` for RR, Serre duality, canonical degree, torsion, coherent degree and generic rank
  in `lean/WeilConjectures` and `lean/Sheaf`, and the item-id grep in upstream:
  found `Curve.RiemannRoch`, `Curve.RiemannRochCoherent`, `Curve.ResidueTrace`,
  `DivisorModule`, the existing torsion/rank modules, the regular-curve divisor calculus
  and the relative-differential generator. Their signatures and docstrings were read.
  Existing upstream individual numerical formulas do not state this complete node,
  notably the normalized field-extension compatibility with both complements.

No `STATEMENT-DISPUTED` issue was found. The mathematics was accepted by the
immutable-head review; this repair addresses its ownership and record-preservation faults.

## New nodes

`def-pc-module-torsion-generic-rank` records the existing definitions
`AlgebraicGeometry.Scheme.Modules.rank` (`Modules.GenericRank`), `torsion` and
`torsionQuotient` (`Modules.Torsion`). The source is the coherent complement in
`sk-thm-picard-rr/_section.md`: the torsion kernel, its quotient, and generic-stalk
rank. The primary module publicly imports the other owning module. These plain
upstream definitions had no owning DAG definition node; the numerical theorem node
`lem-sc-riemann-roch` did not own them. The new node introduces its own integral
scheme, module, generic point and function field. Dense-open vanishing agrees with
the generic-stalk kernel on an integral scheme. The rank is Mathlib finrank, with
its stated zero convention for infinite dimension; the item's coherent modules have
finite generic rank. Searches found Mathlib algebraic module torsion/rank results
but no matching sheaf constructions. The existing project constructions are reused,
with `existing: true`, and no module is copied or rewritten.

`def-pc-residue-trace-pairing` records `Scheme.residueTrace`
(`Curve.ResidueTrace`), `Scheme.Modules.cupPairing` (`Cohomology.CupProduct`), and
`Scheme.functionFieldAlgebra` with its compatibility lemma
(`Curve.AdelicStructureSheaf`). It defines the canonical structure-morphism algebra
on the generic stalk, the residue sum on differential principal-parts classes, and
the cup-product/evaluation pairing followed by that trace. The source is the unit's
trace-duality clause, as expanded in `sk-thm-picard-rr-duality.md` clauses (1) and (4).
The record asserts no perfectness. Its primary module publicly exports the other
owning modules. Searches found algebraic trace forms, trace-dual bases and contraction
maps, but no matching curve cohomology trace pairing in Mathlib. The project already
constructs all three objects; the new node only records ownership, with `existing: true`.

For both nodes the search record includes the actual msearch LeanSearch, LeanFinder,
Loogle and Mathlib grep queries. The combined grep query was
`residueTrace|cupPairing|torsionQuotient|functionFieldAlgebra` under `AlgebraicGeometry`:
its single Mathlib hit was `stalkFunctionFieldAlgebra`, not these constructions.
Loogle `torsionQuotient, cupPairing, residueTrace` returned zero hits and reported
unknown identifier `torsionQuotient`. LeanSearch torsion results included
`Submodule.torsion'`, `Submodule.torsion_isTorsion`, and rank-zero/torsion lemmas;
LeanFinder included `Module.rankAtStalk` and `ModuleCat.Tilde.smul_stalk_no_nonzero_divisor`.
The trace queries returned `Algebra.traceForm`, trace-dual basis lemmas,
`LinearMap.trace_eq_contract`, and `LinearMap.IsPerfPair.dualEval`.
`rg` over the DAG, upstream and Sheaf found the owning source definitions but no
owning definition node. `blueprint_refs.py search 'generic rank'` and
`search 'residue trace'` found zero blueprint nodes; `search 'torsion subsheaf'`
found only the numerical theorem `lem-sc-riemann-roch`.

## Repair of immutable head 2b5c537b83d2

R1: removed the added `lem-sc-riemann-roch` statement dependency. The item now cites
`def-pc-module-torsion-generic-rank` and publicly imports `Modules.GenericRank` and
`Modules.Torsion` directly. The unnecessary public `Curve.RiemannRochCoherent`
import was removed. The private `Curve.RiemannRoch` import remains because the
original proof dependency `lem-pc-vanishing-above-dim` owns
`Modules.subsingleton_H_of_two_le` there.

R2: added `def-pc-residue-trace-pairing`, and the existing nodes
`def-pc-module-pullback` (the canonical section-normalized adjunction and tensor
pullback used by `picardRRPullbackIso`; corrected by the later review below), `sk-def-zeta`
(`Scheme.Hom.degreeOver`), and `def-sc-divisor` (`Scheme.Divisor`, `Scheme.div`,
`Divisor.associatedModule`). Their actual upstream construction modules are used;
there is no private copy of the definitions. The divisor-associated module is the
upstream copy exported by `RegularCurveDivisorCalculus`, following the duplicate
retirement rule, and divisors/principal divisors are imported from `Curve.Divisor`.

R3: deleted the delivered `pqf-def-coherent` node copy, so the live node and its
Q25 `IsQuasiCoherentFiniteType` record are preserved byte for byte. The item's
module now publicly imports `Sheaf.AlgebraicGeometry.CoherentFiniteType` and the
coherent RR clause uses `F.IsQuasiCoherentFiniteType`. The predicate unfolds to
`SheafOfModules.IsQuasicoherent F ∧ SheafOfModules.IsFiniteType F`. On this
Noetherian curve it is equivalent to coherence, including the finite-type-kernel
condition. No claim is made that it replaces that condition on arbitrary schemes.
No global dependency interface or any of its six consumers is changed.

## Second reading by NQ

The dispatcher explicitly prohibited starting other agents; no independent worker reading
is claimed. The maintainer supplies the independent review under the dispatch brief.
A second self-check with the source unit and the complete module open checked every clause
against the mapping above. It caught the scalar-action requirements of residueTrace,
the base-change structure instance, the need to transport legacy cohomology output to
tensor pullback, and the importance of using the unit-pinned adjunction theorem rather
than a bare Nonempty adjunction. These were repaired before delivery. The theorem's
statement contains no extra regularity, Noetherianity, function-field algebra or global
sections hypothesis; those are derived inside the transparent definitions.

Validation: `scompile.py` checks the sandbox and its actual library module separately.
The final source also passes the per-file compilation performed by `deliver2.py`.
The first preflight found an existing-record branch label mismatch (`sheaf-dag`
instead of the required `slopmaster2` for a WeilConjectures declaration); it was repaired.

Repair self-check: re-read the retained module and current unit, the three return
points, the current pqf record and CoherentFiniteType definition, and the full
signatures/docstrings of rank, torsion, torsionQuotient, residueTrace, cupPairing
and functionFieldAlgebra. Checked zero module, rank zero, finite-dimensional
generic stalks, canonical scalar structure, and the residue-theorem quotient.
The line-bundle, divisor, field-extension, genus-zero and arbitrary-proper-scheme
clauses retain the previously accepted formulas. The new nodes cite exactly the
notions they use. Only lean and added stmt_deps differ from the current item.

Repair dry-run: the first repaired packet was refused only because both new nodes
had a nonempty blueprint.from.via for this direct blueprint unit. Set both to the
required empty list. The existing-record signatures were also normalized to the
server extractor’s `def` signatures. The earlier R2 adjunction-theorem citation was superseded by the later ownership
repair below.

## Repair of immutable head 872d46cafd32

H4/H2: replaced the statement dependency `lem-pc-module-pullback-adjunction` with
`def-pc-module-pullback`, the reviewed owner of both `tensorPullback` and its
canonical section-normalized adjunction. Publicly imported
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` in place of
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`. The comparison is now
exactly `(Modules.tensorPullbackSectionAdjunction p).leftAdjointUniq
(Modules.pullbackPushforwardAdjunction p)`. Its docstring and the dependency list
above describe that existing construction. No definition is duplicated and no
choice of an existence-only adjunction remains in this module.

Read the owner's current node record and complete module, including the section
formula, existence-and-uniqueness signature, canonical adjunction body, and the
identity/composition comparisons. The unique normalization fixes the unit on
every section, so this replacement supplies the same canonical base-change
transport for identity and arbitrary field extensions. The mathematical clauses,
helper signatures, theorem signature and two existing:true nodes are retained
from the reviewed packet. Compared the saved item with current shared main:
only `stmt_deps` and `lean` differ. The required initial saved-packet dry run passed
(preflight and both per-file compiles); the substantive repair above follows it.

Repair validation: `scompile.py NQ sk-thm-picard-rr` compiled the repaired file
as both `Sheaf.Stage2.Sandbox0` and
`Sheaf.AlgebraicGeometry.PicardRiemannRoch` cleanly (5.7 s each). Rechecked the
verbatim theorem signature, explicit universe/variable bindings, unique dependency
ids and 100-character line limit. The current blueprint unit and duality detail
were read again; genus zero, rank zero, empty divisor and arbitrary proper scheme
cases retain the accepted clauses. The canonical comparison has no extra
hypothesis and uses the owner's unique section normalization.
