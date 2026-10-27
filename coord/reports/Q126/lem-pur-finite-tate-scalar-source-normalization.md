# Q126: lem-pur-finite-tate-scalar-source-normalization

## Worker report

This stage-2 delivery states the joint normalized finite Tate scalar-source theorem in
`Sheaf.Paper.FiniteTateScalarSourceNormalization`. Its only theorem proof is `sorry`.
Four helpers are transparent aliases or composites of the existing Tate sheaf,
single, shift, unit, scalar tensor, and scalar/pullback maps. Seven further helpers
are transparent predicates displaying the normalization equations. Every definition
contains its full data or proposition.
There are no new independent notions, new nodes, dependency repairs, or statement changes.

The previous worker mistook Q132's stage-1 landing for a completed stage-2 item.
The live node has a seven-step natural-language proof and `reviewed`, but no `lean`
or `reviewed_lean` record. Q132's report explicitly says there were no Lean changes.
This delivery retains that reviewed stage-1 statement and proof.

Hypotheses and objects, matched individually:

- Finite commutative rings A and A': `{A B : Type (u + 1)}` with `[CommRing A]`,
  `[CommRing B]`, `[Finite A]`, `[Finite B]`. The coefficient size is the published
  ModuleCat-valued small-etale convention for `Scheme.{u}`.
- The unital ring map is `(φ : A →+* B)`; it is not assumed flat, injective,
  surjective, or of finite projective dimension.
- The common positive annihilator is `(N : ℕ) (hN : 0 < N)` together with
  `(hA : (N : A) = 0)` and `(hB : (N : B) = 0)`.
- The scheme and local invertibility are `(X : Scheme.{u})` and
  `hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x)`. For each morphism the base
  `Y` has precisely the same local invertibility hypothesis `hY`.
- The sites are literally `X.smallEtaleTopology` and `Y.smallEtaleTopology`.
  The sheaf category is `Sheaf ... (ModuleCat.{u + 1} A)` (and B), and its
  unbounded derived category is the existing `Etale.DerivedCategoryModule`.
- Q is the recorded `Etale.purityScalarExtension`; i is `DerivedCategory.singleFunctor _ 0`.
  The scalar/single map is the recorded `purityScalarSingleMap`, not an arbitrary arrow.
- A flat module sheaf is an arbitrary M with `exactFunctor _ _ (tensorRight M)`.
  This is the existing definition of exact tensoring, as exposed by the recorded
  `def-pc-flat-sheaf-modules` interface in the fixed-coefficient encoding. It is
  neither stalkwise projectivity nor flatness of the coefficient map.
- The sheaves A_T(r) are exactly `Scheme.finiteEtaleTateTwist X N A hA r`.
  Its degree-zero clause is the constant coefficient module, degree one is the
  sheafification of A tensor_(Z/N) mu_N, and the higher clauses use the published
  sheaf tensor. This is the symmetry convention required by the statement.
- Every r is a natural number, and every K is an arbitrary unbounded derived object.
  No boundedness, constructibility, smoothness, or properness restriction is added.

Conclusion clauses, in order (the named predicates only factor these formulas
into separately elaborated definitions):

1. The first conjunct quantifies over every flat M and identifies the actual adjunct
   `purityScalarSingleMap φ X M` with the already published
   `FiniteSmoothPurity.scalarSingleMap φ X M`. The latter's full definition is the
   canonical single/Q identification, `scalarExtensionRepresentative` on M[0],
   the termwise extension/single identification, and the inverse single/Q map.
   This is precisely computation with the identity flat resolution. `IsIso` asserts
   its invertibility; equality alone is not substituted for invertibility.
2. `∃! β : ∀ r, ... ≅ ...` supplies the ordinary balancing isomorphisms for all
   powers. `IsFiniteTateScalarBalancing` records their formulas. Their local formula uses the existing
   `Scheme.finiteTateEtalePowerGenerator`, the actual ordinary scalar unit, and an
   arbitrary new scalar b. It sends b times the scalar unit at the generator
   (a,z) to the B-generator (φ(a)*b,z). At r=1 this is exactly
   (a tensor z) tensor b maps to φ(a)b tensor z. At r=0 it is coefficient
   multiplication. B-linearity incorporates arbitrary coefficients on the target.
   The existing power generators put the coefficient in the first tensor factor;
   multilinearity gives the product formula on arbitrary pure tensors in all factors.
   Uniqueness means a consumer can select these maps without an unspecified unit
   automorphism or a choice of an arbitrary isomorphism.
3. `(β 0).hom = Functor.OplaxMonoidal.η ...` identifies degree-zero balancing
   with the published ordinary scalar-unit map. The successor equation equates
   `(β (r+2)).hom` with the actual ordinary scalar tensorator followed by
   `β (r+1) tensor β 1`. The separate first-power clause handles r=1;
   the zero clause handles the empty power.
4. In `IsFiniteTateScalarLineNormalized`, `purityScalarSingleMap ... ≫ single.map (β 0).hom = purityScalarUnitMap ...`
   is the requested coefficient-unit normalization, with the ordinary multiplication
   formula already included in clause 2. `purityScalarUnitMap` is precisely the
   normalized `ExceptionalCoefficients.unitIso` transported along single/unit isos.
5. `finiteTateScalarObject` abbreviates the existing sheaf in degree zero shifted
   by `2 * (r : ℤ)`. `finiteTateScalarLineMap` is the actual published scalar/shift
   comparison followed by the shifted scalar/single and β map. `∀ r, IsIso ...`
   states the l_(T,r) assertion, including r=0. Its zero equation explicitly uses
   `finiteTateScalarZeroIso` (zero shift and single/unit isos) to identify l_(T,0)
   with the published normalized coefficient unit.
6. `finiteTateScalarSourceMap` has exactly the displayed endpoints
   Q_X(f* K tensor A_X(r)[2r]) and f*(Q_Y K) tensor B_X(r)[2r]. Its definition
   is `purityScalarTensor.hom` followed by
   `purityScalarPullback.hom.app K tensor finiteTateScalarLineMap`. This has the
   inverse orientation of the originally recorded `scalarPullbackIso`, as required.
   The predicate `IsFiniteTateScalarSourceInvertible` asserts `IsIso` for every f, K, and r.
7. `IsFiniteTateScalarSourceUnitNormalized` is the K=A_Y[0] equation. On the target it applies
   f* to the actual `purityScalarUnitMap`, then the B single/unit and geometric
   unit maps, then the left unitor. On the source it applies f* to the A
   single/unit map and the geometric unit map, then the left unitor, inside Q.
   The resulting map is exactly `finiteTateScalarLineMap`. Thus this is a
   normalization of the specified source arrow, not a fresh choice of isomorphism.
8. `IsFiniteTateScalarSourceZeroNormalized` is the r=0 equation for every K. The target is collapsed
   with the zero-twist/unit identification and right unitor. The source is
   collapsed by the corresponding right unitor inside Q. The remaining map is
   exactly `purityScalarPullback.hom.app K`.

The existential family includes all explicit equations, not merely nonemptiness of
an isomorphism type. The maps are uniquely determined by their ordinary local generators,
and the derived maps are defined composites; no data is chosen from an undetermined
existence theorem. IsIso is the usual assertion that the specified arrow has an inverse,
and supplies the claimed isomorphisms with their original forward maps.

Dependency declarations read and reused:

- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` (current Q84 binding):
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`, publicly retaining
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem;
  ordinary extension, universal derived counit and invertible K-flat computation.
  The fixed-coefficient specialization is reexported through the existing
  `Sheaf.Paper.EtaleDerivedScalarTensor.scalarExtensionRepresentative` interface.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; the full ordinary and
  K-flat-derived normalized Hom bijections, without flatness of the ring map.
- `Sheaf.Paper.VectorPurityScalarSingle`:
  `Etale.purityScalarSheaf`, `purityScalarSheafAdjunction`, `purityScalarExtension`,
  `purityScalarPullback`, `purityScalarAdjunction`, `purityScalarTensor`, and
  `WeilConjectures.PurityFiniteSetting.purityScalarSingleMap`, `purityScalarUnitMap`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finite_etale_torsion_twist_line`, whose full local-triviality,
  locally-constant and exact-tensor clauses were read.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its arbitrary-ring-map, flat-term K-flat preservation and unique normalized
  total-tensor square were read. No independent site universes are identified.
- `Sheaf.Paper.FiniteSmoothCoefficientArrows`:
  `Etale.FiniteSmoothPurity.scalarSingleMap`, `scalarShiftIso`.
- `Sheaf.Paper.FiniteTateSiteDescent`:
  `Scheme.finiteTateEtalePowerGenerator`; only its ordinary local generator definition
  is used, not any pro-etale descent assertion or completed Tate object. Its definition
  owner is `def-amb-finite-tate-site-comparison-data`.
- `Sheaf.Paper.ExceptionalCoefficientMaps`, owned by
  `def-pur-exceptional-coefficient-normalizations`: `ExceptionalCoefficients.unitIso`
  and `ExceptionalCoefficients.ordinaryOplax`, whose actual eta and delta occur in
  the line and balancing predicates.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: the existing
  `CategoryTheory.exactFunctor` flatness predicate in the fixed-coefficient encoding.
- The recorded modules for `def-pc-kflat-complex`, `def-pur-sheaf-tensor-product`,
  `lem-pur-etale-scalar-mate-projection`, and `lem-pc-kflat-resolution` are retained
  as proof imports. `scalarPullbackIso` is its all-unbounded introductory comparison;
  no later bounded-below hypothesis concerning the direct-image mate is invoked.

The four added statement dependencies are already landed nodes carrying the existing
scalarSingleMap/shift maps, ordinary Tate power generators, exact-tensor predicate,
and normalized coefficient unit and ordinary oplax maps.
They record reuse; no dependency statement or binding is replaced.

Edge cases checked before writing: M=0; the empty scheme (invertibility is vacuous
there and every sheaf comparison still has the displayed endpoints); r=0 and r=1;
N=1, which forces both coefficient rings to be zero; the zero target ring; φ=id;
and the nonflat map Z/4 -> Z/2 with N=4 on Spec(C). The last case is allowed and
uses flatness only of M and the ordinary Tate lines. Arbitrary unbounded K remains
in the type; the proof plan uses flat-term K-flat representatives, not bounded models.

Searches: the prescribed msearch.py LeanFinder query was "Derived scalar extension
of a flat sheaf in degree zero is the ordinary extension, normalized by the scalar
unit and Tate balancing". Its eight hits concerned sheaf cohomology, differentials,
and ordinary flat ring-map scalar extension; none states this theorem. The Loogle
query `ModuleCat.extendRestrictScalarsAdj, TensorProduct` returned no hits. The Mathlib
grep query `scalar.*Single|Tate.*scalar|scalar.*Tate` returned unrelated single/scalar
lemmas. Direct rg searches of lean/WeilConjectures and lean/Sheaf covered
`purityScalar`, `finiteEtaleTateTwist`, `scalar.*Single`, Tate/scalar balancing,
`finite_tate_scalar_source_normalization`, and the proposed helper names; a grep
for the exact node id in WeilConjectures found no declaration. Existing related
modules were opened, including FlatSingleScalarConventions, FiniteSmoothCoefficientArrows,
VectorPurityFiniteReduction, ExceptionalCoefficientMaps, EtaleDerivedScalarTensor,
PurEtaleScalarMateProjection, and ReductionExceptional. Their partial interfaces do
not state the joint theorem with all flat-single, all-power, unbounded-source and
boundary equations. Their existing maps and generator definitions are reused.

The current blueprint paragraph 2 and the node's seven-step proof were read. No
statement fault or STATEMENT-DISPUTED issue was found. No unit statement is changed.
Compilation and the prescribed delivery dry run are performed with the launcher wrappers.

The two unit diagrams also have generic categorical helper predicates,
`IsFiniteTateScalarLeftUnitEquation` and `IsFiniteTateScalarRightUnitEquation`.
Their displayed equalities share each functor endpoint once before specializing
to etale derived categories; they assert exactly clauses 7 and 8 above.
This avoids repeated expansion of the derived monoidal implementation during elaboration.

Validation: scompile.py checked the module against current live server sources in
42.4 seconds (nice 19, two threads, unchanged 60-second file limit), with no compiler
errors or warnings. The initial overlay timeout was resolved by factoring the diagrams
and retaining the prescribed current-source confirmation; no limit was raised.
The final renamed declarations are rechecked by deliver2.py before delivery.
The local Stacks sources for 06YN, 06YY, 07A4 and 07A6 were opened as well.


## Returned delivery repair (2026-10-22)

Addressed the H2 return on immutable head `bfd4504b0a66`. Replaced
`lem-amb-finite-tate-site-descent` in `stmt_deps` with its already reviewed definition
owner `def-amb-finite-tate-site-comparison-data`. The used declaration
`Scheme.finiteTateEtalePowerGenerator` is a direct recursive definition (zero,
first, and successor tensor powers); it does not choose from the descent theorem.
Added `def-pur-exceptional-coefficient-normalizations`, the landed owner of the
independently normalized `ExceptionalCoefficients.unitIso` and the ordinary oplax
eta/delta used directly in the predicates.

The Lean file is byte-for-byte unchanged from the saved returned packet. The initial
saved-packet dry run passed at `bb2c240220a`; that mechanical pass preceded the
required H2 repair. Only the item's `lean.note`, its dependency list, and this report
are repaired. The item's statement, proof plan and proof dependencies stay identical
to live. No dependency node is included or overwritten: in particular the Q84 rebound
of `lem-pur-derived-change-of-rings` and the current
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` record are inherited unchanged
from the fresh live base selected by `deliver2.py`.

Self-check with both the node and Lean module open: all finite-ring, positive-N,
annihilation and local-invertibility hypotheses remain explicit. The flat-single
conjunct contains both equality with `scalarSingleMap` and invertibility. The unique
balancing family retains every generator, the zero-power eta and successor delta
formulas. The line normalization uses the independently chosen coefficient unit,
all even shifts, and the zero-power equation. The source arrow retains the specified
endpoints and tensorator/pullback orientation for arbitrary unbounded K. Both genuine
unitor equations remain present, including r=0 and the coefficient-unit input. No
mathematical mismatch or additional hypothesis was introduced. The previously checked
zero module, empty scheme, N=1, r=0/1 and nonflat coefficient maps remain covered.
This is the repairing worker's self-check; the maintainer provides the independent
review, as specified by the repair brief.

## Second reading by Q126

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
