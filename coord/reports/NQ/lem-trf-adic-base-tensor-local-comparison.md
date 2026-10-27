## Worker report

The module Sheaf.RingTheory.AdicBaseTensorLocalComparison states
RingTheory.adicBaseTensorLocalComparison with a single sorry proof. Its two helpers
are transparent aliases for the exact tensor algebra H tensor_R U and its canonical
inclusion from U; they use Mathlib's existing constructions and contain real data.
No new independent notion, dependency module, or statement correction is needed.
The original statement, accepted split, and dependencies are preserved.

This is a stage-2 assignment. The live node has stage-1 reviewed PASS, status split,
no lean record, and a stage-2 queue entry. There is no released repair note. The
stage-handoff paragraph of coord/brief-stage2.md explicitly says that its prior
stage-1 unchanged-item blocker does not prohibit this stage-2 statement delivery.

Hypotheses and clauses, in the order of the node:

- R is a commutative Noetherian ring: `{R : Type u} [CommRing R]
  [IsNoetherianRing R]`. The arbitrary ideal is `(I : Ideal R)`.
- U is a finite-type commutative R-algebra: `{U : Type v} [CommRing U]
  [Algebra R U]` and `hU : RingHom.FiniteType (algebraMap R U)`.
  RingHom.FiniteType is the dependency's exact recorded interface.
- H is the I-adic completion: Mathlib `AdicCompletion I R`, with its existing ring
  and R-algebra structures. `AdicBaseTensor I U` unfolds to
  `TensorProduct R (AdicCompletion I R) U`; no restriction equates u and v.
  The canonical maps from H and U are Mathlib includeLeft and includeRight;
  adicBaseTensorInclusion is exactly includeRight.toRingHom.
- r is prime and contains IU: `(r : Ideal U) [r.IsPrime]` and
  `hIr : I.map (algebraMap R U) ≤ r`.
- The canonical quotient identification is the existential ring equivalence `q`.
  Its pure-tensor formula uses `AdicCompletion.evalOneₐ I h` and every base-ring
  representative b. Since pure tensors generate the ring and the quotient map
  is surjective, this formula determines q uniquely; it is not an arbitrary map.
- n is the prime prescribed in the statement: `n : PrimeSpectrum (AdicBaseTensor I U)`
  and its asIdeal equals the comap under q composed with the quotient projection
  of `r.map (Ideal.Quotient.mk (I.map (algebraMap R U)))`. This latter image is
  exactly r/IU because hIr asserts IU is contained in r. PrimeSpectrum supplies
  the IsPrime instance without imposing a new hypothesis on the input.
- Z and W_* are respectively `Localization.AtPrime r` and
  `Localization.AtPrime n.asIdeal`, with Mathlib's local-ring structures.
- W is Noetherian: the first conjunct `IsNoetherianRing (AdicBaseTensor I U)`.
- The canonical local map is `f`, explicitly equated to Mathlib's
  `Localization.localRingHom r n.asIdeal (adicBaseTensorInclusion I U) hnr`.
  The contraction equality hnr is concluded existentially, not assumed.
- The maximal-ideal equality is `Ideal.map f (IsLocalRing.maximalIdeal Z) =
  IsLocalRing.maximalIdeal W_*`.
- For every positive exponent, `e j` is the displayed ring equivalence modulo
  maximal ideals to power `j + 1`. Its value on every quotient representative
  is the class of `f z`, ensuring it is induced by that canonical local map.
- The inverse coefficient formula is the next conjunct, using
  `AdicCompletion.evalₐ I (j + 1) h = Ideal.Quotient.mk _ b` and giving the image
  of the localized pure tensor h tensor a as the class of b*a in Z. It quantifies
  every b satisfying the coordinate condition, so independence of representatives
  is included, without a choice of representatives.
- The localized denominator formula quantifies `t : n.asIdeal.primeCompl` and
  states that the inverse on `IsLocalization.mk' W_* w t` is the inverse on the
  numerator multiplied by `Ring.inverse` of the inverse on the denominator.
  The denominator image is a unit: t is inverted in W_*, its quotient image is
  still a unit, and the ring equivalence preserves units. Thus Ring.inverse is
  its actual multiplicative inverse, not its default value on nonunits.
- Transition compatibility is equality of the two ring homomorphisms built from
  `Ideal.Quotient.factor`, for every j ≤ k. Exponents are j+1 and k+1.
- Residue fields are identified by `e 0`: the quotients by maximal-ideal first
  powers are the residue fields of these local rings. No additional identification
  is postulated: Mathlib defines IsLocalRing.ResidueField as this quotient.
- The completion equivalence E has source and target AdicCompletion of the two
  local rings at their maximal ideals. Its coordinate formula is
  `evalₐ ... (j+1) (E z) = e j (evalₐ ... (j+1) z)` for all j and z.
  The zero coordinate is the singleton quotient by the zeroth power; it adds no
  missing data. This specifies the induced inverse-limit map uniquely.
- Commutation with the maps from U is the next conjunct, evaluated on every a:U,
  with the two localization maps, inclusion into W, and completion algebraMaps.
- E and E.symm are both Continuous, with topology arguments explicitly given as
  the maximal ideals' `Ideal.adicModuleTopology` on their respective completions.
  These are exactly the extended maximal-ideal-power topologies: the neighborhoods
  are m^j times the completion. No implicit arbitrary topology is used.
- I is not assumed maximal, and R is not assumed local; neither restriction occurs
  in the binders. In particular r need not lie over a maximal ideal of R.

Dependencies read and used:

- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing,
  isNoetherianRing_iff_ideal_fg (transitively public through FiniteType).
- Mathlib.RingTheory.FiniteType: RingHom.FiniteType; its Algebra.FiniteType
  specialization and Algebra.FiniteType.isNoetherianRing are the proof interfaces.
- Mathlib.RingTheory.AdicCompletion.Basic: AdicCompletion (compatible sequences).
  Mathlib.RingTheory.AdicCompletion.Algebra: the ring/algebra structures,
  evalOneₐ, evalₐ, and algebraMap. The recorded basic module is publicly imported
  by Algebra, which is needed to have these ring structures and projections.
- Mathlib.LinearAlgebra.TensorProduct.Defs and Basic: TensorProduct, tmul and lift;
  Mathlib.RingTheory.TensorProduct.Basic and Maps: instCommRing, includeLeft,
  includeRight, productMap and ext. Maps publicly imports the underlying tensor
  modules; these are the exact clausewise mathlib_match of the tensor pushout node.
- Mathlib.RingTheory.Localization.AtPrime.Basic: Localization.AtPrime,
  Localization.localRingHom and its fraction formula. The maximal ideal is the
  extension of the prime (AtPrime.map_eq_maximalIdeal). The residue field definition
  was also read in Mathlib.RingTheory.LocalRing.ResidueField.Defs.
- Proof-only imports: Mathlib.RingTheory.AdicCompletion.Completeness
  (pow_smul_top_eq_ker_eval); Mathlib.RingTheory.Localization.Submodule
  (IsLocalization.isNoetherianRing); and
  WeilConjectures.RingTheory.AdicCompletionNoetherian
  (AdicCompletion.isNoetherianRing). The finite-type Noetherian theorem is already
  available from the public finite-type module.
- The two proof nodes lem-trf-tensor-base-change-ideal-power-quotients and
  lem-trf-adic-quotient-isomorphisms-localize have no lean or mathlib_match record
  in the read clone; there is consequently no recorded module to import for them.
  Their full statements and the node's seven proof steps were read. They are
  proof prerequisites only; the statement uses the already recorded Mathlib
  definitions and does not need new declarations of those results.

Source read: literature/stacks-project/algebra.tex, lemma-hathat-finitely-generated,
Tag 05GG, including its proof: completion projection kernels and the quotient
R^/I^nR^ = R/I^n. The tensor/localization assembly is explicitly the agent-supplied
consequence in this node, rather than a literal quotation of that tag. The current
latest blueprint's contracting-local-term unit and proof were also read; this
auxiliary historical algebra node is not that unit's own statement and does not
change its route.

Edge cases checked before writing: I=0 gives the original tensor algebra and the
identity local/completion comparison. I=R admits no prime r containing IU, including
when U is the zero ring, so the hypotheses are correctly vacuous there. Zero base
or zero algebra has no prime r. The case R=Z, I=(p), U=Z[x], r=(p,x) has a nonlocal
base; r=(p) checks a nonmaximal prime. Taking R=k[x,y], I=(x), U=R, r=(x) checks a
nonmaximal adic ideal. Positive exponents are exactly j+1, including exponent one;
no exponent-zero strengthening or local-base assumption was introduced.

Searches actually run:

- msearch.py leanfinder, query "Completion of a Noetherian base ring tensored with
  a finite type algebra induces isomorphisms on local maximal ideal power quotients
  and completed local rings at primes containing the adic ideal": 8 hits. The
  closest ofTensorProductEquivOfFiniteNoetherian results require Module.Finite,
  which finite-type algebras need not satisfy, and do not give this localized package.
- msearch.py leansearch, query "local rings completed after tensoring with adic
  completion of a Noetherian base ring": 8 hits, the same finite-module comparison
  and existing completion structures; no exact match.
- msearch.py loogle, query "AdicCompletion.evalₐ, Localization.AtPrime,
  Algebra.TensorProduct.includeRight": 0 hits.
- msearch.py grep, query "adic.*(local|tensor)|local.*completion|completion.*local"
  in RingTheory: 25 hits, including AsTensorProduct, LocalRing, Noetherian and
  unrelated valuation results; no theorem with this statement.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and
  `adicBaseTensor|adic_base_tensor|completed.base.*tensor|base.change.*adic`, plus
  name-collision searches in those roots and Mathlib: no exact declaration.
  FiniteTypeBaseChangeAdicQuotients was read in full: it requires a local base,
  completes at its maximal ideal, and prescribes Q; it does not give the present
  arbitrary-ideal construction or the continuous completion equivalence.
  CompletedLocalBaseChange was also read; it concerns scheme stalks and uses that
  special local-base comparison. Neither is the same statement as this node.
- dag/lean_names_upstream.json has no occurrence of the item id.

Validation: scompile.py compiled the sandbox probe and the actual library module
cleanly, each in approximately 3.4 seconds. The only postponed proof is the named
main theorem, matched to this DAG node and its complete seven-step proof docstring.
There is no STATEMENT-DISPUTED flag or identified node fault.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
