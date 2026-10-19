## Worker report

The delivery states `ModuleCat.idealPowerTorsion_rightDerived_iso_cech` in
`Sheaf.Algebra.Homology.IdealTorsionCechComputation`. Every theorem has a `sorry`
proof, and all definitions have actual data. The auxiliary declarations belong to
this node's explicitly introduced complex, differentials, and canonical fraction
maps. No new notion outside the node is introduced, and no dependency record is
changed. The node copy changes only `lean`.

The previous worker's stale-assignment report confused the node's stage-1
`reviewed` field with stage-2 completion. The current node is split and reviewed
by NT-cc-NH-30328cc68, but has neither `lean` nor `reviewed_lean`; this delivery
adds its missing Lean statement and does not resplit or change its proof.

Source read: `literature/stacks-project/dualizing.tex`, lines 1649–1672,
`lemma-compute-local-cohomology-noetherian`, Tag 0956. The module assertion gives
precisely the comparison with the displayed extended localization complex.

Clause-by-clause correspondence:

- A commutative Noetherian ring is `{R : Type u} [CommRing R]
  [IsNoetherianRing R]`. There is no domain, nonzero, local, or proper-ideal
  hypothesis.
- The arbitrary finite list, including its empty case, is `(r : ℕ)
  (t : Fin r → R)`. Its ideal K is `Ideal.span (Set.range t)`.
- An arbitrary R-module is `M : ModuleCat.{u} R`; no `Module.Finite` or
  `IsNoetherian` hypothesis is placed on M. The ring and modules can be taken in
  any common universe u. This is the universe convention of the recorded torsion
  functor; it places no cardinality bound on the mathematical modules.
- Gamma_K is exactly the recorded `ModuleCat.idealPowerTorsion K`, with its
  actual primary-component construction. The expression
  `((idealPowerTorsion K).rightDerived q).obj M` is the right-derived functor
  required by the node, not the independently defined Ext-colimit local cohomology.
  Allowing exponent zero only adds zero, already annihilated by K to exponent one.
- `LocalizedModule.Away a M` is Mathlib's module of fractions at
  `Submonoid.powers a`. `LocalizedModule.mk_eq` says there is a further denominator
  killing the cross-multiplied difference; this is exactly the fraction relation
  in the node. No regular-element assumption occurs.
- `IdealTorsionCech.tupleProduct t s` is the product along an increasing tuple
  `s : Fin p ↪o Fin r`.
- `IdealTorsionCech.term t M 0` is definitionally M. Its term at p+1 is the full
  finite product of `LocalizedModule.Away (tupleProduct t s) M` indexed by
  increasing (p+1)-tuples. For p+1 > r the index type is empty, hence the term is
  the zero module. These are natural-number cochain complexes; extending by zero
  to negative degrees gives the node's convention without changing any H^q.
- `differential t M 0` sends m to m/1 in each coordinate. In higher degrees it
  uses `LinearMap.pi`, a finite sum over deleted positions, the sign
  `(-1 : ℤ) ^ a.val`, and the canonical localization map from that face to the
  full tuple. Zero-based position a has the paper's one-based sign (-1)^(a-1).
- `localizationMap_existsUnique` specifies the unique R-linear map agreeing
  with m/1 on numerators when a divides b; inverting b makes a invertible.
  `localizationMap` chooses only this uniquely determined object, as permitted by
  the no-hollow-definitions rule. In the fraction description b=a*c its value on
  m/a^n is c^n*m/b^n. The target generator is the full tuple product, and
  `faceProduct_dvd` supplies precisely the needed divisibility.
- `differential_sq` is the node's assertion that these are cochain differentials.
  Its named proof is used as the proof field of `CochainComplex.of`, giving
  `IdealTorsionCech.complex`; no complex data is selected from an existence claim.
- `mapTerm` is f in degree zero and Mathlib's `IsLocalizedModule.map` on every
  fraction coordinate in positive degrees. `mapTerm_comm` states its compatibility
  with the differential; `map` packages the actual cochain map.
- `(IdealTorsionCech.complex t M).homology q` is the usual homology object in
  ModuleCat, hence kernel modulo incoming image. There is no incoming differential
  at degree zero in `ComplexShape.up ℕ`.
- `(q : ℕ)` covers every q >= 0. The existential family `e` supplies R-linear
  isomorphisms in exactly the required direction, from R^q Gamma_K(M) to H^q(C).
  An isomorphism in ModuleCat is an invertible R-linear map.
- The final universally quantified equation for every `f : M ⟶ N` is
  `R^q Gamma_K(f) ≫ (e N).hom = (e M).hom ≫ homologyMap (map t f) q`.
  Thus the result includes naturality, rather than only pointwise existence.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`, for
  `def-weil-pbc-noetherian-ring`; the full definition and
  `isNoetherianRing_iff_ideal_fg` were read.
- `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`,
  `ModuleCat.idealPowerTorsion` and its additive instance, for
  `def-sbc-ideal-power-torsion-functor`. The full source was read locally and
  confirmed with `scompile.py --source`; it uses `Ideal.primaryComponent` and
  `Ideal.primaryComponent.map`.
- Mathlib's `LocalizedModule.Away`, `LocalizedModule.mkLinearMap`,
  `IsLocalizedModule.map`, `CochainComplex.of`, `CochainComplex.ofHom`,
  `HomologicalComplex.homologyMap`, and `Functor.rightDerived` give the standard
  localization, complex, homology, and derived-functor constructions.
- The proof dependency `lem-per-local-cohomology-cech-bound` was read in full.
  It has no recorded Lean declaration or Mathlib match, hence no module can be
  imported for it. The main theorem docstring carries the item's supplied proof
  via that node, inverting its comparison and explaining naturality. There is
  no dependency wait and no circular import.

Edge cases checked before construction:

- r=0: every positive term has an empty index type, so C=M[0], K=0, and the
  comparison gives M in degree zero and zero in higher degrees.
- r=1: the differential is the usual M to M_t and all later terms vanish.
- r=2: the next differential is x_2 restricted to M_(t_1*t_2) minus x_1
  restricted there, so its composite with m/1 is zero.
- A zero generator gives a zero localization; all-zero lists give K=0.
- A unit generator gives the expected contracting direction and K=R, whose
  ideal-power torsion functor is zero.
- Repeated generators, zero divisors, non-finitely-generated modules, M=0,
  and the zero ring are all admitted by the binders and localization construction.
- q=0 uses the zero incoming image; q>r has zero homology.

Searches made:

- `msearch.py` LeanFinder: "The right derived ideal power torsion functor is
  computed by the extended alternating localization Cech complex". Eight hits,
  headed by `localCohomology` and its Ext-colimit/radical-comparison constructions;
  none states this computation.
- `msearch.py` Loogle: `localCohomology`. Three hits:
  `localCohomology`, `localCohomology.isoSelfLERadical`, and
  `localCohomology.isoOfSameRadical`. They do not give this localization comparison.
- `msearch.py` grep: `Cech|localCohomology|torsion` in `Algebra/Homology`.
  Five hits in Mathlib's `LocalCohomology.lean`; line 46 explicitly lists the
  Cech characterization as future work.
- `rg` in the upstream `WeilConjectures` tree for the item id: no hits. Searching
  localization/Cech in its homology directory found generic homotopy-category
  infrastructure, not this module complex or derived-torsion comparison.
- `rg` in `lean/Sheaf` found the recorded torsion functor and its Ext-colimit
  comparison, but not this theorem. Read `Paper/ExtendedLocalizationCech.lean`
  and `Paper/RingComplexFunctorial.lean`: these deal with coefficient ring sheaves
  on ringed sites and functorial complexes for rings, not this ordinary-module
  complex with arbitrary M and the derived primary-component endofunctor.
- Exact full-name searches for `IdealTorsionCech` and
  `idealPowerTorsion_rightDerived_iso_cech` in Mathlib, upstream, and the project
  returned no collisions.

No statement correction or mathematical dispute is needed. The existing
stage-1 review already notes that this node and
`lem-per-local-cohomology-cech-bound` have equivalent statements. This delivery
preserves the existing DAG and its given proof route.

Validation: the delivered module was compiled individually through `scompile.py`
in both its sandbox and library-module forms, each in 3.2 seconds, with no errors
or warnings. The first pass's unused pattern variable was renamed `_p`; the clean
second pass validates that correction. All variables and the sole universe are
explicitly bound. The maximum source line length is 87 characters.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
