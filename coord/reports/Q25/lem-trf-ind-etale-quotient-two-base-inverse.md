## Worker report

The module `Sheaf.RingTheory.IndEtaleQuotientTwoBaseInverse` states
`Algebra.ind_etale_quotient_two_base_inverse`, with its only proof `by sorry`.
It renders the complete node without changing the natural-language statement,
its dependencies, or its accepted six-step proof. No new notion or dependency
repair was needed. The source read was Stacks `algebra.tex`, Tags 08HR
(lemma-map-into-henselian-colimit), 08HT (lemma-uniqueness-henselian), and 05WS
(lemma-quotient-strict-henselization), together with the recorded quotient theorem.

Hypotheses, one by one:

- The commutative local base is `(R : Type u) [CommRing R] [IsLocalRing R]`.
  Its ideal and containment are `(J : Ideal R)` and
  `hJ : J ≤ IsLocalRing.maximalIdeal R`. The base `S` is exactly `R ⧸ J`.
- The strictly henselian commutative local source is `(C : Type v)` with
  `[CommRing C] [IsStrictlyHenselianLocalRing C]`; the latter extends
  `HenselianLocalRing C`, which extends `IsLocalRing C`.
- The henselian commutative local target is `(D : Type w)` with
  `[CommRing D] [HenselianLocalRing D]`.
- The local structure maps are `[Algebra R C]` and
  `[IsLocalHom (algebraMap R C)]`, and `[Algebra (R ⧸ J) D]` with
  `[IsLocalHom (algebraMap (R ⧸ J) D)]`. The restriction of scalars is expressed
  by `[Algebra R D] [IsScalarTower R (R ⧸ J) D]`. This supplies exactly the
  composite R-action in the node; it does not choose another structure map.
- The two filtered etale colimit assumptions are `hC` and `hD`, using the
  recorded `RingHom.IndEtaleAcrossUniverses` on the two structure maps.
- The field is `(K : Type t) [Field K]`, and the two specified residue
  identifications are `eC : IsLocalRing.ResidueField C ≃+* K` and the
  corresponding `eD`. None of the four universes are identified.
- Agreement of the two maps from R to K is `hbase`. The right side uses
  `algebraMap R D`, which is the map through S by the scalar tower.
  Their common kernel is the maximal ideal by `hker`; hbase transfers this
  equality to the other composite as well.
- The given local R-algebra map is `(u : C →ₐ[R] D)` with
  `[IsLocalHom u.toRingHom]`. Its residue map is the identity of K by `hu`:
  the reductions to K agree after u. Since residue maps are surjective, this
  is precisely the stated equality of residue-field maps, not a weakening.

Conclusions, one by one:

- Every occurrence of Q is the actual quotient `C ⧸ J.map (algebraMap R C)`;
  `J.map (algebraMap R C)` is the extended ideal JC. Every occurrence of q
  is `Ideal.Quotient.mk (J.map (algebraMap R C))`.
- The first existential provides the S-algebra structure on Q; its algebra
  map is required to equal `Ideal.quotientMap ... Ideal.le_comap_map`.
  Thus the action is the induced action from R, fixed on the actual quotient,
  rather than an arbitrary map or extra assumption. Mathlib already defines
  this canonical quotient map, so no helper definition is introduced.
- The second existential is `HenselianLocalRing Q`, including locality. The
  next equality identifies its maximal ideal with the image of m_C under q.
- The existential `eQ : IsLocalRing.ResidueField Q ≃+* K`, with the following
  composition equality after q, says exactly that the quotient-induced
  residue identification is the prescribed one with K.
- The existential `f : Q →ₐ[R ⧸ J] D` is the factored map ū. The first equality
  is `f q = u`, and the quantified f' clause gives uniqueness among all
  factored S-algebra maps. `Function.Bijective f` says it is an isomorphism;
  the actual inverse and both inverse equations are supplied below as well.
- The existential `v : D →ₐ[R ⧸ J] Q`, its `IsLocalHom` clause, and its
  residue composition equality give the required local S-algebra map with
  residue id_K. The quantified v' clause gives uniqueness among all local
  S-algebra maps with that residue condition, without assuming inverse
  equations in the uniqueness predicate.
- The next three equalities render respectively ūv=id_D, vu=q, and vū=id_Q.
  The middle equality is an equality of ring maps, so it does not impose an
  S-algebra structure on C. The other two are S-algebra map equalities.
- Finally `Function.Surjective u` and
  `RingHom.ker u.toRingHom = J.map (algebraMap R C)` are precisely the two
  consequences about the given u.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`; its inherited `HenselianLocalRing` and
  `IsLocalRing`, and the Mathlib henselian-class signatures and docstrings.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`:
  `RingHom.IndEtaleAcrossUniverses`. Read its full definition, its imports,
  and `Algebra.IndEtale` in
  `WeilConjectures.RingTheory.ProEtale.IndEtale`; it is the canonical ULift
  transport of the filtered-etale-colimit predicate.
- Proof-only import `WeilConjectures.RingTheory.StrictlyHenselianQuotient`:
  `isStrictlyHenselianLocalRing_quotient`, with its full signature and proof
  docstring. It supplies the quotient locality, residue field and henselianity.
- Proof-only import `WeilConjectures.RingTheory.MapIntoHenselianColimit`:
  `Algebra.map_into_henselian_colimit`, with its full signature and nine-step
  proof docstring. Its three uses are recorded explicitly over S, S, and R.
- Mathlib `Ideal.quotientMap`, `Ideal.le_comap_map`, `Ideal.map`,
  `IsLocalRing.residue`, `RingHom.ker`, and `AlgHom` express the canonical
  constructions directly; no copied definitions or chosen maps occur.

Edge cases checked mathematically before writing:

- J=0 recovers the residue-preserving comparison over one base.
- J=m_R gives a field base S and the same inverse argument. No proper
  containment in m_R is imposed; the inequality permits equality.
- R=C=k[[t]], J=(t), D=K=k for separably closed k gives the expected
  quotient map and inverse of the factor. A nilpotent ideal, for example
  R=C=k[epsilon]/(epsilon^2), J=(epsilon), has the same behavior.
- J=top cannot satisfy hJ since a local ring here is nontrivial; the zero
  quotient is therefore correctly excluded by the mathematical hypotheses.
- There is no Noetherian, characteristic, finite-generation, or same-universe
  restriction. The existence of residue-field equivalences already rules out
  zero source/target rings as the node does. Filtered index sets are contained
  in the recorded predicate, not replaced by a chosen nonempty small system.
- The uniqueness assertion for v does not presuppose either inverse equation,
  and C is never given an S-action.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder`: "A local residue preserving map from an ind
  etale henselian R algebra C to an ind etale henselian R/J algebra D
  identifies D with C/JC". Eight hits: standard-etale square-zero lifting,
  HenselianRing, formal-etale composition, HenselianLocalRing, an etale
  residue-field construction, and extension homInfinitesimal. No exact match.
- `msearch.py ... loogle`: `HenselianLocalRing, Function.Surjective`.
  One hit, `HenselianLocalRing.TFAE`; it is a henselian characterization,
  not this quotient inverse theorem.
- `msearch.py ... grep`: `[Hh]ensel.*[Qq]uotient|[Ii]nd[Ee]tale.*[Qq]uotient`.
  No Mathlib hits.
- `msearch.py ... leansearch`: "Residue compatible map from ind etale
  henselian algebra over R to one over R/J induces isomorphism of the quotient".
  Eight hits, all residue maps, their functoriality, and residue-field
  equivalences. No quotient inverse statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for quotient/ind-etale,
  two-base, and residue-inverse patterns found the recorded general quotient
  and map-into-henselian theorems and other distinct applications, but no
  statement of this node. The exact item-id search in `lean/WeilConjectures`
  gave no hit. The exact proposed theorem name and two-base names also had
  no hits in those trees, Mathlib, or `dag/lean_names_upstream.json`.

Validation: the delivered file was compiled by the prescribed `scompile.py`
against the published live library. It compiled successfully in both the
sandbox-module and library-module checks, with no non-sorry warning.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q25

A second pass through the node and the complete Lean signature checked each
hypothesis and clause listed above. This is the worker's own rereading; the
maintainer's independent reading is part of delivery review, and no additional
agent was started. In particular I checked that S is the quotient base, both
local structure maps and both ind-etale hypotheses remain present, the common
K-identifications and kernel condition are explicit, and the uniqueness of v
quantifies over its residue/locality property alone. The canonical quotient
algebra map is fixed explicitly, f is unique as a factor before its bijectivity
is asserted, and all three composite equations and both final consequences
are present. The scalar tower adds no mathematical hypothesis beyond the
stated composite R-action, and no S-action on C is required. No mismatch was
found and no statement correction was made.
