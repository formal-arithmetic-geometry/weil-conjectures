## Worker report

Repair of the return on immutable head 76c1e6d6ffee: the node
`def-sfb-relative-birational-group-law` has now landed from Q110, and
`def-sfb-strict-birational-law` has also landed from Q131. I read both current node
statements, their full declaration signatures and docstrings, and the strict law's
`RelativeBirationalMaps` dependency. Both sandbox new-node copies and both definition
modules are removed from this delivery. The item imports their published modules and
adds their existing ids to stmt_deps. Their live records and sources are untouched.
This is a substantive rebind to the landed interfaces, not a rebase of the returned files.

The only delivered module is `Sheaf.AlgebraicGeometry.BirationalLawStrictification`.
It states `AlgebraicGeometry.exists_strict_birational_law_open`, with proof `sorry`,
and two real Prop definitions belonging to this theorem's restriction/base-change
interface. There are no new DAG nodes, no dependency record repairs, and no postponed
helper theorem. The natural-language item statement, proof, and proof_deps are unchanged.

Hypotheses and clauses, matched individually:

- `B : Type u`, `[CommRing B]`, `[IsDomain B]` and
  `hB : IsField B ∨ IsDiscreteValuationRing B` render field or DVR. Both alternatives
  already imply the domain condition. The base is `Spec (CommRingCat.of B)`.
- `X : Over (Spec (CommRingCat.of B))` is the S-scheme. The product `X ⊗ X`
  is the chosen scheme-theoretic fibre product in the slice category.
- `[Smooth X.hom]`, `[IsSeparated X.hom]`, `[LocallyOfFiniteType X.hom]`,
  `[QuasiCompact X.hom]` render smooth separated finite type. Separatedness means
  closed diagonal; finite type is locally finite type plus quasi-compactness.
- `hX : ∀ s, Nonempty (X.hom.fiber s)` renders nonempty fibres, not just the
  special fibre or nonemptiness of X.
- `m : RelativeGroupLaw.Representative (X ⊗ X) X` is Q110's existing relative
  rational multiplication representative. Its `domain`, `dense_domain` and slice
  morphism `hom` supply the S-dense domain and S-morphism. Its `source` and `inclusion`
  are the canonical domain scheme and inclusion, not arbitrary comparison maps.
- `hm : RelativeGroupLaw.IsBirationalGroupLaw m` is used directly. It requires
  birationality of both existing universal translations `leftTranslation` and
  `rightTranslation`, and `IsAssociative`. The former requires dense source and
  image and an open immersion after restriction. The latter tests all four domain
  lifts over every test S-scheme and asserts equality of the two products, preserving
  nonreduced test schemes and equality of morphisms.
- `∃ A : X.left.Opens` gives the canonical open subscheme
  `Over.mk (A.ι ≫ X.hom)`. `RelativeGroupLaw.IsFiberwiseDense X (A : Set X.left)`
  is exactly density of its inverse image in every scheme-theoretic fibre.
- The four explicit classes on `A.ι ≫ X.hom` assert smooth separated finite type
  for that same open subscheme.
- `∃ n : RelativeBirational.StrictLaw (Over.mk (A.ι ≫ X.hom))` uses Q131's
  actual strict-law data: one multiplication domain, two open images, two genuine
  isomorphisms with four prescribed coordinate equations and all six density
  conditions for domain/leftRange/rightRange along both projections. Its
  associativity is equality on a fibrewise dense common triple domain. On the
  smooth separated schemes in this statement that is equivalent to rational-law
  associativity; equality extends wherever both composites are defined by
  fibrewise schematic density and separated-target uniqueness. The strict data
  do not discard either cross-projection density condition.
- `m.AgreesWithStrictRestriction A n` expresses that this is the restriction of m:
  an S-dense open E of the smaller square lies in `n.mul.domain`, its canonical
  product inclusion factors through the original domain, and both multiplications
  agree there as maps to X. The two projection equations uniquely pin the map k
  into the original domain (open inclusions are monomorphisms). Thus no arbitrary
  comparison map or replacement law is assumed. This is just dense common-open
  agreement between different ambient source/target schemes, for which the landed
  same-source `Representative.Agrees` cannot be used directly.
- The additional implication starts with `IsDiscreteValuationRing B` and
  `m.IsGroupBaseChange (Spec.map (CommRingCat.ofHom
  (algebraMap B (FractionRing B))))`. The helper requires that the base-changed
  domain inclusion is an isomorphism, exactly the whole generic square condition,
  and a genuine `GrpObj` on the base-changed X. Its multiplication must equal the
  base-changed given m after the canonical pairing of the two projections. This
  uses the given domain and multiplication, not a freely chosen arrow.
- The conclusion for that same A is `Set.range (pullback.fst X.hom g) ⊆ A`:
  the whole generic fibre lies in the open, not merely a dense generic part.
  `FractionRing B` is a canonical choice of the specified fraction field.

The helper definitions `RelativeGroupLaw.Representative.AgreesWithStrictRestriction`
and `.IsGroupBaseChange` are explicitly constructed propositions and listed in
lean.declarations. They define only the cross-ambient agreement and generic compatibility
clauses of this item; they do not recreate representatives, associativity, strictness,
translations, density, quotient rational maps or a group structure. All binders and
universe u are explicit and auto implicits are disabled.

Dependency declarations used:

- Sheaf.AlgebraicGeometry.RelativeBirationalGroupLaw:
  `RelativeGroupLaw.IsFiberwiseDense`, `.Representative`, `.Representative.source`,
  `.Representative.inclusion`, `.IsBirationalGroupLaw`, `.IsBirationalOnDomain`,
  `.leftTranslation`, `.rightTranslation`, `.IsAssociative` (full definitions read).
- Sheaf.AlgebraicGeometry.StrictBirationalLaw: `RelativeBirational.StrictLaw`,
  `.square` and `.Associative`, with its `RelativeBirationalMaps` dependency
  supplying `.PartialMap` and `.FibrewiseDense` (full definitions read).
- Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map`; Fiber: `fiber`, `fiberι`.
  Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`; Separated: `IsSeparated`;
  FiniteType: `LocallyOfFiniteType`; QuasiCompact: `QuasiCompact`;
  ClosedImmersion/OpenImmersion: the recorded diagonal/open inclusion notions.
- Mathlib.RingTheory.DiscreteValuationRing.Basic: `IsDiscreteValuationRing`;
  Mathlib.RingTheory.Localization.FractionRing: `FractionRing`; Mathlib's `IsField`.
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`, `MonObj.mul`;
  Monoidal.Cartesian.Over: slice products and canonical pairing/projections;
  WeilConjectures.AlgebraicGeometry.BaseChangeConventions: the recorded canonical
  scheme base change `Over.pullback` and scheme-theoretic fibres.
- Proof-only imports: Mathlib.AlgebraicGeometry.Morphisms.Proper (proper/smooth
  base-change dependency), WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
  (`ext_of_isSchemeTheoreticallyDominant_of_isSeparated`), and the newly landed
  Sheaf.AlgebraicGeometry.SmoothFibrewiseDenseOpenBaseChange
  (`Smooth.fibrewise_dense_open_baseChange`). Smooth composition is `smooth_comp`.
  The remaining proof node `lem-sfb-product-projection-density-shrink` has no
  published declaration; no missing object from it is needed to type this statement.

Source: BLR Néron Models 2.5, 5.1 Definition 1 and Theorem 5, and 5.2 Definition 1
and Proposition 2, printed pp.112--117, primary scan
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The theorem docstring retains all six proof steps, including both cross-density
arguments and the generic-fibre-preserving charts. No unit statement is changed.

Edge cases: X need not be irreducible, integral or geometrically connected.
Disconnected and zero-dimensional smooth schemes are retained. Auxiliary empty
fibres have vacuous density, but hX excludes empty fibres of X itself. No
characteristic restriction occurs. Both projection directions remain separate.
Over a DVR, density of the generic fibre alone is not substituted for S-density.
The entire generic domain and entire generic fibre are retained in the extra clause.
Test schemes have the same arbitrary universe u as the base; no smaller test
universe or arbitrary coefficient-universe equality is imposed.

Searches: the original LeanFinder strictification query, LeanSearch relative-rational-map
query, Loogle `AlgebraicGeometry.Scheme.RationalMap, CategoryTheory.GrpObj`, and
Mathlib grep `FibrewiseDense|FiberwiseDense|[Bb]irational[Gg]roup[Ll]aw|[Rr]elative[Rr]ational`
are retained in searches.jsonl. They found ordinary absolute rational maps and
special point groups, not the then-missing interface. For this repair I searched
the current DAG and current Sheaf source, found Q110's landed relative group law
and Q131's landed strict law, and read all definitions instead of retaining the
stale sandbox copies. Fresh Loogle of the two project declaration names reports
zero hits (the public service does not index these project declarations).
Direct rg for `AgreesWithStrictRestriction|IsGroupBaseChange|relativeOpen` in the
relevant project modules and for the two helper names in Mathlib/AlgebraicGeometry
found no existing helper. The existing representative agreement takes identical
ambient sources/targets, so cannot directly express the restriction to an open.

No STATEMENT-DISPUTED issue or statement correction is introduced. This repair
removes the conflicting node creation and both conflicting module paths; the
item uses the first landed owners' actual interfaces. Only the item node,
its module and this report are submitted. Compilation and dry-run validation
use the prescribed scompile.py and deliver2.py wrappers.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
