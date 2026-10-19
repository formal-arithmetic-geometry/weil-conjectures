## Worker report

The module `Sheaf.FieldTheory.CanonicalTraitTameCharacter` states
`IsDiscreteValuationRing.exists_canonical_tame_character` with `sorry` as its whole proof.
The node statement is unchanged. The complete sixteen-step DAG proof is in the theorem
docstring; no data or new definition is postponed.

Clause-by-clause correspondence:

- Strictly henselian DVR: `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [IsStrictlyHenselianLocalRing R]`.
  The existing strict henselian class extends `HenselianLocalRing` and supplies the
  separably closed residue field. No excellence, completeness, perfection or
  algebraically closed residue-field hypothesis is imposed.
- Fraction field: `(K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]`.
- Residue field k: `IsLocalRing.ResidueField R`, literally `R / maximalIdeal R`.
  The recorded scheme residue-field dependency uses this same Mathlib ring construction
  on a stalk; the present ring-theoretic statement uses the underlying ring construction
  directly and does not introduce a second residue-field notion.
- Separable closure inside an algebraically closed field:
  `(Ksep : Type w) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]`,
  `(Ω : Type z) [Field Ω] [IsAlgClosed Ω] [Algebra Ksep Ω]`.
  The algebra map embeds the separable closure, since a field map is injective.
  R maps into it through K, and K maps into Ω by composition. There is no additional
  algebraicity condition on the ambient Ω, matching the node.
- H with its Krull topology: `Gal(Ksep/K)`, with Mathlib's `krullTopology` instance.
- Characteristic exponent: `p` and `hp : p = if ringChar (IsLocalRing.ResidueField R) = 0
  then 1 else ringChar (IsLocalRing.ResidueField R)`.
- Positive prime-to-p orders: `TameRoots.Order p`; its subtype conditions are
  `0 < d` and `d.Coprime p`.
- Root groups and transitions: `TameRoots.limitSubgroup Ω p` is the subgroup of
  families in Ωˣ whose coordinates belong to Mathlib's `rootsOfUnity d Ω` and
  satisfy `x e ^ (e / d) = x d` when d divides e. Its `limitTopology Ω p`
  is the initial topology of the coordinates into discrete units, equivalently
  the product-subspace topology of the finite discrete root groups.
- Compatible roots of each uniformizer exist: the first universal π clause uses
  `Irreducible π` (equivalent to generating the maximal ideal in a DVR) and gives
  an α with the displayed power and divisibility compatibility equations in Ksep.
- Canonical tame map: `∃ t : Gal(Ksep/K) →* TameRoots.limitSubgroup Ω p`,
  followed by continuity for the specified inverse-limit topology and
  `Function.Surjective t`.
- Its defining formula and independence: the SAME t is required to satisfy
  `(((t h).1 d : Ωˣ) : Ω) = algebraMap Ksep Ω (h (α d) / α d)` for EVERY
  uniformizer π and EVERY compatible root family α of π. Thus all choices give
  the same map; no arbitrary uncharacterized homomorphism is substituted.
- Wild kernel and exactness: S is exactly `t.ker`, with its canonical subgroup
  inclusion into H, not an unrelated subgroup. Surjectivity and this actual kernel
  give the stated exact sequence. For every finite discrete group Q and continuous
  surjective `f : t.ker →* Q`, the order is `p ^ n` for some n. This is precisely
  the stated finite-continuous-quotient meaning of pro-p. The separate clause
  `p = 1 → t.ker = ⊥` says S is trivial in residue characteristic zero.
- Compatible primitive roots exist: `∃ σ : TameRoots.limitSubgroup Ω p,
  TameRoots.IsCompatiblePrimitiveFamily p σ.1`.
- Every such compatible primitive family gives a generator: the subsequent
  universal σ clause asserts density of `fun n : ℤ ↦ σ ^ n` with the actual
  inverse-limit topology. For every d in `Order p`, a subgroup U has carrier
  equal to the closure of the range of `n ↦ (σ ^ d.1) ^ n`, and `U.index = d.1`.
  This states exactly the topologically generated subgroup and its finite index;
  it does not assume a topological-group instance for an unspecified topology.

Dependencies read and used:

- `def-weil-pbc-henselian-terminology`:
  `WeilConjectures.Mathlib.RingTheory.Henselian`,
  `IsStrictlyHenselianLocalRing` (extends henselian local ring, separably closed residue).
- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing` and `irreducible_iff_uniformizer`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, read together with its underlying
  `IsLocalRing.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Defs`.
- `def-pd-separable-closure`: `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`,
  `IsSepClosure.exists_intermediateField_mem`; its module explicitly identifies the
  notion as Mathlib's `IsSepClosure`, which is used here.
- Added definition dependency `def-per-tame-root-limit` (existing declarations):
  `Sheaf.FieldTheory.TameRootsProduct`, helpers `TameRoots.Order`, `limitSubgroup`,
  `limitTopology`, `IsCompatiblePrimitiveFamily`. These definitions are unrestricted
  in p and in the characteristic of Ω. The module's positive-characteristic product
  theorem is NOT invoked to discard mixed-characteristic or p=1 cases. Its full
  signature and the docstrings of all four reused helpers were read.

The six public imports provide the statement's actual definitions and classes. Per the
maintainer's H9 return, all sixteen private imports have been removed. The proof plan
remains in the theorem docstring; proof-only modules are not imported in this repair.
No statement dependency is missing.

Source checked: the local ILO PDF, PDF pages 265–266 = printed pages 259–260, XVII §1.2
and §1.2.1–1.2.3; local `literature/stacks-project/pione.tex`,
`lemma-structure-decomposition-separable-closure` (Tag 0BUB). The latter expressly
includes the characteristic-zero trivial wild kernel. The root formula and all sixteen
proof steps are those of the reviewed node. No source/statement discrepancy was found.

Edge cases checked before the final statement:

- p=1 retains every positive order and explicitly requires the trivial wild kernel;
  no `Fact p.Prime` or `CharP Ω p` excludes it.
- Mixed characteristic is retained: p is computed from the residue field, not Ω.
- Imperfect separably closed residue fields are retained: no `IsAlgClosed k` binder.
- d=1 is included; primitive root and root coordinate are 1, and the subgroup has index 1.
- d=0 is excluded by positive order, exactly as the inverse system requires.
- A uniformizer is nonzero, so its roots and the denominators in the formula are nonzero.
- Replacing π by uπ and changing root choices are included in the universal formula.
- R, K, Ksep, Ω and finite quotient Q have separately bound universes. Any finite quotient
  is equivalent to one in Type 0, so the Q universe does not make the assertion vacuous.

Searches (the retained earlier attempt's `searches.jsonl` was also read):

- LeanFinder, previous query "Canonical tame ramification homomorphism for a strictly
  henselian discrete valuation ring with pro-p kernel and procyclic tame quotient":
  eight hits, including valuation inertia and unrelated tilt constructions; no match.
- Loogle, previous query `IsDiscreteValuationRing, IsStrictlyHenselianLocalRing`:
  no hits (Loogle does not index the project's strict henselian class).
- `msearch.py ... grep 'tame.*inertia|wild.*inertia|henselian.*Galois'`: no Mathlib match.
- `rg` over `WeilConjectures/FieldTheory` and `lean/Sheaf/FieldTheory` for `tame|Tame`:
  found `TameRootsProduct` (reused) and `HenselianDVRTameSequence`. The latter assumes
  excellence, positive residue characteristic and algebraically closed residue field,
  and states a noncanonical untwisted quotient; it is not this node.
- `rg` for `lem-per-trait-tame-algebra|trait_tame|canonical_tame` in the whole upstream
  `WeilConjectures` and project `lean/Sheaf`: no existing declaration.
- Repeated LeanFinder query "Canonical tame ramification sequence of a strictly henselian
  discrete valuation field, uniformizer root ratios and pro-p kernel" and Loogle
  `"inertia", "ramification"`: LeanFinder returned eight hits (tilt constructions,
  `Field.henselian`, `ValuationSubring.inertiaSubgroup`, and a finite ramification
  degree formula); Loogle returned seven finite ramification/inertia degree formulas.
  None gives this canonical tame map, wild kernel and generator statement.

Validation: the final module compiled separately via the required scompile.py wrapper
as both a sandbox file and its library module, with no errors or warnings. No global build,
live-library write or direct git mutation was used. The theorem's only proof is `sorry`.

## Second reading by N8

I reread the current node and final signature clause by clause, and checked the source
paragraphs and reused inverse-limit definitions. The initial draft only existentially
asserted a primitive generator; I strengthened the rendering to the node's intended
universal assertion that every compatible primitive family generates topologically and
has the index-d property. The explicit `DenseRange` type-argument order was corrected
using the compiler diagnostic. Rechecked the Krull topology on H, the induced topology
on its kernel for finite quotients, and explicit inverse-limit topology in continuity,
density and closure; these are the required topologies. Exactness uses the actual kernel
and no extra tautological conjunct. No hypotheses of excellence, residue perfection or
positive characteristic were added. No item statement correction or dependency-module repair is needed. The H2 repair adds
the definition-node record described below, without duplicating any Lean definitions. This is the author's second pass; the maintainer's
independent delivery review remains the independent mathematical review.

The required delivery dry run passed: `OK (dry run): commit a31a1a1f4e passes the
preflight and compiles; nothing pushed`.


## New nodes

`def-per-tame-root-limit` records the four existing declarations `TameRoots.Order`,
`TameRoots.limitSubgroup`, `TameRoots.limitTopology`, and
`TameRoots.IsCompatiblePrimitiveFamily` in the unchanged module
`Sheaf.FieldTheory.TameRootsProduct`, with `existing: true`. The primary signature is
copied verbatim in `lean.statement`, all four names are listed in `lean.declarations`,
and the other three verbatim signatures are in `lean.note`. The source is ILO XVII §1.2
and the root limit in Stacks 0BUB. The definition applies to any field k and any natural
number p, with no characteristic assumption. It cites `def-weil-field` (Mathlib `Field`).
The positive coprime subtype is D_p; the subgroup imposes both the root and every
power-transition equation; the topology is the infimum of coordinate-induced discrete
topologies; the primitive predicate imposes exact order, normalization and compatibility.
LeanSearch returned eight related finite-root and general inverse-system declarations;
Loogle `rootsOfUnity` returned twelve finite-level declarations. Mathlib and upstream
grep found none of these limit definitions; project grep found this exact existing module.
The DAG exact-name search found only the theorem node `lem-exc-tame-roots-product`,
not a definition node for the general notion; `blueprint_refs.py search 'tame root'`
returned zero blueprint nodes. All results are recorded in the new node. No new module
or definition is introduced, and no result of `compatible_roots_product` is used.
For p=1 all positive orders remain; for p=0 only order 1 remains; order 0 is always
excluded. The definitions make sense in every field, whether or not primitive families
exist there. Existence remains a theorem rather than part of the definition.

## Returned delivery repair

H2: Replaced the extra theorem dependency `lem-exc-tame-roots-product` with the new
definition node `def-per-tame-root-limit`. All other original statement dependencies
are retained. The new node binds the four plain definitions actually used, so neither
a choice from the product theorem nor its positive-characteristic hypotheses enter
the trait theorem. The existing TameRootsProduct module is unchanged.

H9: Removed exactly the sixteen private `import` lines. The six `public import` lines
remain. The complete theorem signature is byte-identical to the returned packet and
to its `lean.statement`; its proof is still exactly `by sorry`.

Self-check of the repair: opened the current live item record and compared every field
with the saved packet; apart from the permitted dependency addition and Lean record,
the original statement and proof plan remain unchanged. Reopened the unchanged root-limit
source and matched each of the four declarations with the new definition node: positivity
and coprimality, subgroup equations, discrete coordinate topology, exact order and
normalization all agree. The actual map, its uniformizer formula, kernel quotient clause,
p=1 clause, universal primitive generator and index-d closure clauses are unchanged.
The maintainer's independent review at immutable head f4024d609a61 already checked these
clauses and their independent universes; this repair changes only the requested dependency
ownership and imports. No new mathematical claim or statement correction was made.
