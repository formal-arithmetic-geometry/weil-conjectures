## Worker report

This is a stage-2 statement delivery for `lem-trf-abhyankar-inequality`, not a
repeat of NU's stage-1 split. The current node has no `lean` record. NU's
2026-10-18 merged delivery supplied its proof plan, rather than a Lean statement.
The mathematical statement is unchanged.

The main declaration is `ValuationSubring.abhyankar_inequality` in
`Sheaf.FieldTheory.AbhyankarInequality`. Its two canonical-map definitions have
real data. The theorem and the named locality property have `sorry` proofs,
as required at stage 2. The locality property is exactly the node's existing
maximal-ideal intersection clause, used to construct the canonical residue map;
it introduces no additional mathematical assumption or independent lemma.
All four declarations are recorded in `lean.declarations`.

Hypotheses and clauses, individually:

- Fields F and K are independent-universe types with `[Field F] [Field K]`.
  `[Algebra F K]` represents the given inclusion: every homomorphism from a field
  to a field is injective. There is no assumption that the valuation is trivial
  on F, no restriction on characteristic, and no same-universe constraint.
- Finite generation as a field is `hfg : (⊤ : IntermediateField F K).FG`.
  In particular it is not finite generation as an F-algebra, which would wrongly
  force the extension to be algebraic.
- The given valuation ring is `A : ValuationSubring K`, Mathlib's subring with
  the element-or-inverse membership property. Mathlib supplies its local ring
  and fraction-field structures, so these are not extra hypotheses.
- A_F is `A.comap (algebraMap F K)`. This is the actual inverse-image subring,
  hence A intersect F, rather than an independently selected valuation ring.
- Its map into A is `A.comapInclusion (algebraMap F K)`, obtained by
  `RingHom.restrict`; it applies precisely `algebraMap F K` to the underlying
  element. `comapInclusion_isLocalHom` states the node's locality assertion.
  Locality identifies the inverse image of m_A with m_A_F. Units are likewise
  exactly the inverse images of units, so A_F^x=A^x intersect F^x.
- Gamma_K is the actual group quotient `Kˣ ⧸ A.unitGroup`. Mathlib's
  `A.unitGroup` is the kernel of the valuation on K^x and is canonically
  isomorphic to A^x by `ValuationSubring.unitGroupMulEquiv`.
- The composite `(QuotientGroup.mk' A.unitGroup).comp
  (Units.map (algebraMap F K).toMonoidHom)` sends F^x to Gamma_K. Its kernel
  is A_F^x by the preceding unit intersection. Thus its range is exactly the
  canonically embedded Gamma_F, and quotienting Gamma_K by that range is the
  stated Gamma_K/Gamma_F. No ordered-group quotient, arbitrary subgroup,
  or arbitrary group map is assumed.
- Kappa_K and kappa_F are respectively `IsLocalRing.ResidueField A` and
  `IsLocalRing.ResidueField (A.comap (algebraMap F K))`. These are the actual
  maximal-ideal quotients, with their canonical field structures.
- `A.comapResidueFieldMap (algebraMap F K)` is Mathlib's
  `IsLocalRing.ResidueField.map` applied to the restricted inclusion and its
  named locality proof. It sends the residue of a to the residue of its image.
  Its `toAlgebra` is supplied explicitly to `Algebra.trdeg`, so this is exactly
  the induced residue extension, without an arbitrary choice of algebra action.
- Rational rank is `AddCommGroup.rationalRank` of the additive form of the
  relative quotient. Its definition is `Module.rank ℚ (ℚ ⊗[ℤ] G)`: the full
  cardinal dimension, including infinite groups and groups with torsion.
  Tensor symmetry identifies this with the node's G tensor_Z Q; putting Q
  first uses Mathlib's canonical left scalar action and changes no object up
  to the canonical tensor symmetry.
- The conclusion adds this rational rank and the residue transcendence degree
  and compares their cardinal sum with `Algebra.trdeg F K`, using `≤`, exactly
  the displayed inequality. No finiteness predicate is added to either summand,
  and neither summand is replaced by `Cardinal.toNat` or finite dimension.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`, including
  its full class signature and nontrivial division-ring inheritance.
- `def-kun-transcendence-degree`: `Algebra.trdeg`, in
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`; its definition is the supremum
  of cardinalities of algebraically independent subsets.
- Proof dependency `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`:
  `exists_finset_isTranscendenceBasis` in `Mathlib.FieldTheory.FinTrdeg`, with
  `[FinTrdeg F K]`; the finite-field-generation interface supplies this instance.
  `FinTrdeg` is imported and also provides the statement's field-generation API.
- The existing unstated prerequisite `def-trf-rational-rank` is supplied in this
  delivery as `AddCommGroup.rationalRank`, module `Sheaf.GroupTheory.RationalRank`,
  and added to the item's `stmt_deps`. See Dependency modules below.

Source checked: the source URL in the node is accessible online. I read
Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, p. 8,
§2.1, definitions of E and F immediately before Lemma 2.1.2 and the lemma
and its proof. It uses the rationalized quotient of value groups and the
relative residue transcendence degree and gives their sum as bounded by field
transcendence degree. This confirms the node; no statement correction is needed.
The report does not change the node's archival-source availability metadata.
Source URL: https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf
The Lean docstring carries all eight steps of the node's polynomial proof plan.

Edge cases checked mathematically before writing:

- F=K with a nontrivial valuation, including Q and Z_(p): the relative value
  group is trivial and the residue extension is the identity, giving 0≤0.
  This avoids the false absolute inequality previously corrected in stage 1.
- The trivial valuation A=K: the value group is trivial and the residue
  extension is F→K, so the conclusion is equality.
- Algebraic finitely generated extensions: the right side is zero, forcing
  both relative summands to be zero; torsion in the relative group is retained
  and killed by rationalization, rather than incorrectly prohibited.
- Purely value-transcendental and purely residue-transcendental extensions
  contribute to their respective summands. Empty independent families are
  allowed by the proof plan, covering either zero summand and trdeg=0.
- Infinite absolute value rank is permitted: only the relative rationalization
  is bounded. No finite generation of the abelian quotient is assumed.
- Characteristic zero, positive characteristic, and mixed residue
  characteristic are all admitted. Universe u for F and v for K are independent;
  both summands and the right side lie in Cardinal.{v}.
- For rational rank, zero and finite torsion groups have rank zero, Z has rank
  one, and an infinite direct sum is not collapsed to zero by `finrank`.

Searches actually run (msearch.py, group Q15, this item):

- LeanFinder: “Relative Abhyankar inequality for a valued field extension:
  rational rank of quotient value group plus residue transcendence degree
  bounded by field transcendence degree”: eight hits including
  `Field.insepDegree_le_rank` and `IntermediateField.relrank` results;
  none states the valuation inequality.
- Loogle: `ValuationSubring, Algebra.trdeg`: zero hits.
- Mathlib grep: `Abhyankar|abhyankar|rationalRank|rational_rank`: zero hits.
- LeanSearch: “Relative Abhyankar inequality for valued fields”: eight hits
  about valuation comparison, uniformizers and rank-one local fields; no match.
- LeanFinder: “Canonical local ring homomorphism from the restriction of a
  valuation subring along a field embedding and induced residue field embedding”:
  found `Valuation.HasExtension` local-hom instances and
  `IsLocalRing.ResidueField.map`. Their signatures and source were read. The
  former use two valuations and `HasExtension`; the present interface instead
  takes the node's single valuation subring A and its literal comap. The
  latter is reused directly for the quotient map's data.
- LeanFinder: “Rational rank of an abelian group as dimension over Q of its
  tensor product with Q”: `AddGroup.rank`, `Module.rank`, `Module.finrank`
  and special number-field ranks. `AddGroup.rank` was opened and is the minimum
  number of generators of a finitely generated group, not rational rank.
  `Module.rank` is reused to define the actual rationalization dimension.
- Loogle: `Module.rank, TensorProduct`: five hits, tensor rank/base-change
  results. None defines the rational rank of an arbitrary abelian group.
- Mathlib grep in LinearAlgebra: `rationalRank|rational_rank|rational rank`:
  zero hits.
- Direct rg over Mathlib, upstream WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json for the proposed names: no declarations collide.
  Direct rg for Abhyankar/abhyankar found only the different tame-DVR ramification
  lemma and the downstream finite-height theorem; neither is this inequality.
  Upstream grep for the item id found no declaration. DAG search found the
  already-existing `def-trf-rational-rank`, so no duplicate node was created.

No STATEMENT-DISPUTED issue remains. No statement is corrected. No new node is
created; the original status and all non-owned fields of each node are preserved.
Compilation and preflight results are recorded below after verification.

## Dependency modules

`def-trf-rational-rank` is an existing genuine DAG definition node with neither
usable Lean declaration nor Mathlib match. Under the human's 2026-10-16
bottom-up/nothing-waits instruction it is stated in this same delivery, rather
than duplicated or deferred. Its copy changes only `lean`, with `lean.note`
explaining this. `Sheaf.GroupTheory.RationalRank` defines
`AddCommGroup.rationalRank (G : Type u) [AddCommGroup G] : Cardinal.{u}` by the
actual tensor rationalization. It uses Mathlib dimension and tensor product,
with no postponed construction, finite-generation assumption, or truncation.
The base node's `status: unsplit` is preserved, as workers may not change it.

Verification: scompile.py compiled both modules separately in dependency order,
with no errors or non-sorry warnings. The first dry run found only the stored
signature prefix: its extractor starts at `def`, so the node record now omits
the `noncomputable` modifier while the actual definition remains noncomputable.
No Lean declaration or mathematical statement changed in that formatting repair.

The repaired dry run printed `OK (dry run): commit c5122c6229 passes the preflight
and compiles; nothing pushed`. It accepted the existing prerequisite as a
dependency module and the item with the added dependency, with no statement
correction and no non-owned node-field changes.

## Second reading by Q15

Independent maintainer reading, 2026-10-18, of immutable delivery
671179884c5d39adcbd44836c8e8a3b46ef5f1e4. This reading was performed by a reader
who neither wrote nor previously second-read the delivery. It replaces the
original placeholder in this section; the Worker report above is preserved.

I read the item node, all three statement-dependency nodes, both delivered Lean
modules and every declaration/docstring, and the finite-transcendence-basis
proof dependency. I compared the mathematical statement with Temkin, Stable
modification of relative curves, arXiv:0707.3953v3, section 2.1, pp. 7–8,
including the notation immediately before Lemma 2.1.2 and that lemma's proof.
The source is https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf.
It states the relative inequality for arbitrary valued-field extensions;
finite field generation is the node's intended specialization. No assumption
of finite height, completeness, separability, or trivial base valuation is used.

Clause-by-clause comparison:

- F and K: independent `Type u` and `Type v`, with `Field` instances.
  `Algebra F K` gives the specified injective field map. The Field definition
  includes commutativity, nontriviality and inverses. This matches
  `def-weil-field`; no characteristic hypothesis is added.
- Finite field generation: `(⊤ : IntermediateField F K).FG` means that a
  finite set generates the top intermediate field, by
  `IntermediateField.FG` in Adjoin/Defs.lean:653. It is the field-generation
  hypothesis, with no stronger algebra-finite-generation assumption.
- A: `ValuationSubring K` has exactly the subring and element-or-inverse
  property. Its existing local-ring and fraction-field instances supply the
  node's structural clauses without extra assumptions.
- A_F: `A.comap (algebraMap F K)` is the literal inverse-image subring.
  `comapInclusion` restricts the given field homomorphism, using real data
  from `RingHom.restrict`. Its named `IsLocalHom` theorem is exactly the
  node's maximal-ideal intersection property. Units are reflected because
  membership of an inverse is reflected by this comap; zero is a nonunit
  on both sides. Thus the unit-intersection clause also holds.
- Value groups: `Kˣ ⧸ A.unitGroup` uses Mathlib's actual subgroup of units,
  canonically identified with A's units by `unitGroupMulEquiv`. The range
  of the displayed composite from Fˣ is the image of Γ_F. Its kernel is
  the unit group of A_F, so the induced Γ_F map is injective and the second
  quotient is exactly Γ_K/Γ_F. It is a quotient abelian group, with torsion
  allowed; it is not an ordered-group quotient or an arbitrary subgroup.
- Residue fields: `IsLocalRing.ResidueField` is the maximal-ideal quotient.
  `comapResidueFieldMap` uses the existing `ResidueField.map` quotient
  construction on the restricted inclusion and its named locality theorem.
  The induced field homomorphism is injective. Its explicit `toAlgebra`
  fixes the canonical residue extension used by `Algebra.trdeg`.
- Rational rank: the dependency module defines
  `Module.rank ℚ (ℚ ⊗[ℤ] G)` for any additive commutative group. Tensor
  symmetry identifies this with G tensor_Z Q, with its rational action.
  It uses cardinal dimension, not `finrank`, and has no finite-generation
  or torsion-free hypothesis. This states `def-trf-rational-rank` exactly.
- Conclusion: cardinal addition of relative rational rank and residue
  transcendence degree is bounded by `Algebra.trdeg F K`. All three
  cardinals lie in universe v; F's universe u is unrestricted. Mathlib's
  `Algebra.trdeg` is the dependency's supremum of independent-subset sizes.

I checked the eight-step proof docstring against the node. Finite field
generation gives finite transcendence degree via `fg_top_iff`, `FinTrdeg`
and `exists_finset_isTranscendenceBasis`. Coefficient normalization, distinct
relative values of monomial terms, and division by a minimal term establish
noncancellation and algebraic independence. The finite-family bounds then
bound rational rank and residue transcendence degree together. The argument
allows empty families and torsion in the relative group. Stacks fields.tex,
labels lemma-transcendence-degree and definition-transcendence-degree
(Tags 030F/030G), and more-algebra.tex, lemma-inequality-general (0ASH), were
read as well. The latter is correctly described as inspiration for the
polynomial argument, not applied outside its finite-extension hypotheses.

Edge cases checked: F=K, including a nontrivial base valuation (both relative
summands zero); trivial A=K (equality); finite algebraic extensions (relative
value torsion has rational rank zero); zero transcendence degree; either empty
independent family; purely value or residue transcendence; infinite absolute
rank; all characteristics and mixed residue characteristic. The rank definition
also retains infinite rank and kills torsion correctly. No case is excluded by
an equality of universes or an additional structure hypothesis.

Independent searches: direct rg over Mathlib, upstream WeilConjectures, and
Q15 lean/Sheaf for Abhyankar, rational rank/rationalRank/rational_rank and the
helper names found no exact existing statement or rational-rank definition.
The other Abhyankar modules concern tame DVR ramification or the downstream
height bound. LeanSearch queries for rationalization dimension and the relative
valuation inequality returned group-generator rank or specialized valued-field
results, not these declarations. Loogle `ValuationSubring, Algebra.trdeg`
returned zero declarations. The existing `Module.rank`, tensor product,
`ValuationSubring.comap`, unit subgroup and `ResidueField.map` APIs are reused.
The existing rational-rank DAG prerequisite is supplied in this delivery under
the nothing-waits rule, without creating a duplicate node.

Both `lean.statement` strings match their file signatures verbatim, beginning
at `theorem` or `def` as required. All four main-module declarations are listed
in the item's record. The dependency's required note explains its missing
interface. The item changes only `lean` and adds rational rank to `stmt_deps`;
the dependency changes only `lean`. No statement correction or citer audit is
needed. Every definition has real data; the only two postponed proofs are
named theorems with `sorry`, source/blueprint docstrings, and matching clauses
of the item node. No local theorem proof is supplied. No line exceeds 100
characters and `autoImplicit` is false.

Reproduction on 2026-10-18:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q15 \
  lem-trf-abhyankar-inequality \
  snapshot/lean/Sheaf/GroupTheory/RationalRank.lean \
  snapshot/lean/Sheaf/FieldTheory/AbhyankarInequality.lean
```

The wrapper exited 0. Private overlay RationalRank: 1.1 s; preliminary rank
module: 1.4 s; first sandbox: 1.3 s; rank library check: 1.1 s; second sandbox:
1.7 s; Abhyankar library check: 1.7 s. No errors or unexpected warnings were
reported. The installed wrapper currently performs the private side overlay
on the server and confirms there; it does not perform a local-machine compile.
Only this prescribed wrapper was invoked; no direct ssh, global build, live
Lean edit, delivery or merge was performed.

The current route-pivot dropped-node list has no intersection with this item's
or its rational-rank dependency's references. No route-pivot repair note exists
for this item, and no dropped machinery or pro-etale substitute is introduced.

Finding H11: the delivered Second reading section was only a placeholder.
This completed independent reading repairs that report defect. The mathematics,
Lean files and node records need no change. Verdict: FIX, report only.
