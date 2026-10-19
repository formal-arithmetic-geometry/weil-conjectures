## Worker report

The module Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension states
AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isAffine.
Its only proof is `sorry`; no definition or helper theorem is introduced.
The item's node changes only in `lean`. No statement correction is needed.

Hypotheses and clauses, in node order:

- A field K: `(K : Type u) [Field K]`.
- A nonnegative integer c: `(c : ℕ)`, without an extra positivity assumption.
- The field bound: `hK : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c`.
- A K-scheme: `(X : Scheme.{u}) [X.Over (Spec (.of K))]`.
- Affineness: `[IsAffine X]`.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of K))]` together with
  `[QuasiCompact (X ↘ Spec (.of K))]`, the recorded scheme convention.
- Nonemptiness applies only to the first conjunct: `Nonempty X → ...`.
- The bound dim X + c: `HasTorsionEtaleCohomologicalDimensionLE X
  (((topologicalKrullDim X).unbotD 0).toNat + c)`.
  For a nonempty finite-type scheme over a field, Krull dimension is finite and nonnegative;
  hence the displayed conversion returns exactly its dimension. This avoids adding a
  separate dimension parameter or a finiteness hypothesis.
- The empty case is the second conjunct, `IsEmpty X → ...`.
- Every torsion abelian étale sheaf: `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`
  and `F.IsTorsion`, matching the dependency's local-section torsion predicate. There is
  no globally fixed annihilator, constructibility, or finiteness assumption on F.
- Every nonnegative q: `∀ q : ℕ`, including zero.
- Ordinary cohomology vanishes: `Subsingleton ((Etale.cohomology ... X q).obj
  ((DerivedCategory.singleFunctor _ 0).obj F))`.
  As in the dependency, a sheaf is put in degree zero and natural degrees are coerced
  to the integer grading of the ordinary derived-section functor. Subsingleton of the
  underlying abelian group expresses vanishing.

Dependency declarations read and reused:

- Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension:
  AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE, full definition read.
- WeilConjectures.Mathlib.Topology.KrullDimension: topologicalKrullDimAt;
  Mathlib.Topology.KrullDimension: topologicalKrullDim. The latter is the actual global
  dimension used here, the Krull dimension of the poset of irreducible closed subsets.
- def-weil-pbc-scheme-conventions is explicitly a convention-only record, not a
  declaration; use Mathlib AlgebraicGeometry.IsAffine, LocallyOfFiniteType and QuasiCompact.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  AlgebraicGeometry.Etale.cohomology, ordinary RΓ followed by homology.

Every proof dependency with a recorded module is imported non-publicly, except the
cohomological-dimension module already imported publicly. The proof-only dependency
sbc-lem-affine-space-smooth has no recorded module/declaration in this checkout and
contributes no import. No statement depends on that missing proof-only interface.
The theorem docstring transcribes all twelve current node proof steps and their inputs,
including strong dimension induction over all fields, finite direct image comparison,
the local field-model calculation, compactification, the exceptional degree-two stalk,
support filtration, spectral-sequence bounds and removal of the uniform exponent.
The blueprint node source was read; the current DAG proof includes its reviewed repairs.

Edge cases checked: c = 0 is allowed; nonempty zero-dimensional schemes receive bound c;
empty X is handled independently of Krull dimension's bottom value; q = 0 is included
in empty-scheme vanishing; zero sheaves satisfy the statements; characteristic p is not
excluded; neither reducedness, integrality, smoothness nor separatedness is imposed.
All universes and binders are explicit; the coefficient size u+1 agrees with the recorded
cohomological-dimension definition. Field and scheme sizes follow the existing same-universe
scheme-over-field convention. No extra small test category is quantified over.

Searches for the exact theorem:

- msearch.py LeanFinder: 'For an affine finite type scheme over a field of torsion
  cohomological dimension c, etale torsion cohomology vanishes above dimension plus c'.
  Eight unrelated results on cotangent cohomology and group Tor; no match.
- msearch.py Loogle: 'AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE,
  topologicalKrullDim'. Zero results; the project predicate is unknown to the service.
- msearch.py grep: 'cohomologicalDimension|CohomologicalDimension|affine.*torsion'.
  Seven unrelated affine-monoid and affine-space results; no theorem match.
- msearch.py LeanSearch: 'An affine finite type scheme over a field has torsion etale
  cohomological dimension at most its Krull dimension plus that of the field'.
  Unavailable: Internal Server Error, recorded without a negative verdict.
- rg in WeilConjectures and lean/Sheaf for
  'HasTorsionEtaleCohomologicalDimensionLE|topologicalKrullDim.*(unbot|toNat)|affine.*torsion':
  existing curve bounds and the predicate, but no general affine bound. Existing upstream
  dimension conversions use the same unbotD/toNat expression.
- grep -rn for 'thm-sc-affine-torsion-cd' in upstream WeilConjectures: no hits.
- rg for the new declaration name in dag/lean_names_upstream.json: no hits.
- scompile.py --source WeilConjectures.AlgebraicGeometry.EtaleSheaves read the published
  module missing from the older source checkout; it retains the local torsion interpretation.

Validation: scompile.py NQ thm-sc-affine-torsion-cd compiled the delivered module on the
server against live/side imports, with no errors or warnings. No local compiler was run.


## Second reading by NQ

Independent second reader: I did not write the module. I read the current node,
its full twelve-step proof, the blueprint source statement and proof, and Stacks
`algebra.tex`, `lemma-Noether-normalization` (Tag 00OY, lines 28024–28054).
The Stacks lemma assumes an arbitrary field and a finitely generated quotient
algebra; its nonzero-ring hypothesis is exactly the nonempty case of the
normalization argument. It imposes no perfectness, characteristic, domain or
reducedness hypothesis. The node itself, rather than Tag 00OY (an algebra input),
is the source of the cohomological theorem. Its explicit empty-scheme clause
resolves the bottom-dimensional case left implicit in the blueprint statement.
No statement correction was introduced by the first worker or this reading.

Object/hypothesis/conclusion inventory and matching, in node order:

1. An arbitrary field K: `(K : Type u) [Field K]`. Verdict: exact; no separable
   closure, algebraic closure or characteristic hypothesis is imposed.
2. A nonnegative integer c: `(c : ℕ)`. Verdict: exact, including zero.
3. Torsion cohomological dimension of K at most c: `hK :
   HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c`. Verdict: exact.
   I opened `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension` and read the
   definition, not just its name: it quantifies over all locally torsion abelian
   sheaves and natural q with c < q, and uses ordinary derived-section cohomology.
4. An affine K-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of K))]
   [IsAffine X]`. Verdict: exact. The `Over` instance provides the structure
   morphism; Mathlib `IsAffine` says its canonical map to Spec of global sections
   is an isomorphism. No integrality, smoothness or separatedness binder is added.
5. Finite type over K: `[LocallyOfFiniteType (X ↘ Spec (.of K))]
   [QuasiCompact (X ↘ Spec (.of K))]`. Verdict: the exact conjunction in the
   convention dependency, which is convention-only. I read Mathlib's defining
   signatures in `Morphisms/FiniteType`, `Morphisms/QuasiCompact` and `AffineScheme`.
   The first is local finite generation on affine opens and the second is
   quasi-compactness of the structure morphism, with no extra Noetherian binder.
6. Nonemptiness for the first conclusion: `Nonempty X → ...`. Verdict: exact;
   it does not prevent the separately quantified X from being empty.
7. The dimension-plus-field bound: the consequent is
   `HasTorsionEtaleCohomologicalDimensionLE X
   (((topologicalKrullDim X).unbotD 0).toNat + c)`. Verdict: exact. I opened both
   declarations recorded by `def-kun-dimension`: Mathlib `topologicalKrullDim`
   is `krullDim (IrreducibleCloseds X)` and upstream `topologicalKrullDimAt`
   is the infimum over open neighbourhoods. The theorem correctly uses the
   global dimension. A nonempty affine finite-type scheme over a field has a
   finite natural dimension (normalization and its dimension assertion); both
   conversions preserve that value. No additional dimension assumption is needed.
8. If X is empty: the second conjunct starts `IsEmpty X → ...`. Verdict: exact,
   independently of the nonempty implication and its dimension conversion.
9. Every torsion abelian étale sheaf F: `∀ (F : Sheaf X.smallEtaleTopology
   AddCommGrpCat.{u + 1}), F.IsTorsion → ...`. Verdict: exact. I read the current
   published `WeilConjectures.AlgebraicGeometry.EtaleSheaves` using `scompile.py
   --source`, and then the actual `CategoryTheory.Sheaf.IsTorsion` definition in
   `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` (also
   checked against current server source). Each section becomes finite-order on
   a covering sieve; the integer may depend on the restricted section. There is
   no uniform exponent, constructibility or finite-stalk hypothesis.
10. Every degree q ≥ 0 and vanishing H^q(X,F): `∀ q : ℕ, Subsingleton
    ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1} X q).obj
    ((DerivedCategory.singleFunctor _ 0).obj F))`. Verdict: exact, including q=0.
    I opened `Etale.cohomology` in `Derived/LowerShriek`: it is
    `rightDerivedGlobalSections A X ⋙ DerivedCategory.homologyFunctor A i`.
    Placing F in degree zero therefore gives ordinary sheaf cohomology; natural
    q coerces to integer i. Subsingleton of an abelian group's carrier is its
    vanishing, not the invalid `IsZero` predicate on a bare type.

Edge cases: the empty scheme is covered without assigning it a natural dimension;
nonempty zero-dimensional X receives bound c; c=0 is allowed; q=0 is explicitly
included in the empty case. The zero sheaf is among the quantified F. There is no
index set or auxiliary nonempty family. Every characteristic is allowed, including
p-primary torsion in characteristic p. Nilpotents and disconnected schemes are
allowed. Universe u is declared and all binders are explicit; K and X share the
existing scheme-over-field convention, and coefficients have exactly the u+1 size
of the recorded cohomological-dimension predicate and derived-sections API. There
is no independent smaller test universe or extra size equality.

Independent duplicate searches used different wording from the worker:

- LeanFinder via msearch.py: “Artin vanishing: torsion abelian etale sheaves on an
  affine variety have vanishing cohomology above dimension plus the base field
  cohomological dimension”. Eight hits concern cotangent cohomology, group Tor,
  derived truncation and affine limits; none states this theorem.
- Grep via msearch.py: `Artin.*vanish|affine.*torsion|torsion.*affine` returned nine
  unrelated affine-monoid, affine-space and connection-torsion hits.
- Direct rg of Mathlib, upstream WeilConjectures and project lean/Sheaf with
  `artin.?vanish|affine.*cohomolog|cohomolog.*affine|torsion.*dimension|dimension.*torsion`
  found curve bounds, the existing cohomological-dimension predicate and unrelated
  quasi-coherent/Artin–Schreier results. I separately searched the predicate and
  the proposed full declaration name: there is no existing general affine bound.
- Loogle query `"cohomology" "IsAffine"` was rejected by the service's parser;
  this is not evidence of absence. LeanSearch's independently worded higher
  étale cohomology query was unavailable (Internal Server Error), also not a
  negative search. The successful LeanFinder and grep searches above supply the
  concept search; no exact declaration was found to reuse.

No new nodes or dependency modules are present. There are no definitions to be
hollow and no private copies of dependency notions. The only theorem proof is
`sorry`. I checked the module/declaration source and blueprint docstrings and
matched all twelve proof steps and their cited inputs to the node. I verified
programmatically that `lean.statement` is verbatim the theorem signature through
the conclusion before `:= by`, and checked the binders by eye.

Mismatches found: none. Changes: appended this independent second-reading report;
the Lean module and node record remain as written. Validation: the delivered
module compiled using scompile.py on the server, both sandbox and library passes,
with no errors or warnings (3.4 s and 3.7 s respectively). No local compiler or
library build was run.
