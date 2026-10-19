## Worker report

The module `Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology` states
`AlgebraicGeometry.Etale.constantSheaf_cohomology_of_isStrictlyHenselianLocalRing`.
Its only proof is `sorry`; it introduces no definitions or additional nodes. The node is
unchanged except for its `lean` field.

Hypothesis and conclusion correspondence:

- The commutative strictly henselian local ring is `(R : Type u) [CommRing R]
  [IsStrictlyHenselianLocalRing R]`. The last class extends `HenselianLocalRing`, which
  includes the local-ring structure. Thus no separate maximal ideal is additional data:
  it is `IsLocalRing.maximalIdeal R`.
- `X = Spec R` is written explicitly as `Spec (CommRingCat.of R)` at every occurrence.
- The finite abelian group is `(A : AddCommGrpCat.{u + 1}) [Finite A]`.
  The size is the established coefficient convention for the small étale site of a
  `Scheme.{u}`. Every finite abelian group admits such a carrier, including the trivial group.
- Invertibility of its order is `_hA : IsUnit (Nat.card A : R)`; the underscore avoids an
  unused binder warning while retaining exactly the node's hypothesis.
- Its associated constant étale sheaf is
  `(constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A`.
  This is Mathlib's sheafification of the constant presheaf, not a copied construction.
- Cohomology of that sheaf is the recorded `Etale.cohomology` evaluated on its image under
  `DerivedCategory.singleFunctor ... 0`. No alternative definition of cohomology is used.
- The degree-zero clause is `Nonempty (H0 ≅ A)` in `AddCommGrpCat`: an isomorphism of
  abelian groups, expressing the displayed identification with `A`.
- The positive-degree clause is `∀ (q : ℕ), 0 < q → IsZero (Hq)`, with the degree
  cast to `ℤ` for the derived cohomology API. Natural-number degrees cover exactly the
  nonnegative degrees in the source. Vanishing is categorical zero in the category of
  abelian groups, not `IsZero` on a bare type. Both clauses are joined by `∧`.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category and `Spec`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to
  `AddCommGrpCat.{u + 1}`. The scheme-conventions node explicitly introduces no new notion.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology`, `rightDerivedGlobalSections`.
- The two recorded proof modules are imported without `public`:
  `Sheaf.Paper.StrictlyHenselianEtaleAcyclic`, theorem `strictlyHenselian_etale_acyclic`,
  and `Sheaf.AlgebraicGeometry.StrictlyHenselianConstantHZero`, theorem
  `AlgebraicGeometry.Etale.nonempty_constantSheaf_cohomology_zero_iso`.
  Their signatures supply precisely the two proof steps in the theorem docstring.

Edge cases checked: the trivial coefficient group has cardinality one, so invertibility
holds and both conclusions have their expected meaning. Degree zero is included explicitly;
positive degrees include degree one. A strictly henselian local ring is nontrivial, so its
spectrum is nonempty; the excluded zero ring is already excluded by the source hypothesis.
No noetherianity, residue-characteristic restriction beyond invertible order, or field
hypothesis is imposed. No statement dispute or correction is needed.

Searches (via `msearch.py NN sbc-lem-strict-henselian-constant-cohomology`):

- LeanFinder: "The cohomology of a finite constant abelian sheaf on the spectrum of a
  strictly henselian local ring is its value in degree zero and zero in positive degrees".
  Eight hits concern cotangent complexes and group cohomology; none is this statement.
- Loogle: `IsStrictlyHenselianLocalRing, Sheaf.H`: zero hits, unknown identifier
  `IsStrictlyHenselianLocalRing` in the Mathlib search service.
- Mathlib grep: `henselian|constantSheaf`, restricted to `AlgebraicGeometry/Sites`:
  one import hit in `ElladicCohomology.lean`, no matching statement.
- LeanSearch: "etale cohomology of a strictly henselian local ring constant sheaf":
  unavailable, Internal Server Error. Recorded as unavailable, without a search verdict.
- Source-repository `rg`: `strict.henselian|StrictlyHenselian|constant.*cohomology`, and
  the exact node id. Read `WeilConjectures/AlgebraicGeometry/Sites/StrictlyHenselian.lean`
  in full. It has the separate results `subsingleton_H_of_isStrictlyHenselianLocalRing`
  and `hZeroConstantSheafAddEquiv` using `Sheaf.H`; neither states the combined theorem
  with the finite/invertible-order hypotheses and the node's recorded derived encoding.
- Project `lean/Sheaf` grep: `constantSheaf.*cohomology|constant.*henselian` and
  strict-henselian keywords. Found the degree-zero dependency above, but no combined result.
- Read the exact blueprint source file named by the node, including its proof paragraph.
  The DAG's two proof steps retain its conclusions using the existing general acyclicity
  and degree-zero comparison rather than repeating the source's informal contractibility.

Validation: the delivered module compiled cleanly through `scompile.py` on the server,
with the degree-zero dependency resolved through the wrapper's private side overlay.
No local Lean compiler or library build was run. The dry-run delivery result follows below.

## Second reading by NN

I independently read the sandbox node and module against the blueprint file
`sec-smooth-base-change/sk-rem-rest/sbc-lem-strict-henselian-constant-cohomology.md`
and Stacks `etale-cohomology.tex`, Tag 03QO (the lemma and its proof). The Stacks
lemma assumes only that R is strictly henselian local; its surrounding section
adds no noetherianity or characteristic hypothesis. The blueprint retains finite
coefficients of invertible order, although Stacks gives vanishing for all abelian
sheaves. The Lean correctly retains these hypotheses.

Object, hypothesis, and conclusion checklist (all verdicts: match):

1. Commutative local ring (R, m): `(R : Type u) [CommRing R]` with
   `[IsStrictlyHenselianLocalRing R]`. I read the recorded upstream class: it extends
   `HenselianLocalRing R`, including `IsLocalRing R`, and requires separably closed
   residue field. The maximal ideal is canonical, not extra input data.
2. Strict henselianity: the same class is precisely the terminology dependency;
   neither algebraic closedness nor a field structure is substituted.
3. Scheme X = Spec R: every occurrence is `Spec (CommRingCat.of R)`, using Mathlib's
   scheme and affine spectrum, rather than an arbitrary strictly local scheme.
4. Finite abelian coefficient group: `(A : AddCommGrpCat.{u + 1}) [Finite A]`.
   The category bundles exactly the abelian group structure; `Finite` imposes no
   choice of enumeration or extra algebraic structure.
5. Order invertible in R: `(_hA : IsUnit (Nat.card A : R))`. For finite A,
   `Nat.card A` is its order, and the natural-number cast is the canonical ring map.
6. Associated constant étale sheaf: `(constantSheaf
   (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A`.
   I opened Mathlib's `constantSheaf`, which is the constant presheaf followed by
   sheafification, and `smallEtaleTopology`, which uses the category of schemes
   étale over X with the induced étale covering topology. These are the recorded
   dependency notions, not private versions.
7. Cohomology: `cohomology AddCommGrpCat.{u + 1} (Spec ...) q` applied to
   `DerivedCategory.singleFunctor ... 0` of that sheaf. I read `cohomology` and
   `rightDerivedGlobalSections` in LowerShriek: they are derived global sections
   followed by degree-q homology, as the cohomology dependency specifies.
8. Degree zero: `Nonempty (H0 ≅ A)`, an isomorphism in AddCommGrpCat, expresses
   the displayed identification of abelian groups. The node's conclusion does not
   additionally demand a chosen map or naturality data.
9. Every positive degree: `∀ (q : ℕ), 0 < q → IsZero (Hq)`; the cast `(q : ℤ)`
   supplies the derived API's degree. Together with clause 8 this covers exactly
   all nonnegative degrees of the source, with both clauses under the same R and A.

I opened every statement dependency's node and recorded signatures. The scheme
conventions dependency explicitly introduces no new notion. I also opened both
proof dependency modules: `strictlyHenselian_etale_acyclic` has the same derived
cohomology encoding and quantifies over every abelian sheaf and integer p >= 1;
`nonempty_constantSheaf_cohomology_zero_iso` gives a natural isomorphism whose
component at A supplies clause 8. Their imported statements support the two
numbered proof steps in the docstring. There are no new nodes or dependency
modules in this delivery to review.

Edge cases: q = 0 is the first conjunct, q = 1 is included in the second, and
negative degrees are not claimed by the node. The trivial group is allowed:
its order is one, hence invertible. An empty group carrier is impossible for an
abelian group, and no index family is introduced. The zero ring and empty
spectrum are already excluded by the local-ring hypothesis (proper maximal
ideal); no extra nonemptiness hypothesis was added. All ring characteristics
are covered subject to exactly the invertible-order hypothesis. The ring
universe u is arbitrary. The coefficient universe u+1 is the recorded small
étale cohomology convention; any finite abelian group has a representative in
this universe, so the finite coefficient cases are all covered. No unbound
universe or variable occurs in the declaration.

Independent searches: LeanFinder via msearch, query "strict local scheme finite
abelian coefficients higher etale cohomology vanishes", returned eight unrelated
cotangent/étale-algebra and limit results, no match. I used rg with
`strict.*[Hh]ensel`, `[Hh]ensel.*cohom`, `hZeroConstant`, and
`constantSheaf_cohomology` over Mathlib algebraic geometry, upstream sites, and
project Sheaf modules, and narrowed the project/upstream search to
`constantSheaf_cohomology|hZeroConstantSheafAddEquiv|subsingleton_H_of_isStrictlyHenselianLocalRing|constantSheaf.*cohomology_zero`.
I read upstream StrictlyHenselian.lean in full: its positive-degree theorem uses
`Sheaf.H` and its degree-zero declaration is an additive equivalence, neither the
combined theorem in the recorded derived encoding. The project degree-zero
module is the cited proof dependency, not a duplicate combined statement.
The worker's additional Loogle and unavailable LeanSearch records remain above.

No mathematical, signature, dependency, docstring, or convention mismatch found.
No Lean or node changes made; this independent review is the only addition.
The module has one named theorem with only `sorry`, no definitions, local notation,
or private instances. Its source/blueprint docstrings and proof steps match the
node, and the node's lean.statement is verbatim the module's theorem signature.
