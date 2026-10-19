## Worker report

The module `lean/Sheaf/AlgebraicGeometry/LeftTExactDerivedDirectImage.lean`
states the blueprint lemma for a morphism `f : X ⟶ Y` of schemes and a bounded-below
étale derived object `E` on `X`. The integer `b` is explicit. The hypothesis
`hE` renders, for every integer `i < b`, the clause `\mathcal H^i(E)=0` as
`IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj E)`. The conclusion renders,
for every `i < b`, the clause `\mathcal H^i(Rf_*E)=0` as `IsZero` of the corresponding
homology object after `rightDerivedLowerStarPlus`. The direct image is the recorded
`AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, and the derived category is the
recorded `DerivedCategory.Plus` specialization to sheaves of abelian groups.

The proof is `sorry`, as required at stage 2. Its source proof uses the
hypercohomology spectral sequence from `def-weil-pbc-hypercohomology-filtrations`;
that proof dependency is not needed by the statement module.

Recorded dependency declarations used:

- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  including `DerivedCategory.Plus` and `DerivedCategory.Plus.homologyFunctor`.
- `def-weil-pbc-direct-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, including
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`.

Edge cases checked: `b` is any integer (including negative and zero); the quantifier
allows an empty range when no integer is below `b`; `X` and `Y` are arbitrary schemes,
including empty schemes; and no nonzero or characteristic assumption is introduced.
The abelian-sheaf coefficient universe is `AddCommGrpCat.{u + 1}`, matching the small
étale-site convention in the dependency declaration.

Searches made:

- `msearch.py ... leanfinder "left t exactness derived direct image cohomology vanishing schemes etale"`:
  no exact target theorem; returned unrelated Mayer–Vietoris, étale-locus, and `IsEtale` declarations.
- `msearch.py ... loogle "isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE"`:
  unavailable/no hit for the unqualified query.
- `msearch.py ... grep "tensor-t-est" AlgebraicGeometry`:
  no match.
- `rg` in the source and project trees found the exact generic theorem
  `CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE`
  (source `WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean:115-132`)
  and the recorded étale functor `rightDerivedLowerStarPlus`; the generic theorem does
  not itself state the scheme-level target, so this module supplies the target statement.

## Second reading by NL

Final verdict: the original wrapper has the right mathematical statement but
violates H4 by restating an existing theorem. I dropped its module and recorded
`existing: true` for
`CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE`
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
This supersedes the Worker report's conclusion that the wrapper is necessary.

I read the original blueprint node at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-tensor-t-est.md`.
It is verbatim the DAG statement and has no surrounding scheme, finiteness, field,
or torsion assumption. I also read Stacks 03PY in `etale-cohomology.tex`
(direct image along any scheme morphism and its left exactness), 071J in
`sites-cohomology.tex` (derived pushforward on bounded below derived categories),
and 015J in `derived.tex` (the hypercohomology spectral sequence and finite
convergent filtration). These agree with the node and its proof.

Object, hypothesis, and conclusion checklist, with the exact specialization:

- Schemes X and Y and morphism f: in the original wrapper these are
  `{X Y : Scheme.{u}} (f : X ⟶ Y)`. In the recorded existing theorem take
  `C = Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`,
  `D = Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}`, and
  `F = AlgebraicGeometry.Etale.lowerStar AddCommGrpCat.{u + 1} f`.
  Verdict: same schemes, small étale sites, and canonical direct image.
- Bounded below E: take `K = E : DerivedCategory.Plus C`. Verdict: exactly
  Dplus(X_Et) with abelian-group sheaves; no torsion condition.
- Integer bound b: take `n = b : ℤ`. Verdict: arbitrary integer, not a natural
  degree or a nonnegative bound.
- Vanishing hypothesis for every i < b: the wrapper uses
  `hE : ∀ i : ℤ, i < b → IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj E)`.
  The existing theorem uses `[K.IsGE n]`. I opened Mathlib's
  `DerivedCategory.Plus.isGE_ι_obj_iff`, `DerivedCategory.isGE_iff`, and
  `DerivedCategory.Plus.homologyFunctor`: the latter is homology after the
  inclusion, and the former two identify IsGE exactly with this vanishing.
  Verdict: equivalent hypothesis, with no strengthening.
- Derived direct image Rf_*E: I opened the recorded dependency definitions.
  `lowerStar` is sheaf pushforward along scheme base change, with sections
  F(V ×_Y X); `rightDerivedLowerStarPlus` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` is
  definitionally `F.rightDerivedFunctorPlus`. Verdict: the same canonical functor.
- Conclusion for every i < b: specialize the existing theorem's implicit
  `q : ℤ` to each i and `hq : q < n` to i < b. It returns exactly
  `IsZero ((DerivedCategory.Plus.homologyFunctor D i).obj
    (F.rightDerivedFunctorPlus.obj E))`. Verdict: all requested degrees, same
  strict inequality and no additional conclusion.
- Generic structural hypotheses: Abelian, HasDerivedCategory, EnoughInjectives
  and F.Additive are supplied canonically for these sheaf categories and this
  direct image. I read the source sheaf Grothendieck/derived-category instances
  and `Etale.lowerStar_additive`. They impose no additional scheme hypotheses.

Dependencies read: the node records and the source module
`Sheaf.AlgebraicGeometry.DerivedCategories` for D, Dplus and homology; and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` plus the derived coherence
module for lowerStar and rightDerivedLowerStarPlus. I opened the existing theorem
itself, including its full signature and proof (source lines 115–132). It is
universe-polymorphic, so specializing to these categories introduces no new
universe equality. The node's `lean.statement` is copied verbatim from that
signature, and `lean.note` records the complete specialization.

Edge cases: b = 0 and negative b are retained. Unlike the Worker's report, the
integer set i < b is never empty (b - 1 belongs to it); no empty-range argument
is used. E = 0 and empty schemes are allowed. There is no field or characteristic
assumption and no coefficient integer n. No index family is introduced, so there
is no nonempty-index requirement. The small-site convention uses
`Scheme.{u}` and `AddCommGrpCat.{u + 1}` exactly as the dependency encoding.

Independent searches, with different terms from the worker:

- `msearch.py ... leanfinder "right derived additive functor preserves lower cohomology bound"`
  returned generic derived-category lower-bound and right-derived-functor
  declarations, including `DerivedCategory.isGE_Q_obj_iff`; no special replacement
  was needed beyond the upstream theorem found by source search.
- `msearch.py ... loogle "CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE"`
  reports unknown identifier in the public Mathlib index (the theorem is upstream).
- `msearch.py ... leansearch "right derived functor cohomology vanishes below a bound"`
  was unavailable with Internal Server Error; no result is claimed for it.
- `msearch.py ... grep "isGE_iff|isZero.*rightDerivedFunctorPlus" Algebra/Homology/DerivedCategory`
  found Mathlib's `DerivedCategory.isGE_iff`, which verifies the hypothesis match.
- Direct `rg` on Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
  `lean/Sheaf`, and the DAG found the existing generic theorem and its existing
  attachment to this very node. Its greater generality includes exactly the
  node's specialization; this is why a new scheme-specific sorry is unnecessary.

Mismatches and changes: H4 was repaired by dropping the duplicate module and
recording the existing upstream theorem; the node's mathematical statement and
all dependencies remain unchanged. The report corrects the Worker's mistaken
empty-integer-range remark and dependency module location (derived lowerStarPlus
is in UpperLowerStarCoherence, not the underived Defs module). No new node,
dependency repair, statement_change, or citer edit is needed. The intermediate
wrapper compiled cleanly through scompile.py before removal; the final delivery
wrapper checks the recorded existing declaration directly. No proof or hollow
definition is delivered.
