## Worker report

The module `Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound` states
`AlgebraicGeometry.Scheme.affine_direct_image_support_bound`, with exactly one
`sorry` and no new definitions. The node statement is unchanged. Source checked:
`literature/stacks-project/etale-cohomology.tex`, Tag 0F0X,
`lemma-interlude-I`, lines 19940–19949, and its proof.

Hypothesis and clause correspondence:

- Field K: `{K : Type u} [Field K]`.
- Schemes X,Y: `{X Y : Scheme.{u}}`. Their K-structures are the two
  `Over (Spec (.of K))` instances, with structure morphisms `X ↘ Spec (.of K)`
  and `Y ↘ Spec (.of K)`.
- Finite type over K: `LocallyOfFiniteType` and `QuasiCompact` for each structure
  morphism, precisely the conjunction in def-weil-finite-type-morphism.
- Affine K-morphism: `(f : X ⟶ Y) [f.IsOver (Spec (.of K))] [IsAffineHom f]`.
  The first instance asserts compatibility with those same K-structures.
- E_b(T): reuse `Scheme.Hom.pointsOfTrdegLE` for nonnegative indices.
  For a signed index b, the inline set
  `{y | 0 ≤ b ∧ y ∈ (Y ↘ Spec (.of K)).pointsOfTrdegLE b.toNat}`
  is exactly E_b(Y), including the prescribed empty set when b < 0.
  This is an inline expression using the dependency, not a new definition.
  Transcendence degrees use the structure morphism's residue-field algebra map,
  as in the dependency definition, rather than any independent field action.
- Integer a >= 0: `(a : ℤ) (ha : 0 ≤ a)`; `a.toNat` is therefore its exact
  nonnegative index, without any loss from truncation.
- Abelian etale sheaf F: `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Torsion: `(hF : IsTorsionAbelianSheaf F)`, the recorded colimit-of-kernels
  definition, not a replacement stalkwise or sectionwise predicate.
- Support assumption: `hsupport : etaleSheafSupport F ⊆
  (X ↘ Spec (.of K)).pointsOfTrdegLE a.toNat`.
- Every q >= 0: `(q : ℕ)` represents exactly the nonnegative integers, cast to
  ℤ for cohomology and the signed subtraction a-q.
- R^q f_* F: `DerivedCategory.Plus.singleFunctor ... 0` places F in degree zero;
  `Etale.rightDerivedLowerStarPlus AddCommGrpCat f` is the recorded derived
  direct image; `DerivedCategory.Plus.homologyFunctor ... (q : ℤ)` takes its
  degree-q cohomology sheaf. These signatures and docstrings were read.
- Conclusion: `etaleSheafSupport` of that sheaf is contained in the inline E_(a-q)
  set above. In particular no natural subtraction accidentally replaces a
  negative support bound by the bound zero.

Dependency declarations used (their source signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Sheaf.AlgebraicGeometry.EtaleSupport`: `Scheme.etaleSheafSupport` and
  `Scheme.Hom.pointsOfTrdegLE`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`, used through
  `pointsOfTrdegLE` and publicly available from EtaleSupport.
- `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`: `Scheme.IsTorsionAbelianSheaf`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`;
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `Etale.rightDerivedLowerStarPlus` (which is built from that lowerStar).
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.

All already-stated proof dependencies' modules are imported non-publicly;
Mathlib affine permanence is already public because its affine class is in the
statement. The two not-yet-stated proof dependencies
`lem-kun-strict-local-algebraic-residue-models` and
`lem-kun-affine-support-vanishing` have no module to import. Their steps and all
other node proof steps are retained in the theorem docstring for stage 3.

Edge cases checked mathematically: a=0, q=0, q=a and q>a, F=0, X empty, Y empty,
and arbitrary characteristic. For q>a the nonnegativity conjunct is false,
so the conclusion requires empty support, as in the node. No nonempty scheme,
separably closed base field, invertible torsion order, or uniform annihilator
is assumed. One arbitrary universe u holds K and the schemes; the standard
etale coefficients live in u+1 as in the dependency declarations.

Searches (2026-10-15):

- `msearch.py ... leanfinder`: “For an affine morphism of finite type schemes over
  a field, the support of higher direct image of a torsion etale sheaf has
  transcendence degree at most a minus q”. Eight results, concerning algebraic
  etale loci, ideal support, or module support dimension; none states this result.
- `msearch.py ... loogle '"support", "rightDerived"'`: zero hits.
- `msearch.py ... grep 'support.*rightDerived|rightDerived.*support'`: zero hits.
- `msearch.py ... leansearch`: “Support of higher direct images of torsion etale
  sheaves under affine morphisms is bounded by transcendence degree minus
  cohomological degree”. Unavailable: service Internal Server Error.
- `rg` over upstream WeilConjectures and project lean/Sheaf for
  `support.*rightDerived|rightDerived.*support|affine_direct_image_support`:
  only unrelated compact support comments and a complex-degree support lemma.
- `rg` over upstream WeilConjectures for this node id: zero hits.
- `rg` over dag/lean_names_upstream.json for `pointsOfTrdegLE` and the proposed
  theorem name: zero hits. Project searches for `pointsOfTrdegLE` locate the
  exact recorded EtaleSupport definition, which is reused.

Validation: scompile.py compiled the module cleanly on the server in 2.8 seconds,
nice 19, two threads, 60-second limit. No local compilation was run.
No statement dispute, correction, new nodes, or dependency repair was needed.

## Second reading by NY

Independent second reader, 2026-10-15. I read the node and its sandbox module,
Stacks `etale-cohomology.tex`, Tag 0F0X (`lemma-interlude-I`, statement and
proof), and the beginning of the surrounding cohomological-dimension section.
The source assumes a field and finite-type schemes, with an affine morphism;
it adds no separatedness, algebraic-closure, characteristic, constructibility,
or invertible-torsion-order condition here. The node makes the K-linearity
and negative-bound convention explicit. No correction is required.

Object/hypothesis/conclusion checklist, written against the node:

1. A field K: `{K : Type u} [Field K]`. Exact; not restricted to closed,
   separably closed, finite, or characteristic-zero fields.
2. Schemes X and Y over K: `{X Y : Scheme.{u}}` with
   `[X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]`. Exact. I opened
   Mathlib `AlgebraicGeometry/Over.lean`: these are structure morphisms, not
   additional geometric properties.
3. Both structure morphisms finite type: each has `LocallyOfFiniteType` and
   `QuasiCompact`. Exact, using def-weil-finite-type-morphism's two conditions.
   I read the actual Mathlib class signatures in `Morphisms/FiniteType.lean`
   and `Morphisms/QuasiCompact.lean`; neither imposes separatedness.
4. Affine K-morphism f: `(f : X ⟶ Y) [f.IsOver (Spec (.of K))]
   [IsAffineHom f]`. Exact. `Hom.IsOver` asserts commutation with those same
   structure maps. I read `IsAffineHom` in `Morphisms/Affine.lean`: preimages
   of affine opens are affine, exactly pqf-def-affine-morphism.
5. E_b(T), for signed integer b, consists of points with residue transcendence
   degree at most b and is empty for b<0. The nonnegative stratum is the
   dependency's `Scheme.Hom.pointsOfTrdegLE`. I opened its definition in
   `Sheaf.AlgebraicGeometry.EtaleSupport`: it uses `Algebra.trdeg` on
   `T.residueField t`, with the algebra induced by the structure morphism's
   `residueFieldAlgebraMap`. I also read `Algebra.trdeg` in Mathlib
   `RingTheory/AlgebraicIndependent/Basic.lean`. The conclusion's inline
   `{y | 0 ≤ a - (q : ℤ) ∧ y ∈ ...pointsOfTrdegLE (a - (q : ℤ)).toNat}`
   extends precisely that stratum to signed indices. Exact, with no private
   definition and no truncated natural subtraction.
6. Nonnegative integer a: `(a : ℤ) (ha : 0 ≤ a)`. Exact. The hypothesis uses
   `a.toNat`, which equals a because of ha.
7. Abelian etale sheaf F on X: `Sheaf X.smallEtaleTopology
   AddCommGrpCat.{u + 1}`. Exact; not a module sheaf or a constructible sheaf.
8. F torsion: `hF : IsTorsionAbelianSheaf F`. Exact. I opened
   `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`: this is `IsIso` of the
   canonical colimit-of-positive-integer-kernels map, the definition recorded
   by def-weil-pbc-torsion-etale-sheaf. It does not require a uniform
   annihilator or torsion of every section group.
9. Support contained in E_a(X): `hsupport : etaleSheafSupport F ⊆
   (X ↘ Spec (.of K)).pointsOfTrdegLE a.toNat`. Exact. I read
   `etaleSheafSupport`: points admitting an algebraically closed geometric
   point over them with nonzero sheaf fiber, as def-kun-support specifies.
10. Every q>=0: `(q : ℕ)`, after F and its hypotheses. Exact; it ranges over
    all nonnegative integer degrees, and is cast to ℤ for subtraction and
    derived cohomology.
11. R^q f_* F: `Plus.singleFunctor ... 0` embeds F in degree zero,
    `Etale.rightDerivedLowerStarPlus ... f` applies Rf_*, and
    `Plus.homologyFunctor ... (q : ℤ)` takes H^q. Exact. I opened the
    upstream `UpperLowerStar/Defs.lean` lowerStar (evaluation on the
    base-changed etale object), `Derived/UpperLowerStarCoherence.lean`
    rightDerivedLowerStarPlus (that functor's rightDerivedFunctorPlus),
    and Mathlib `DerivedCategory/Plus.lean` singleFunctor and homologyFunctor.
    These are the declarations recorded by def-weil-pbc-direct-image, not
    an underived pushforward or the wrong sign of cohomology.
12. The sole conclusion is support of that sheaf contained in E_(a-q)(Y),
    using the same support and Y's given K-structure. Exact, every clause
    present, no additional asserted vanishing or equivalence.

Edge cases: q=0 gives bound a; a=0 and q=0 give E_0; q=a gives E_0;
q>a makes the target set empty by its integer nonnegativity conjunct.
For F=0 or X empty the source support is empty and the statement still
applies. Empty Y is allowed (a map to it forces empty X); no nonempty
scheme instance appears. There is no index set in this statement. All
characteristics, including torsion divisible by the characteristic, remain
covered. All universes are bound: arbitrary u for field and schemes, and
u+1 for the recorded abelian-etale-sheaf category. This is the same universe
encoding as the dependencies; larger sets can be placed in a common larger
universe. There is no small test-object quantifier that could become vacuous.

Independent H4 searches, using different wording from the first worker:

- `msearch.py ... leanfinder`: “Vanishing stalks of higher direct images for
  affine maps with torsion coefficients and residue field dimension bounds”.
  Eight hits, about affine limits, structure-sheaf germs and localization;
  none is this theorem.
- `msearch.py ... loogle '"trdeg", "Sheaf"'`: zero hits.
- `msearch.py ... leansearch`: “affine pushforward torsion abelian etale
  sheaf support dimension decreases by cohomological degree”. Service
  unavailable (Internal Server Error); no mathematical verdict inferred.
- `rg` over upstream WeilConjectures, Mathlib, project lean/Sheaf and
  dag/lean_names_upstream.json for support near `pushforward`, `directImage`,
  or `lowerStar`, the proposed declaration name, and the node id. Hits are
  coherent-module/ideal support, compact supports, perverse operations, or
  unrelated function pushforwards. None states this torsion abelian support
  estimate. The recorded support and torsion definitions are reused.

No new definition node or dependency module is delivered, so H12/H13 need
no new-node review. The sandbox contains just the item's node and module.
There is no statement_change, and the natural-language node is unchanged;
no corrected-statement citer audit is applicable. The five docstring proof
steps match the node's five steps, including compatible strict-local models,
algebraic residue extensions, the b>a case, affine support vanishing, and
continuity. Already-stated proof dependencies are imported; the two unstated
ones remain named in that proof plan. The module defines no object, proves
nothing, and has one named theorem with `sorry`. Source/blueprint docstrings,
namespace, imports, and 100-column width conform. The node's lean.statement
is byte-for-byte the theorem signature before `:= by`; universe u and every
variable are explicitly bound.

Mismatches found: none. Changes: appended this independent reading only;
Lean and the node record are unchanged.

Second-reader validation: scompile.py compiled the delivered module cleanly
on the server in 2.8 seconds, nice 19, two threads, 60 seconds per file; no
errors or warnings. No local compiler or global build was run.
