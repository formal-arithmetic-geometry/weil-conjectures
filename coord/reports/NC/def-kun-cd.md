## Worker report

The module Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension defines
AlgebraicGeometry.Scheme.torsionEtaleCohomologicalDimension and
AlgebraicGeometry.Scheme.Hom.torsionEtaleCohomologicalDimension. Both are real
constructions by sInf of the set of finite valid bounds in ℕ∞; there are no
proof declarations, sorry data, or auxiliary notions.

Clause and hypothesis matching:

- Scheme T is `T : Scheme.{u}`; quasi-compactness is `[CompactSpace T]` and
  quasi-separatedness is `[QuasiSeparatedSpace T]`.
- Scheme cohomology vanishes for every torsion abelian étale sheaf above n:
  `T.HasTorsionEtaleCohomologicalDimensionLE n`, reused from the landed node
  def-sc-etale-torsion-cd. Its full definition quantifies over
  `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`, uses `F.IsTorsion`, and
  expresses vanishing as `Subsingleton` of `Etale.cohomology ... q` evaluated
  at `(DerivedCategory.singleFunctor _ 0).obj F`. Its degrees q are natural;
  these cover exactly the integer degrees q > n because n is nonnegative.
- Morphism f is `{X Y : Scheme.{u}} (f : X ⟶ Y)`; its quasi-compact and
  quasi-separated hypotheses are `[QuasiCompact f] [QuasiSeparated f]`.
  Neither X nor Y is separately required to be quasi-compact or quasi-separated.
- Every torsion abelian sheaf on X is quantified as
  `∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), F.IsTorsion →`.
  This is local torsion, with no uniform annihilator or invertibility condition.
- Every integer q > n is `∀ (q : ℤ), (n : ℤ) < q →`.
  The zero higher direct image is `IsZero` of `Plus.homologyFunctor ... q`
  applied to `Etale.rightDerivedLowerStarPlus ... f` applied to
  `Plus.singleFunctor ... 0` of F. This is exactly H^q(Rf_*F).
- Both values belong to ℕ∞ (nonnegative integers with infinity). In both
  definitions the set under sInf contains precisely `(n : ℕ∞)` for natural
  valid bounds n. A nonempty set of naturals has a least member, so its
  infimum in ℕ∞ is that least bound. If there is no valid bound the set is
  empty and sInf is top, i.e. infinity. Infinity is never a finite candidate.

Dependency declarations read and used:

- def-weil-pbc-scheme-conventions is explicitly a convention record, with no
  declaration of its own; Scheme, CompactSpace, QuasiSeparatedSpace,
  QuasiCompact and QuasiSeparated are the Mathlib notions it names.
  The morphism properties are imported through
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated.
- def-weil-pbc-etale-sheaves records the upstream module
  WeilConjectures.AlgebraicGeometry.EtaleSheaves. Its torsion clause records
  CategoryTheory.Sheaf.IsTorsion from
  WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic,
  whose covering-sieve definition and docstring were read. It is inherited
  through Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension.
- def-weil-pbc-etale-cohomology: AlgebraicGeometry.Etale.cohomology and
  rightDerivedGlobalSections in
  WeilConjectures.SixFunctors.Etale.Derived.LowerShriek. Read the full
  coefficient-category assumptions and docstrings; used through the existing
  scheme bound predicate, with A = AddCommGrpCat.{u+1}.
- def-weil-pbc-direct-image: AlgebraicGeometry.Etale.lowerStar in
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs, and
  AlgebraicGeometry.Etale.rightDerivedLowerStarPlus in
  WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence.
  The latter module is imported directly. Read both signatures, binders,
  docstrings and bodies: lowerStar is the base-change sheaf pushforward;
  rightDerivedLowerStarPlus is its bounded below right derived functor.
- Added the already landed definition node def-sc-etale-torsion-cd to stmt_deps
  as allowed by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES), to reuse
  AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE in
  Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension. Its node statement,
  lean record, full definition and docstring were read. No new node is needed.
- Mathlib.Data.ENat.Lattice supplies the complete linear order on ℕ∞;
  Mathlib.Algebra.Homology.DerivedCategory.Plus supplies singleFunctor and
  homologyFunctor, whose definitions and docstrings were read.

Edge cases checked: n = 0 imposes only positive-degree vanishing, with no
condition on degree zero. Negative integer degrees never satisfy q > n.
For the empty scheme all groups are zero, so every natural bound is valid and
the dimension is zero. The zero sheaf imposes no restriction. Unbounded
cohomology gives an empty set of finite bounds and hence infinity. No field,
characteristic, finite coefficient exponent, nonempty scheme, finite type,
or separatedness hypothesis is introduced. Universe u is explicit, and
abelian groups live in u+1 as required by the recorded étale functors.

Searches (2026-10-15):

- msearch.py leanfinder, query “Torsion etale cohomological dimension least
  natural bound on cohomology and higher direct images”: eight results,
  concerning etale loci, formal etaleness and injective/projective dimension;
  none defines the requested numerical invariant.
- msearch.py loogle, query `cohomologicalDimension, CohomologicalDimension`:
  zero hits, unknown identifier cohomologicalDimension.
- msearch.py grep, query
  `cohomologicalDimension|CohomologicalDimension|cohomological dimension`:
  zero Mathlib hits.
- msearch.py leansearch, query “torsion etale cohomological dimension least
  bound with infinity”: unavailable, Internal Server Error.
- rg of the source WeilConjectures tree and project lean/Sheaf, for
  `cohomologicalDimension|CohomologicalDimension|def-kun-cd`: found the existing
  scheme bound predicate and its citers, curve vanishing modules, and the
  different ProEtale.HasUniformCohomologicalDimensionLE predicate; no numerical
  torsion étale dimension. Also checked AlgebraicGeometry subtrees and the
  upstream name index. No upstream reference to def-kun-cd was found.
- The new full declaration names have no existing source/project match.

The blueprint source def-kun-cd.md was read directly. The stalk criterion is
only a pointer to a separate theorem and is not additional defining data.
There is no statement correction, disputed statement, unusable dependency,
or new definition node.

Validation: scompile.py compiled the delivered module cleanly on the server
(nice 19, two threads, 60 seconds per file); the existing scheme-bound module
was compiled in the private overlay as well. No local compilation was run.

## Second reading by NC

Independently read the node and both definitions, the original blueprint
`sec-smooth-purity/sk-prop-sf-cbc/def-kun-cd.md`, and Stacks
`etale-cohomology.tex`, definitions `definition-cd` (0F0Q, lines 19612–19624)
and `definition-cd-f` (0F0Z, lines 20026–20038), including their section
introductions. They introduce precisely the following objects, hypotheses,
and defining clauses. No ambient Noetherian, field, characteristic, or
coefficient-exponent hypothesis is assumed there.

1. A scheme T: `T : Scheme.{u}`. Verdict: same object.
2. T is quasi-compact and quasi-separated: `[CompactSpace T]` and
   `[QuasiSeparatedSpace T]`. Verdict: exact, including the empty scheme.
3. Every torsion abelian sheaf on its small étale site: the body of the reused
   `Scheme.HasTorsionEtaleCohomologicalDimensionLE` quantifies over
   `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}` with `F.IsTorsion`.
   Verdict: exact. I opened that dependency's node and complete source in
   `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`. I also read
   `CategoryTheory.Sheaf.IsTorsion` in the upstream sheaf-cohomology Basic
   module: its covering sieve and finite additive order mean locally killed
   by positive integers, without a common annihilator.
4. For every integer q > d, ordinary H^q(T,F) vanishes: the reused predicate
   has `∀ q : ℕ, n < q → Subsingleton ((Etale.cohomology ... q).obj
   ((DerivedCategory.singleFunctor _ 0).obj F))`. Verdict: exact. For natural
   n, every integer q > n is positive and uniquely a natural number.
   I read the recorded `Etale.cohomology` and `rightDerivedGlobalSections`
   definitions and their full variable context in upstream LowerShriek:
   they compute H^q of derived global sections, and introduce no hypothesis
   on T. Subsingleton of an abelian group means the zero group.
5. The least nonnegative bound, infinity if none: `sInf {d | ∃ n : ℕ,
   d = (n : ℕ∞) ∧ T.HasTorsionEtaleCohomologicalDimensionLE n}`.
   Verdict: exact. Every finite candidate is an actual bound; a nonempty
   subset of natural numbers has a minimum, its infimum in ℕ∞. The empty
   candidate set has infimum top. The definition contains no postponed data.
6. A morphism of schemes f:X→Y: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
   Verdict: exact. Same scheme universe is the recorded morphism category;
   enlarging u accommodates objects initially presented at different sizes.
7. f is quasi-compact and quasi-separated: `[QuasiCompact f]`
   `[QuasiSeparated f]`. Verdict: exact. I read Mathlib's class definitions:
   quasi-compact preimages and quasi-compact diagonal, respectively. There
   are no extra compactness or quasi-separatedness instances on X or Y.
8. Every torsion abelian sheaf F on X and every integer q > n:
   `∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
   F.IsTorsion → ∀ (q : ℤ), (n : ℤ) < q → ...`. Verdict: exact quantifiers.
9. R^q f_* F is zero: `IsZero` of `DerivedCategory.Plus.homologyFunctor`
   at q on `Etale.rightDerivedLowerStarPlus ... f` of
   `DerivedCategory.Plus.singleFunctor ... 0` of F. Verdict: exact. I opened
   the direct-image dependency node, upstream `Etale.lowerStar` (objectwise
   base change), `rightDerivedLowerStarPlus` (its rightDerivedFunctorPlus),
   and Mathlib's Plus single and homology functors. This is the recorded
   bounded below derived image, followed by its cohomology sheaf.
10. Least nonnegative morphism bound, infinity if none: the second `sInf`
    has the same finite-candidate construction as item 5 with the vanishing
    condition of items 8–9. Verdict: exact for both finite and infinite values.

Dependency audit: also read the statements and lean records of
`def-weil-pbc-scheme-conventions`, `def-weil-pbc-etale-sheaves`,
`def-weil-pbc-etale-cohomology`, and `def-weil-pbc-direct-image`.
The first is a conventions record with no declaration to import. The other
three use exactly the canonical objects above; no private replacements.
The added dependency `def-sc-etale-torsion-cd` is already landed and is reused,
not redefined. There are no new nodes or dependency modules in this delivery,
and no statement_change to review. The source's stalk-criterion pointer
belongs to the separate theorem and adds no defining clause.

Edge cases: at n=0 only positive degrees must vanish; negative degrees are
never queried above a nonnegative bound. The zero sheaf contributes no
restriction. The empty scheme, and a morphism from it, have bound zero.
The identity morphism likewise has bound zero although H^0 need not vanish.
No empty index set is introduced. If finite valid bounds are absent, the
empty set under sInf gives infinity. All characteristics are included, with
no invertibility restriction. The explicit universe u and the canonical
u+1 coefficient category match the dependency functors; no test objects
are quantified in an independent smaller universe. No variables are unbound.

Independent searches on 2026-10-15, using different wording from the author:

- msearch leanfinder: “Numerical dimension of the small etale topos defined
  by vanishing of derived pushforward on all torsion abelian sheaves”:
  eight results, including smallEtaleTopology/smallEtalePretopology and
  algebraic étaleness; no numerical cohomological dimension.
- msearch loogle: `"dimension", "torsion"`: one result,
  `Module.AEval.isTorsion_of_finiteDimensional`, about polynomial modules;
  not the requested invariant.
- msearch leansearch: “Infimum of finite vanishing bounds for higher direct
  images of torsion etale abelian sheaves”: unavailable, Internal Server Error.
- rg over all Mathlib, upstream WeilConjectures, and project lean/Sheaf:
  `cohomological.?dimension|torsion.*dimension|dimension.*torsion`.
  Found the reused bound predicate, dimension estimates and curve theorems,
  and the different pro-étale `HasUniformCohomologicalDimensionLE`.
  I opened the latter: it quantifies over pro-étale base changes and every
  coefficient sheaf, so does not define this invariant. The upstream
  finite-type dimension module contains a theorem with field and finite-type
  assumptions, not this definition. Neither is an exact existing match.
- Checked the upstream declaration index and source/project for the new
  full names: no prior declaration of either numerical invariant.

No mathematical or signature mismatch was found. No Lean or node change was
needed; only this independent second-reading report was added. Both source
citations and blueprint docstrings are present; all constructions are real
sInf constructions, with no theorem proofs or sorry data.
