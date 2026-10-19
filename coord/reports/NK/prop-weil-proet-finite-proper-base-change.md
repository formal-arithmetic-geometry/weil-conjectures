## Worker report

The module `Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange` states
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_torsionSheaf_of_isProper`.
Its only proof is `sorry`. No definitions, dependency repairs, or new nodes are needed.
The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- The four schemes are `{X' X Y' Y : Scheme.{u}}`, with all four arrows explicitly bound.
- The Cartesian square with chosen identification is
  `sq : ChosenCartesianSquare g' f' f g`. Its `isoPullback`, `hom_fst`, and `hom_snd`
  are the chosen fibre-product identification and projection compatibilities;
  its inherited `toCommSq` is the equality used by the exchange construction.
- Properness of the vertical morphism `f` is `[IsProper f]`. There is no condition on `g`.
- An arbitrary abelian étale sheaf is
  `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Torsion is exactly `hF : F.IsTorsion`: sections are locally killed by positive integers.
  It requires neither finite stalks nor one uniform annihilator.
- `F[0]` is `(DerivedCategory.Plus.singleFunctor
  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F`.
- The actual canonical exchange arrow is the component at that object of
  `derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq`.
  Its source is derived direct image along `f` followed by inverse image along `g`;
  its target is inverse image along `g'` followed by derived direct image along `f'`.
- `IsIso` of that component states exactly that this arrow is an isomorphism in
  `DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})`.

Dependency declarations inspected and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`, including its full fields and docstring.
- `WeilConjectures.SixFunctors.BaseChange.Derived`,
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`: the recorded canonical exchange
  transformation, constructed from the termwise exchange using right derivation.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded category conventions use
  Mathlib's `DerivedCategory.Plus`; `DerivedCategory.Plus.singleFunctor` was read in
  `Mathlib.Algebra.Homology.DerivedCategory.Plus` and inserts a sheaf in degree zero.
  The module's module-valued torsion predicate is not needed for this abelian statement.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, read using `scompile.py --source`
  because it is missing in the older local checkout: the abelian sheaf and derived
  category encodings agree with this module. Torsion uses its recorded
  `CategoryTheory.Sheaf.IsTorsion` from
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`; its full local
  section definition and documentation were inspected.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`:
  separated, universally closed, locally of finite type (universally closed implies
  quasi-compact, giving finite type). Scheme conventions introduce no declaration.
- Proof-only import `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`:
  the current server source, read using `scompile.py --source`, gives
  `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` on abelian sheaves with
  torsion cohomology. Its `Etale.baseChange` agrees with `derivedBaseChangeMapPlus`.
  The older local checkout instead has the module-valued version, so the live
  source was used to check the proof plan.

The complete three-step natural-language proof is in the theorem docstring:
compute the cohomology of `F[0]`, apply the bounded-below proper base change
statement, and identify its canonical exchange component with the one asserted.
Source checked: the blueprint node's Detailed form and its proof; Stacks
`etale-cohomology.tex`, `lemma-proper-base-change` (Tag 0DDE).
The earlier blueprint sketch includes additional coherence clauses; as already
noted in the node's stage-1 review, those are absent from the authoritative
Detailed form. No clauses were silently added.

Edge cases checked: zero sheaf; empty schemes; identity squares; arbitrary base
change `g`; nonconstructible torsion sheaves and torsion with no common exponent.
All are admitted by the binders. The single complex includes degree zero and all
other degrees, without an extra boundedness assumption. Universe `u` is arbitrary;
abelian groups use the site's established coefficient universe `u + 1`.
No statement fault or disputed statement was found.

Searches (2026-10-15):

- `msearch.py ... leanfinder "Proper base change for a torsion abelian sheaf on the
  small etale site in degree zero"`: eight unrelated condensed-sheaf hits; no match.
- `msearch.py ... loogle '"baseChange", "IsProper"'`: one hit,
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, a geometric stability result.
- `msearch.py ... grep 'isIso_baseChange_of_isProper|singleFunctor|derivedBaseChangeMapPlus'
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "proper base change for torsion sheaves on the small
  etale site"`: unavailable, Internal Server Error.
- `rg` of the upstream project and `lean/Sheaf` for the node id and proposed name:
  no existing statement. Searches for `isIso_baseChange_of_isProper` and
  `isIso.*[Tt]orsion.*[Ss]heaf` found general complex-valued proper base change and
  smooth base change, not this exact degree-zero specialization. The general
  theorem is recorded as a proof dependency, not restated here in its full strength.
- Read the existing `singleFunctor` API instead of constructing a duplicate
  degree-zero embedding.

Validation: the delivered file compiled cleanly with the prescribed server
`scompile.py NK prop-weil-proet-finite-proper-base-change <file>` (3.5 seconds).

## Second reading by NK

Independent second reading, 2026-10-15. I opened the DAG node, the sandbox module,
the blueprint source (especially its Detailed form), and Stacks
`etale-cohomology.tex`, `lemma-proper-base-change` (Tag 0DDE). The Stacks lemma
introduces arbitrary schemes, a proper morphism, arbitrary base change, and a
bounded-below complex with torsion cohomology. It assumes no Noetherian,
constructibility, prime-to-characteristic, or uniform-annihilator hypothesis.
Specialization to the single complex of a torsion sheaf gives exactly this node.
The earlier sketch has additional coherence clauses, but the Detailed form and
reviewed node do not; this delivery follows the latter without changing either.

Object, hypothesis, and conclusion checklist:

1. Four schemes and four arrows forming the displayed square: `{X' X Y' Y :
   Scheme.{u}}`, `{g' : X' ⟶ X}`, `{f' : X' ⟶ Y'}`, `{f : X ⟶ Y}`,
   `{g : Y' ⟶ Y}`. Verdict: exact objects and arrow orientation.
2. Cartesian square with chosen identification: `sq : ChosenCartesianSquare g' f' f g`.
   I read its module and the dependency node: `isoPullback : X' ≅ pullback f g`,
   `hom_fst`, and `hom_snd` identify the two arrows with the projections;
   `toCommSq` supplies the equality for the exchange. Verdict: exact, with no
   separately assumed or arbitrary comparison map.
3. Properness of the right vertical arrow: `[IsProper f]`. I read Mathlib's
   `Morphisms/Proper.lean` and the dependency record: separated, universally
   closed, locally finite type, with quasi-compactness supplied by universal
   closedness. Verdict: the node's properness, with no hypothesis on `g`.
4. Every abelian etale sheaf on X: `F : Sheaf X.smallEtaleTopology
   AddCommGrpCat.{u + 1}`. I read the current server `EtaleSheaves` source and
   its DAG record. Verdict: the recorded abelian encoding, not the module or
   condensed pro-etale coefficient category suggested by the historical item name.
5. Torsion: `(hF : F.IsTorsion)`. I read the full definition in
   `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, including
   the current server source. Each section is locally of finite additive order
   on a covering sieve. Verdict: exactly torsion sheaves, without a uniform
   exponent or finiteness of stalks.
6. Sheaf regarded as a derived object: `(DerivedCategory.Plus.singleFunctor
   (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F`.
   I read Mathlib's `DerivedCategory/Plus.lean`: `singleFunctor C n` puts the
   object in degree n and lies in D-plus. I also read the recorded
   `DerivedCategories` module. Verdict: exactly F[0], with its other degrees zero.
7. Specified canonical exchange, not just isomorphic endpoints:
   `(derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app` at F[0].
   I read the recorded `BaseChange.Derived` definition, its coefficient-category
   assumptions and endpoint functors: `lowerStar f` right-derived then derived
   `upperStar g`, to derived `upperStar g'` then right-derived `lowerStar f'`.
   Verdict: precisely the dependency's canonical exchange, in the stated direction.
8. Isomorphism in D-plus of abelian sheaves on Y': `IsIso` of that component.
   Verdict: all and only the conclusion of the Detailed form, for each F after
   fixing the square. The target category is inferred from the recorded functors.

I read the current server `BaseChangeTheorems.Proper` proof-dependency declaration:
`Etale.isIso_baseChange_of_isProper` takes `IsPullback`, a D-plus abelian object,
and torsion homology. Its conclusion uses `Etale.baseChange`, identified with
`derivedBaseChangeMapPlus`. This supports the three-step docstring: compute
cohomology of F[0], apply the bounded-below theorem, identify the actual component.
There are no new definition nodes or dependency modules to review. The existing
scheme-conventions node is only conventions, and introduces no additional binder.

Edge cases: the zero sheaf and empty schemes remain admitted; arbitrary identity
and nonidentity base changes remain admitted. No index type or positive-degree
binder restricts an empty index set or degree zero. Torsion may have varying
orders, including residue-characteristic torsion, with no invertibility condition.
All universes are bound by `universe u`; the coefficient size u+1 is the existing
small-etale derived-functor convention, and u is arbitrary. No extra smallness,
field, Noetherian, or finiteness instance is requested from the caller.

Independent searches, 2026-10-15:

- `msearch.py ... leanfinder "Derived direct image of a torsion etale abelian
  sheaf commutes with arbitrary pullback along a proper morphism"`: eight
  sheaf-of-modules pullback/pushforward comparison results, no matching theorem.
- `msearch.py ... loogle '"IsIso", "baseChange"'`: six Guitart-exact Kan-extension
  results, no torsion etale proper base change statement.
- `rg` in Mathlib's algebraic-geometry and category-theory Sites directories for
  `baseChange`, proper/torsion combinations: no matching cohomological theorem.
  `rg` in upstream `WeilConjectures/SixFunctors`, upstream Sites helpers, and
  project `lean/Sheaf` for torsion/single and proper-base-change names found the
  general complex theorem and torsion-single helper, but no exact sheaf-level
  specialization. I opened the general theorem on the server, rather than
  treating a similar name from the older checkout as a match.

Mismatch and repair verdict: none. The Lean module and node's Lean record were
already correct and were left unchanged; this reading adds only the report.
There are no hollow definitions or hidden choices, no local notation or private
copies, and the only proof is `sorry`. The module and theorem docstrings give the
source and blueprint id and all three DAG proof steps. I mechanically compared
`lean.statement` with the theorem signature: verbatim equal. The file compiled
cleanly using the prescribed `scompile.py NK
prop-weil-proet-finite-proper-base-change` wrapper (3.7 seconds for the module),
with no errors or warnings. The first invocation used the repository working
directory and could not find the sandbox file; rerunning from the sandbox
resolved that path error and produced this clean result.
