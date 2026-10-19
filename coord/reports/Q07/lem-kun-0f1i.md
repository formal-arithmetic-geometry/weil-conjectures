## Worker report

`Sheaf.Targets.BaseChangeTowardsFields` states
`AlgebraicGeometry.Etale.baseChange_towardsSpecField`. Its only theorem proof
is `sorry`; it defines no new objects.

Each hypothesis of `lem-kun-0f1i` is rendered as follows:

- The field is `{K : Type u} [Field K]`.
- The schemes are `{X S' T : Scheme.{u}}`. The structure morphism of X is
  `f : X ⟶ Spec (.of K)`, with `[LocallyOfFiniteType f] [QuasiCompact f]`,
  exactly finite type in the recorded scheme conventions.
- The K-scheme structures are `[S'.Over (Spec (.of K))]` and
  `[T.Over (Spec (.of K))]`.
- The morphism is `g : T ⟶ S'`, with `[g.IsOver (Spec (.of K))]`,
  `[QuasiCompact g]`, and `[QuasiSeparated g]`.
- The coefficient sheaf is
  `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The stalk hypothesis is
  `hF : IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F`.
  This is the published declaration of `def-kun-torsion-invertible`.
  Its quantifiers run over geometric stalk elements, with a separate positive
  annihilator n for each element and `(n : K) ≠ 0`. Over a field the latter
  condition is equivalent to invertibility. It requires no common annihilator.
  The dependency uses separably closed geometric points, the standard equivalent
  family of points of the small etale topos; passing to an algebraic closure
  preserves their stalks. Thus it expresses the node's geometric-stalk condition.
  Torsion is included stalkwise; the enough-points characterization gives local
  torsion of sections, without imposing sectionwise global annihilation.

The clauses concerning the diagrams and conclusion are rendered as follows.
`X'` is `pullback f (S' ↘ Spec (.of K))`, and f' is its second projection.
`Y` is the pullback of that second projection and g; h and e are respectively
its first and second projections. `CommSq.mk (pullback.condition ...).symm`
supplies the commutativity `e ≫ g = h ≫ f'`. These chosen pullbacks give both
cartesian squares required by the node. `exactDerivedBaseChangeMap` applied to
this square is the canonical exchange from f' inverse image after Rg_* to
Rh_* after e inverse image. It is evaluated on
`(DerivedCategory.singleFunctor
  (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F`,
which places F in degree zero. `IsIso` of that component is precisely the
asserted isomorphism in the unbounded derived category with abelian coefficients.

Dependency declarations read and used:

- `def-kun-unbounded-exchange`: module
  `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`, declaration
  `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`. Its definition is the
  adjunction mate of the termwise-derived square comparison; no arbitrary
  exchange map or additional isomorphism assumption is introduced.
- `def-kun-torsion-invertible`: module
  `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`, declaration
  `AlgebraicGeometry.Etale.IsTorsionOfInvertibleOrder`, using
  `invertibleTorsionOrders`. The published source was also checked with
  `scompile.py --source Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`.
- `def-weil-pbc-etale-sheaves`: the recorded module
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves` and its imports provide
  `CategoryTheory.Sheaf`, the small-etale abelian coefficient category,
  and `CategoryTheory.Sheaf.IsTorsion`. The current module was read with
  `scompile.py --source`; it is imported through the torsion-order dependency.
- `def-weil-pbc-scheme-conventions` is a convention record rather than one
  declaration. Its finite-type notion uses Mathlib `LocallyOfFiniteType` and
  `QuasiCompact`; its other conditions use `QuasiSeparated`, `Scheme`, and
  `Limits.pullback`. The finite-type declaration is imported explicitly.

Edge cases checked: positive n excludes zero; in characteristic zero every
positive n has nonzero scalar, while in characteristic p positive multiples
of p are excluded. The zero sheaf and zero stalk satisfy the condition with
n = 1. Empty schemes and empty families of geometric points require no
nonemptiness assumption. There is no finite-type restriction on S' or T,
no uniform annihilator, and no boundedness assumption beyond placing the
input sheaf in degree zero. The site, stalks, coefficient category, and
schemes follow the published shared-universe convention.

Existing searches (recorded in `searches.jsonl`) were checked:

- `msearch.py` LeanFinder query: "etale cohomology base change finite type
  scheme over field torsion sheaf". Eight hits concern Kahler differentials
  or algebra/ring etale base change; none states this theorem.
- `msearch.py` Loogle query: "exactDerivedBaseChangeMap, base change etale".
  No hits; this project declaration is absent from the search service index.
- `msearch.py` Mathlib grep query: "baseChange|etale.*cohomology", under
  AlgebraicGeometry. No hits from that query.
- Fresh `rg` in the upstream project and `lean/Sheaf` for
  `baseChange_towardsSpecField` and `IsTorsionOfInvertibleOrder` found the
  published torsion-order definition and no existing copy of the theorem.
  Searches for `IsTorsionSheafOfInvertibleOrder` also found an upstream
  ModuleCat-valued predicate, which is not this abelian-sheaf interface.

No statement correction or disputed mathematical statement is needed.
No new node or dependency module is included: all statement dependencies
now have usable published declarations.

## Repair of return L

The returned immutable head b43feb0aa885 failed file-only compilation with
unknown identifier `IsTorsionSheafOfInvertibleOrder`. Replaced that reference
with the current recorded dependency
`AlgebraicGeometry.Etale.IsTorsionOfInvertibleOrder` and replaced its import
by `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders`. The K-scheme argument
is `Over.mk (T ↘ Spec (.of K))`.

Removed the superseded sandbox dependency module
`Sheaf.Targets.TorsionInvertible` and its dependency node copy. Keeping it
would duplicate the published notion and its cohomology declaration. The
item's mathematical statement and dependency edges are unchanged; its Lean
signature record is copied verbatim from the repaired file.

The previous independent reading concerned the superseded two-module packet.
It is not asserted as a reading of this repair; the next second reader should
check the published predicate and the repaired one-module delivery.

## Second reading by Q07

I independently read the repaired one-module delivery, the node and all four
statement dependencies. I read Stacks Tag 0F1I, including its actual TeX
`etale-cohomology.tex`, label `lemma-punctual-base-change`, and the opening of
the containing Kunneth section. The local literature checkout is absent, so
the TeX was read from the Stacks project's official GitHub repository:
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex
and checked against https://stacks.math.columbia.edu/tag/0F1I.
There is no section-wide standing extra hypothesis. Stacks proves the more
general arbitrary-X assertion and then reduces to finite type in its proof;
this node explicitly and correctly states the finite-type-over-K case.
No node statement correction is needed.

Object, hypothesis and conclusion checklist (each verdict is pass):

1. A field K: `{K : Type u} [Field K]`. This is a field, with no
   algebraic-closure, perfection or characteristic assumption.
2. The finite-type K-scheme X and its named structure map f:
   `{X : Scheme.{u}} (f : X ⟶ Spec (.of K))`
   with `[LocallyOfFiniteType f] [QuasiCompact f]`. I opened the Mathlib
   finite-type, quasi-compact and quasi-separated definitions, and the
   convention dependency. Locally finite type plus quasi-compact is exactly
   the node's finite type, including nonseparated schemes.
3. K-schemes S' and T: `{S' T : Scheme.{u}}`,
   `[S'.Over (Spec (.of K))] [T.Over (Spec (.of K))]`.
   These specify their structure maps without imposing finiteness conditions.
4. The K-morphism g: `(g : T ⟶ S') [g.IsOver (Spec (.of K))]`.
   This says precisely that the structure maps commute with g.
5. The two required properties of g: `[QuasiCompact g] [QuasiSeparated g]`.
   There is no properness, separatedness, smoothness or finite-type hypothesis.
6. X' and f': `pullback f (S' ↘ Spec (.of K))` and
   `pullback.snd f (S' ↘ Spec (.of K))`. This chosen pullback realizes the
   first cartesian square; no arbitrary product or extra chosen map appears.
7. Y and its projections h and e: the pullback of that f' and g, with
   h its first projection to X' and e its second projection to T.
   The second square is therefore cartesian. The `CommSq` uses the symmetric
   pullback condition, namely `e ≫ g = h ≫ f'`.
8. An arbitrary abelian etale sheaf F on T:
   `(F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`.
   I opened the recorded EtaleSheaves module using `scompile.py --source`,
   and checked its imports and category conventions. This is Ab(T_et),
   with no module structure or constructibility restriction added.
9. Torsion stalks with invertible orders:
   `(hF : IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F)`.
   I opened `Sheaf.AlgebraicGeometry.InvertibleTorsionOrders` and read
   `invertibleTorsionOrders` and `IsTorsionOfInvertibleOrder` in full.
   It quantifies over every separably closed geometric point and every
   stalk element, then requires a positive n with `(n : K) ≠ 0` and
   `n • x = 0`. Nonzero is precisely invertible in a field. These are the
   geometric stalks constructed by Mathlib `Scheme.pointSmallEtale` and
   `sheafFiber`; I opened the former's construction and enough-points
   declarations. Separably closed points give the same stalk family as
   algebraically closed points, since adjoining the purely inseparable
   remainder of an algebraic closure changes no etale neighbourhoods.
   Stalkwise torsion also implies the local-section torsion condition.
   There is no fixed exponent and no extra global sectionwise condition.
10. F lies in degree zero:
    `(DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F`.
    The conclusion concerns the unbounded derived category on this object.
11. The canonical arrow `(f')⁻¹ Rg_* F → Rh_* e⁻¹ F`:
    `exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}` on the above `CommSq`,
    evaluated at F[0]. I opened both declarations in ExactUnboundedExchange,
    the upstream `squareUpperStarIso`, and
    `mapDerivedUpperStarLowerStarAdjunction`. The square is descended termwise
    and its mate uses the canonical derived adjunction. In the generic
    declaration's names the substitutions are `f = g`, `f' = h`,
    `g =` the node's f', and `g' = e`; thus both endpoints and direction
    are exactly the required ones. AddCommGrpCat is the integral/abelian
    coefficient specialization and requires no arbitrary exchange choice.
12. The entire conclusion is `IsIso` of this component. No cohomological
    degree is omitted, and no extra conclusion or hypothesis is present.

Edge cases: no Nonempty hypothesis excludes empty schemes. On the empty T
the stalk condition is vacuous as it should be. The zero sheaf and zero
stalk elements admit annihilator 1. Order 0 is excluded by `0 < n`;
in characteristic zero all positive n are allowed, while in characteristic
p exactly the positive n prime to p are allowed. The conclusion is a
derived isomorphism, including degree zero and all negative degrees;
there is no degree cutoff or index-set restriction. The declaration binds
its sole universe `u`, all schemes, the field and every morphism explicitly.
Coefficients use `AddCommGrpCat.{u+1}`, as in the published sheaf and
exchange interfaces, rather than an additional equality of site universes.
Increasing the ambient universe accommodates any set-sized field and
scheme data; the predicate's Type-u geometric points include algebraic
closures of the Type-u residue fields. No independent smaller test universe
makes its quantification vacuous.

Fresh searches, using wording other than the first worker's:

- LeanFinder via `msearch.py`: "punctual base change abelian sheaves
  geometric stalk prime to characteristic". Eight hits concerned structure
  sheaf stalk localization, sheaf-module pullback, or abelian module
  categories; none states this theorem.
- Loogle via `msearch.py`: `"baseChange"`. Twelve hits concerned linear
  maps, submodules and related algebra constructions; none is this theorem.
- Mathlib grep via `msearch.py`: `punctual|baseChange_towardsSpecField`
  under AlgebraicGeometry; zero hits.
- LeanSearch via `msearch.py`: "The base change morphism for torsion etale
  sheaves and finite type schemes over a field is an isomorphism".
  The service returned Internal Server Error, recorded as unavailable.
- Direct `rg` across Mathlib, the upstream WeilConjectures source and the
  project's `lean/Sheaf` for `punctual.?base.?change`,
  `baseChange_towardsSpecField`, `base.?change.?towards`, and `0f1i`
  found no existing theorem. A broader search for field/base-change
  declarations found smooth-base-change failure detection and projective-line
  stalk comparison results, not the assertion here. The published
  torsion-order and exact-exchange definitions are used, not duplicated.

Mismatches repaired:

- H8: the original short proof docstring did not carry the node's eight
  steps in enough detail for stage 3. Expanded it to all eight, including
  filtered annihilators, the two direct-image comparisons and mate pasting,
  lifting geometric points for conservativity, reduction, universal
  degree-zero base change and cumulative induction through normal-integral
  vanishing. Each step cites the node IDs it uses.
- Stage-2 import rule 7: the module omitted its already recorded proof
  dependencies. Added their thirteen modules as nonpublic imports, keeping
  the statement imports public. The exact-exchange module was already a
  public statement import. I checked the source import graphs: none of
  the added modules imports this theorem, so no cycle is introduced.
  Dependencies without a recorded module cannot yet be imported; they are
  still named in the proof docstring for stage 3.

The mathematical Lean signature was already correct and is unchanged.
The node's `lean.statement` is verbatim equal to the signature in the file.
There are no new definition nodes or dependency modules, no hollow
definitions, no private copies, and nothing proved: the sole theorem's
entire proof remains `sorry`. Compilation and delivery preflight are run
on this repaired packet using the prescribed wrappers.

Validation: `scompile.py Q07 lem-kun-0f1i
lean/Sheaf/Targets/BaseChangeTowardsFields.lean` exited successfully with
no errors or warnings. It compiled the four needed overlay dependencies,
the sandbox module and the library-path module. The signature equality and
100-character Lean line limit were also checked mechanically.
