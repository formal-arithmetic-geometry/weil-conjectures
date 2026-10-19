## Worker report

`Sheaf.AlgebraicGeometry.OpenComplementCondition` defines
`AlgebraicGeometry.Scheme.HasOpenComplementCondition`. It is a proposition for a finite
commutative coefficient ring `A`, schemes `V,T`, a quasi-compact open immersion
`j : V ⟶ T`, and a nonnegative bound `c : ℕ`. The definition has the two conjuncts in the
node and contains no proof or choice data.

The first clause of the node, “for every sheaf `M` of `A`-modules on `V_et` and every integer
`q > c`, `R^q j_* M = 0`,” is rendered by

```
∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
  (q : ℤ), (c : ℤ) < q →
  IsZero ((DerivedCategory.Plus.homologyFunctor
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
    ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj M)))
```

Here `Plus.singleFunctor` places `M` in degree zero, `rightDerivedLowerStarPlus` is the
canonical `Rj_*` on the bounded-below derived categories, and `Plus.homologyFunctor` is
`H^q`; `IsZero` is the categorical zero-sheaf assertion. The natural-number binder `c`
encodes exactly `c ∈ ℤ_{≥0}`.

The second clause, “for every constructible sheaf `F` and every integer `q`, `R^q j_* F` is
constructible on `T_et`,” is rendered by

```
∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
  IsConstructibleEtaleModuleSheaf F →
  IsConstructibleEtaleModuleSheaf
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
      ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F)))
```

`IsConstructibleEtaleModuleSheaf` is the recorded finite-coefficient constructibility
predicate, so this clause keeps the coefficient category and the target site fixed exactly
as in the node.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`; only the `QuasiCompact` class is used in this
  definition, while `IsOpenImmersion` comes from the preceding dependency.
- `def-weil-pbc-etale-site`: Mathlib `AlgebraicGeometry.Scheme.Etale` and
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, used in the site expressions.
- `def-weil-pbc-etale-sheaves`: `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, whose
  canonical sheaf/module-site encoding is imported; the module uses
  `Sheaf T.smallEtaleTopology (ModuleCat A)` rather than a private category.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`,
  declaration `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`.
- `def-weil-pbc-constructible-complexes`: landed declaration
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` in
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.

The module imports the two landed project interfaces and the Mathlib finite-type morphism
interface; the remaining dependency notions are supplied transitively by those canonical
modules. No dependency module or new definition node was needed.

Edge cases checked: `c = 0` is allowed; `q` ranges over all integers (including negative
values in clause (2)); `M` and `F` may be zero sheaves; `V` and `T` may be empty; and no
connectedness, separatedness, finite-type, affine, or nonzero-coefficient assumption is
added. The open immersion and quasi-compactness are typeclass hypotheses exactly as in the
node. The all-sheaf clause is independent of constructibility, while the constructibility
clause quantifies every integer degree.

Searches made:

- `msearch.py ... leanfinder` with the query “predicate for an open immersion whose
  higher etale direct images vanish above a bound and preserve constructible sheaves”: eight
  generic hits (`IsEtale`, open-immersion lemmas, and site declarations); no predicate
  matching this node.
- `msearch.py ... loogle` with `DerivedCategory.Plus.homologyFunctor,
  rightDerivedLowerStarPlus, IsConstructibleSheaf`: zero hits; Loogle reported the project
  identifier as unknown.
- `msearch.py ... grep` with `open.?complement|cohomological.?dimension|
  rightDerivedLowerStarPlus` in `AlgebraicGeometry`: no Mathlib matches.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf` for `HasOpenComplementCondition`, `openComplementCondition`, and related
  predicate names: no existing declaration. Related cohomological-dimension declarations
  concern torsion global sections and do not express either direct-image clause.
- The node's recorded LeanFinder/Loogle/grep searches were also read; they independently
  report no Mathlib definition of the simultaneous two-clause condition.

No statement correction or `STATEMENT-DISPUTED` flag is needed. The source's finite ring is
rendered as `[CommRing A] [Finite A]`, and all proofs remain postponed only because this is
a stage-2 definition.

## Earlier second reading (a previous round; superseded)

I independently reopened the node, its source paragraph, the module, and all seven dependency
records. The binders match: `A` is finite commutative, `j : V ⟶ T` is an open immersion with
`QuasiCompact j`, and `c : ℕ` is the nonnegative bound. Clause (1) quantifies arbitrary
module sheaves and every integer degree above `c`, then applies the canonical bounded-below
right-derived pushforward and asks for a zero target homology sheaf. Clause (2) quantifies
arbitrary constructible module sheaves and every integer degree, applying the same canonical
pushforward and the recorded constructible predicate on `T`. The zero-sheaf assertion,
coefficient category, site, degree quantifiers, and both hypotheses are present; no extra
hypothesis or omitted case was found. The file compiled cleanly with `scompile.py`, with no
warnings.

## Second reading by N5

I independently read the actual source paragraph at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/def-exc-open-complement-bound.md`
(order 1914), the repository and sandbox node records, the Lean definition, all seven
statement-dependency nodes, and their declaration sources. This node's source is a blueprint
paragraph, not a Stacks statement with additional standing hypotheses. Its concluding
application paragraph does not impose a field, characteristic, dimension, or finiteness-of-type
hypothesis on this definition. The node's explicit commutative-ring convention agrees with
its cited module-sheaf and constructibility definitions.

My object/hypothesis/conclusion list, matched against the repaired Lean:

1. A specified finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A]
   [Finite A]`. PASS. There is no field, nontriviality, or invertibility assumption.
2. Two arbitrary schemes and their specified open immersion: `{V T : Scheme.{u}}`
   and `(j : V ⟶ T) [IsOpenImmersion j]`. PASS. I read Mathlib's `Scheme` and
   `IsOpenImmersion` definitions; these are schemes and open immersions of locally
   ringed spaces, not an affine or Noetherian specialization.
3. Quasi-compactness of that same immersion: `[QuasiCompact j]`. PASS. I read the
   Mathlib class requiring compact preimages of compact opens. No finite-type
   hypothesis is added.
4. A nonnegative integral cutoff: `(c : ℕ)`, used as `(c : ℤ)`. PASS. Naturals
   parameterize exactly the allowed nonnegative integers, including zero.
5. The small etale sites and constant-coefficient module sheaves: `V.smallEtaleTopology`,
   `T.smallEtaleTopology`, and `Sheaf ... (ModuleCat.{u + 1} A)`. PASS. I opened
   Mathlib's `Scheme.Etale`, `smallEtaleTopology`, and its jointly-surjective covering
   criterion, and the recorded `EtaleSheaves` source. The dependency's note explicitly
   authorizes this module-valued encoding for constructible and six-functor material.
6. Higher direct images of sheaves placed in degree zero: the composition of
   `DerivedCategory.Plus.singleFunctor ... 0`, `Etale.rightDerivedLowerStarPlus`, and
   `DerivedCategory.Plus.homologyFunctor ... q`. PASS. I read the three definitions:
   they respectively place a sheaf in degree zero, right-derive the canonical
   base-change/precomposition pushforward, and take its degree-q cohomology sheaf.
7. Clause (1): `∀ (M : Sheaf ...) (q : ℤ), (c : ℤ) < q → IsZero (...)`. PASS.
   Every module sheaf is allowed; the strict inequality and categorical zero assertion
   match the node. Constructibility is not assumed in this clause.
8. Clause (2): `∀ (F : Sheaf ...) (q : ℤ), IsConstructibleEtaleModuleSheaf F →
   IsConstructibleEtaleModuleSheaf (...)`. PASS AFTER REPAIR. The original Lean omitted
   the premise `IsConstructibleEtaleModuleSheaf F`, requiring constructibility of the
   image of every sheaf. I inserted exactly that premise and updated the worker report's
   displayed formula. For example, for the identity of a geometric point and degree zero,
   an infinite-dimensional module over a finite field shows why the original unrestricted
   conclusion was stronger. The earlier second reading's claim that the input was
   restricted to constructible sheaves was incorrect.
9. Both clauses form one predicate depending on `A`, `j`, and `c`: the definition's body
   is their conjunction. PASS. The order of universal quantifiers in clause (2) is
   harmless: its premise depends on `F` only, and every integral `q` is still quantified.

For constructibility I opened `BoundedConstructibleComplexes.lean` and
`IsConstructibleEtaleModuleSheaf.lean`: the former uses exactly the latter predicate on
cohomology sheaves. The latter requires a finite locally closed constructible
stratification with finite constant module values after etale trivialization, matching
the node's referenced sheaf clause. The same predicate is now used on input and output.
The generic right-derived pushforward interface supplies the required ModuleCat instances;
no additional instance binder or choice of a noncanonical map is introduced. There are no
new nodes or dependency modules to audit and no change to the mathematical DAG statement.

Edge cases: `c = 0`, `q = 0`, and negative `q` are included with exactly the node's
inequalities; zero sheaves and empty schemes are allowed. There is no index family or
coefficient-stage integer n in this definition. No characteristic is excluded, and the
zero ring is allowed. The universe `u` is arbitrary; the `u + 1` coefficient/module size is
the recorded convention for the small etale site (objects in `u + 1`, morphisms in `u`),
not a restriction to small coefficients or an equality of distinct site universes.

Independent duplicate searches:

- LeanFinder: “A quasi compact open inclusion has uniformly bounded higher pushforward
  on all etale module sheaves and preserves constructible sheaves” returned eight hits
  about constructible images of scheme morphisms, quasi-compactness, and ordinary
  structure-sheaf-module pushforward. None is this simultaneous etale predicate.
- Loogle: `"cohomologicalDimension"` returned zero hits.
- LeanSearch: “Uniformly bounded higher direct image for arbitrary etale module sheaves
  and preservation of constructibility by an open immersion” returned Internal Server
  Error; recorded as unavailable, not as evidence of absence.
- Wrapper grep: `higherDirectImage|cohomologicalDimension|openComplement` returned zero
  Mathlib hits. Direct `rg` in Mathlib, upstream `WeilConjectures`, the project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json` used `cohomological.?dimension`,
  `preserv.*constructib`, and open-complement variants. The related upstream
  `UpperShriekConstructible` statements were opened: they concern exceptional inverse
  images or finite-type/invertible-coefficient specializations, not this definition.
  The proposed full declaration name is absent outside this delivery.

The repaired definition contains real proposition data, no `sorry`, no proof, no private
notion, and no unbound implicit variables (`autoImplicit false`). Its source/blueprint
and clause-by-clause construction docstrings remain correct. All Lean lines fit 100
characters. The node's `lean.statement` was checked verbatim against the unchanged
signature. `scompile.py N5 def-exc-open-complement-bound
lean/Sheaf/AlgebraicGeometry/OpenComplementCondition.lean`, from the sandbox, passed
both sandbox and library-path compilation cleanly, with no warnings. The sole Lean repair
is the missing constructible-input premise in clause (2).
