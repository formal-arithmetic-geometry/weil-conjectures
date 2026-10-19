## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProEtaleClassicalBounds.lean` states
`AlgebraicGeometry.ProEtale.classicalUniformBounds`, with the postponed proof `sorry` required
for stage 2.  Its auxiliary proposition
`AlgebraicGeometry.ProEtale.HasClassicalUniformBounds` packages the three clauses for one
finite-type source, target, map, and torsion sheaf.  It has real data only: the dimension is
computed as `(topologicalKrullDim S).unbotD 0 |>.toNat`, so the empty scheme receives dimension
zero, and the bound is `2 * d + 1`.

The theorem hypotheses render the opening sentence as follows.

- `k : Type u` with `[Field k]` and `hk : Finite k ∨ IsAlgClosed k` is exactly the finite or
  algebraically closed ground field alternative.
- `aX : X ⟶ Spec (.of k)` and `aY : Y ⟶ Spec (.of k)`, with
  `[LocallyOfFiniteType aX] [QuasiCompact aX]` and the corresponding instances for `aY`, are
  the finite-type `k`-scheme hypotheses.  The map `g : X ⟶ Y` with
  `[LocallyOfFiniteType g] [QuasiCompact g]` is the finite-type morphism hypothesis.
- `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` is an abelian étale sheaf and
  `hG : G.IsTorsion` is the local-section torsion condition.  There is no fixed annihilator,
  finite coefficient ring, constructibility, or invertibility assumption.

The three clauses inside `HasClassicalUniformBounds` are rendered clause by clause.

1. `U : S.ProEt` is an object of the small pro-étale site.  The hypothesis
   `proAffineEtale U.hom` is the recorded notion of a nonempty cofiltered affine étale
   presentation with affine transitions.  For every integer `q` above
   `(2 * ((topologicalKrullDim S).unbotD 0).toNat + 1 : ℤ)`, the term
   `IsZero ((DerivedCategory.homologyFunctor _ q).obj ((rightDerivedGlobalSections ...).obj
   ((DerivedCategory.singleFunctor _ 0).obj ((ProEtale.upperStar ... U.hom).obj
   ((comparisonUpperStar ... S).obj F)))))` says
   `H^q(U_Proet,(ν_S^*F)|_U)=0`.  `comparisonUpperStar` is `ν_S^*`, and the pro-étale
   `upperStar` along `U.hom` is the inverse image/restriction to the object.
2. `V : R.ProEt` and `proAffineEtale V.hom` give the corresponding presentation over the
   target.  `pullback f V.hom` is the specified fibre product
   `T = S ×_R V`, while `pullback.fst f V.hom` pulls the coefficient from `S`; the same
   derived-global-sections expression therefore says
   `H^q(T_Proet,(ν_S^*F)|_T)=0` above the source bound.  The target-side presentation and
   all affine transition requirements are retained through `proAffineEtale`.
3. For every `q` above the same bound,
   `IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
   ((Etale.lowerStar ... f).rightDerivedFunctorPlus.obj
   ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))` says
   `R^q f_Et,* F = 0`.  The `Plus` derived functor is the recorded right-derived direct image
   on the bounded-below étale derived category.

The final theorem conjunct quantifies an arbitrary finite-type `k`-scheme `Z` via `aZ` and an
arbitrary finite-type map `h : Y ⟶ Z`, together with any torsion sheaf `H` on `Y_Et`, and
repeats the same three assertions with source `Y`, target `Z`, sheaf `H`, and the bound
`e_Y`.  Taking `Z = Y` and `h = 𝟙 Y` gives the absolute assertion for `Y`; no extra
separatedness or nonemptiness hypothesis is introduced.

Dependency declarations used:

- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`.
- `def-kun-topological-krull-dimension`: Mathlib `topologicalKrullDim`.
- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` and its topology, from
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `def-weil-pbc-etale-sheaves`: `CategoryTheory.Sheaf` and `CategoryTheory.Sheaf.IsTorsion`.
- `def-weil-pbc-site-comparison-morphism`: `AlgebraicGeometry.ProEtale.comparisonUpperStar`.
- `def-weil-pbc-inverse-image` and `def-weil-proetale-inverse-image`:
  `AlgebraicGeometry.ProEtale.upperStar`.
- `def-weil-pbc-etale-cohomology`: `AlgebraicGeometry.ProEtale.rightDerivedGlobalSections`.
- `def-weil-pbc-sites-and-cohomology`: the `DerivedCategory` single and homology functors.
- `sk-def-pe-morphisms`: `AlgebraicGeometry.proAffineEtale`.
- `def-pc-fibre-product`: Mathlib `CategoryTheory.Limits.pullback`, `pullback.fst`, and
  `pullback.snd` for schemes.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` and its
  `rightDerivedFunctorPlus`.

Searches for an existing declaration were made before writing.  `msearch.py` LeanFinder with
“uniform cohomological dimension bounds for torsion sheaves on pro-etale affine limits over
finite type schemes” returned affine-transition-limit lemmas and unrelated étale/cotangent
lemmas, with no uniform bound.  `msearch.py` Loogle with
`topologicalKrullDim, proAffineEtale, rightDerivedGlobalSections, IsTorsion` returned no hits
(the search service reported `proAffineEtale` as unknown).  `msearch.py` grep with
`proAffineEtale|rightDerivedGlobalSections|classicalUniformBounds` in Mathlib returned no
hits.  `rg` over the source and the shared `lean/Sheaf` tree found the existing generic
`rightDerivedGlobalSections`, `upperStar`, and `proAffineEtale` declarations but no declaration
of this three-part finite/algebraically-closed uniform-bounds statement.  The exact existing
interfaces are imported and used; no private copy of them is introduced.

Edge cases checked: the explicit empty-scheme convention gives `d = 0` and hence `e = 1`;
empty pro-étale objects and empty fibre products remain quantified; `q` is an arbitrary integer
with the strict inequality from the node; the torsion sheaf may have locally varying positive
annihilators; finite fields and algebraically closed fields are separate branches of `hk`; and
the final identity-map case for `Y` is included.


## Second reading by Q31

I independently opened the sandbox node, its module, every statement-dependency record,
and the actual declarations used below. I read the main-20261015 detail statement and
proof, the node's eleven expanded proof steps, the upstream pro-affine presentation
and site functors, and Stacks 01T6, 03Q8 and 099W in their local TeX sources. The detail
source assumes finite type, not separatedness; 099W is valid for every scheme and
03Q8 for every scheme morphism. No additional standing hypothesis belongs in Lean.
There is no repair note for this item, no new node, no dependency-module delivery,
and no stage-2 `statement_change` to audit.

The independent list of objects, hypotheses and conclusions, with its final mapping:

1. Ground field k, finite or algebraically closed: `{k : Type u} [Field k]` and
   `hk : Finite k ∨ IsAlgClosed k`. Verdict: exact; neither a finite-field-only nor
   a characteristic-zero restriction is present.
2. Finite-type k-schemes X and Y: `{X Y : Scheme.{u}}`, structure maps `aX`, `aY`,
   and `LocallyOfFiniteType` plus `QuasiCompact` for each. I opened Mathlib's
   `LocallyOfFiniteType` and the recorded finite-type convention. Verdict: exact.
3. Finite-type g from X to Y: `(g : X ⟶ Y)` and its two finite-type instances.
   Verdict: exact. The node does not require `g ≫ aY = aX`; Lean adds no such equation.
   It also adds no separatedness, Noetherian instance, or nonempty source assumption.
4. Common larger small-site universe: `Scheme.{u}`, `S.ProEt`,
   `Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}`. I opened the actual
   `Scheme.ProEt` and `ProEt.topology` definitions. These are the weakly etale
   over-category and its fpqc precoverage topology, with objects in u+1, morphisms
   in u, and abelian group values in u+1. Verdict: the recorded size convention,
   with arbitrary u; no equality of object and morphism universes is imposed.
5. Source dimension with the explicit empty convention and bound: in the transparent
   helper, `dS := (topologicalKrullDim S).unbotD 0 |>.toNat` and
   `eS := 2 * dS + 1`. I opened Mathlib's dimension definition (chains of nonempty
   irreducible closed sets) and the finite-type finite-dimension declaration.
   Verdict: exact: bottom maps to zero and a finite natural dimension is unchanged.
   The `toNat` top case is irrelevant under the theorem's finite-type hypotheses.
6. Arbitrary torsion abelian etale G, without a common annihilator:
   `(G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion)`.
   I read `CategoryTheory.Sheaf.IsTorsion`: every section has a covering sieve on
   whose restrictions it has finite additive order. Verdict: exactly locally killed
   by positive integers; no finite coefficient, constructibility or invertibility
   hypothesis is hidden here.
7. Comparison nu and restriction: `comparisonUpperStar ... S` is the existing
   left Kan extension along `toProEt S` followed by sheafification;
   `ProEtale.upperStar ... f` is the corresponding inverse image along scheme
   base change. I opened both definitions and `Etale.upperStar`, rather than infer
   their meaning from the names. The site's recorded comparison module uses the
   same canonical construction. Verdict: the node's actual coefficients.
8. Cohomology is right-derived global sections: the helper uses the existing
   `ProEtale.rightDerivedGlobalSections`, defined as `R(Sheaf.Γ ...)`, on
   `DerivedCategory.singleFunctor _ 0`, followed by `homologyFunctor _ q`.
   I also opened the recorded etale `rightDerivedGlobalSections`/`cohomology`.
   Verdict: exact ordinary cohomology, not compactly supported cohomology or
   cohomology of a different constant coefficient.
9. First conclusion, for every pro-etale affine U over X and every q > e_X:
   the helper's first conjunct is `∀ (U : S.ProEt), proAffineEtale U.hom →
   ∀ q : ℤ, (eS : ℤ) < q → IsZero (...)`, with coefficient
   `upperStar U.hom` of `comparisonUpperStar S F` on U's own site.
   I read `proAffineEtale` and `MorphismProperty.pro`: a small cofiltered nonempty
   category, absolutely affine etale stages, compatible structural maps and an
   `IsLimit` cone. Maps between affine schemes are affine, giving precisely the
   required affine transitions. Verdict: exact presentation and quantifier order.
10. Second conclusion, every such V over Y, T = X times_Y V, q > e_X:
    the second conjunct quantifies `V : R.ProEt`, requires
    `proAffineEtale V.hom`, and uses `pullback f V.hom` and its source projection
    `pullback.fst f V.hom`. Verdict: the correct fibre product and pullback of
    nu_X^*G, still with the source bound, with no finite-type assumption on T or V.
11. Third conclusion, higher etale direct images vanish for q > e_X:
    the third conjunct applies `DerivedCategory.Plus.homologyFunctor` to
    `(Etale.lowerStar ... f).rightDerivedFunctorPlus.obj (singleFunctor 0 F)`.
    I opened `Etale.lowerStar` and the recorded bounded-below derived-image API.
    Verdict: exactly R^q g_Et,* G, an etale sheaf on the target; `IsZero` is in
    that abelian category, not on a bare type.
12. Repeat every clause with source Y and bound e_Y, arbitrary torsion H and any
    finite-type h to a finite-type k-scheme Z: the theorem's second conjunct
    quantifies `Z`, `aZ`, its finite-type instances, `h`, its instances, `H`,
    and `hH`, then invokes `HasClassicalUniformBounds hk aY aZ h H hH`.
    Verdict: all three conclusions repeat with the correct source and bound.
    The identity h is permitted, including the original absolute Y assertion.

Edge cases: the presentation category is nonempty by `IsCofiltered`, as required,
so the empty index category is correctly excluded. Its affine schemes and its limit
may still be empty. Empty X gives d_X = 0 and e_X = 1; empty products and empty Y
remain covered. A zero coefficient sheaf is allowed. For a nonempty dimension-zero
source the bound is also one. Degrees are all integers and the strict inequality
includes exactly the requested degrees; q = 0 imposes no unintended assertion.
Positive-characteristic torsion, including torsion at the characteristic, is allowed.
The arbitrary universe u and the common u+1 coefficient/site convention retain the
node's size cases.

Independent searches: `msearch.py` LeanFinder with “Vanishing of higher derived
 direct image for every torsion abelian etale sheaf on a finite type scheme over
 an algebraically closed field in large degree” returned generic derived-category
vanishing and injective/projective derived-functor lemmas, not this statement.
Loogle `"IsTorsion", "IsZero"` returned zero hits. The grep query
`cd.*torsion|torsion.*bound|uniform.*cohomol` returned only Cauchy-Davenport results.
I separately used rg on Mathlib, the slopmaster2 WeilConjectures tree, and shared
lean/Sheaf with `uniform.*(cohom|bound)|torsion.*(bound|vanish)|classical.*bound`,
and with the proposed declaration names. The existing generic torsion-dimension,
finite-type and affine-limit results supply parts of the proof but none states
this three-clause conclusion. I opened upstream `HasUniformCohomologicalDimensionLE`
in `ExceptionalAdjoint.lean`: it tests all pro-etale sheaves after base change,
not these classical torsion coefficients, so it is not an exact match. The helper
only packages this item's three clauses and constructs no second site, torsion
predicate, inverse image, derived functor or presentation notion.

Mismatches repaired: H8, the initial source comment was not a module docstring
and preceded imports; replaced it with the conventional copyright header and
`/-!` module documentation after imports. H8, the theorem docstring collapsed the
eleven-step node proof into one sentence; expanded it step by step, including the
all-torsion finite-field reduction, finite quotient inflation, dimension and qcqs
checks, both limit comparisons, the direct-image sheafification argument, the empty
source, and repetition for Y, with the dependency IDs. H9/stage-2 import rule,
replaced the unrelated cohomological-dimension-comparison import and unused affine
comparison import by the defining imports and the recorded statement modules;
added non-public imports for every recorded stated proof dependency not already
publicly imported. The helper's `let` bindings are inside a transparent definition,
not the theorem signature, so they unfold normally in stage 3 and were retained.
No mathematical mismatch required changing a declaration or node statement.

Validation: scompile.py compiled the only delivered file cleanly, including its
live overlay dependencies; no error or warning was emitted. Every universe and
variable is explicitly bound. The only postponed proof is `classicalUniformBounds`,
whose body remains `by sorry`; the helper is an actual Prop expression. The node's
`lean.statement` was checked to be verbatim equal to the unchanged theorem signature.

## Maintainer review fix (landing compile)

The maintainer's reviewer removed two imports from the module. The statement, the
docstrings, the node record and the mathematics are unchanged.

- `public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` was removed.
  No declaration of this module is used by the statement. The abelian pro-étale inverse
  image used is `ProEtale.upperStar`. It is the same term as the recorded
  `Scheme.proEtaleSheafInverseImage` (abbrev: `sheafPullback` along
  `MorphismProperty.Over.pullback @WeaklyEtale ⊤ f`).
  With the import in place, the module failed to compile on the server (2026-10-17). The side
  framework now has two declarations named
  `AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`, in
  `ProEtale.LowerShriek.OpenImmersion.Defs` and in
  `ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`. This import was the only route to the
  second one, while `ProEtale.Derived.LowerShriek`, which the statement needs, brings in
  the first.
- `import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison` was removed. This is the
  stated proof dependency `sk-prop-sf-comparison`. It transitively imports
  `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison`, which currently fails to
  compile on its own because of the same duplicate. Stage 3 should restore this import once
  the side framework's duplicate declaration is resolved.
