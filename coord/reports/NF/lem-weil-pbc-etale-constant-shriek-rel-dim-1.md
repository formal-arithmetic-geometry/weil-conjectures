## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne` states
`AlgebraicGeometry.Etale.constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one`.
Its sole proof is `sorry`. No definition, new node, dependency repair, or statement correction
was necessary. The docstring contains all six proof steps of the node, including their cited
nodes: Noetherian closed-subset induction, the good-curves diagram and surjective descent,
two open-closed localization reductions, proper smooth curve finiteness and finite disjoint
union assembly, and gluing across the remaining closed subset and reduction of the base.

Clause-by-clause correspondence:

- A finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is the established small-etale module-sheaf size convention, with scheme universe `u`.
- A finitely generated integer algebra is `(A : Type u) [CommRing A]
  [Algebra.FiniteType ℤ A]`. The integer algebra structure is canonical. The base `S = Spec A`
  is literally `Spec (CommRingCat.of A)` throughout the signature, rather than an arbitrary
  affine scheme with an unspecified identification.
- The morphism is `{X : Scheme.{u}} (h : X ⟶ Spec (CommRingCat.of A))`.
  Its separatedness and affineness are `[IsSeparated h] [IsAffineHom h]`.
- Smoothness of relative dimension one is `[SmoothOfRelativeDimension 1 h]`. This is exactly
  the declaration recorded by `def-sbc-smooth-morphisms`; it entails smoothness, so a separate
  smoothness assumption would be redundant. In particular it does not require nonempty fibres.
- The ambient qcqs and finite-type conventions do not require extra assumptions here:
  `Spec A` is affine, `X` is affine because `h` is affine over an affine scheme, and smooth
  morphisms are locally of finite presentation. Thus the morphism is of finite type and both
  schemes are qcqs. These consequences are not substituted for stronger hypotheses.
- A finite module is `(M : ModuleCat.{u + 1} Λ) [Finite M]`. It is finite as a set, exactly as
  requested; over finite Λ this is equivalent to finite generation.
- The constant sheaf is `(constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M`.
  It is the existing sheafification of the constant module presheaf, with its Λ-linear structure.
- Placement in degree zero is `(_root_.DerivedCategory.Plus.singleFunctor
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj` applied to that sheaf.
  Hence the input and the compact-support functor both use the specified bounded-below category.
- Every chosen compactification is covered by `(c : Compactification h) [QuasiCompact c.i]`.
  `Compactification` supplies the open immersion, proper map, and factorization equation;
  the explicit `QuasiCompact c.i` is the remaining condition in the node's definition of `c`.
- `rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c` is exactly
  `Rp_* j_!` on bounded-below derived categories: the exact extension by zero followed by
  bounded-below right derived direct image. It is not the right derived functor of the
  underived composite.
- Every degree is `(q : ℤ)`, with no sign or upper bound. The output cohomology sheaf is
  `(_root_.DerivedCategory.Plus.homologyFunctor
  (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj`.
- Constructibility is exactly `Scheme.IsConstructibleEtaleModuleSheaf` of that cohomology
  sheaf, using the recorded finite constructible locally closed stratification and finite
  locally constant module values.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-scheme-conventions` is a conventions-only record with no module or declaration;
  its properties are rendered by the existing Mathlib classes, not a new definition.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and its
  `rightDerivedLowerShriekOfCompactificationPlus` counterpart.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, used inside the compact-support functor.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` and `rightDerivedLowerStarPlus`, used inside that functor.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the established module-sheaf derived-category
  encoding; `DerivedCategory.Plus`, `DerivedCategory.Plus.singleFunctor`, and
  `DerivedCategory.Plus.homologyFunctor` specialize existing Mathlib constructions.
- `WeilConjectures.ConstructibleSheaf.Defs`: `Scheme.LocallyConstantDatum` and
  `Scheme.IsLocallyConstantSheaf`, used in the recorded constructibility predicate.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, restricted to Plus by the homology functor above.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.

The recorded proof-dependency modules are imported without `public` unless already needed
in the public signature. Mathlib-only proof matches without a recorded module are supplied
transitively by these imports. No dependency is copied or restated.

Source and edge-case checks: read the actual `lemma-constant-shriek-rel-dim-1` in
`literature/stacks-project/more-etale.tex` (Tag 0GKX). Its Noetherian finite-dimensional affine
base hypothesis holds for finite-type integer algebras; the DAG intentionally states this
specialization. Finite commutative rings satisfy its torsion Noetherian coefficient requirement.
No assumption that the order of Λ is invertible on the base is present or needed. Empty base,
empty source, nonsurjective morphisms/empty fibres, nonreduced bases, zero module, and trivial
coefficient ring are all retained. Relative dimension is a local condition at source points,
so it is vacuous for the empty source, as it should be. Negative degrees are retained and
have zero cohomology; the theorem does not impose a cohomological range. The compactification
is arbitrary and no existence or choice of compactification is assumed beyond the argument `c`.
All universes and variables are explicit; there are no local notations, instances, or lets.
No statement dispute or node fault was found.

Searches before writing:

- `msearch.py ... leanfinder "compactly supported cohomology constant finite module smooth
  affine relative dimension one constructible"`: eight hits on unrelated qcqs/global-section
  and limit results; none states this theorem.
- `msearch.py ... loogle "AlgebraicGeometry.SmoothOfRelativeDimension,
  AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf"`: zero hits; Loogle does not index
  the side-project constructibility name.
- `msearch.py ... grep "constant.*shriek|shriek.*constant|constructibleCohomology"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "compactly supported cohomology constant finite module affine
  smooth relative curve constructible"`: unavailable, Internal Server Error. Other searches
  and direct source inspection were used.
- `rg` of `constant.*shriek|shriek.*constant|constant.*Shriek|Shriek.*constant` in
  `WeilConjectures` and `lean/Sheaf`: constant-twist comparisons, field curve assertions,
  underived etale extension by zero, and affine-line constructibility are different statements.
  The lisse-relative-line consumer cites this item in its proof; it does not state this item.
- `grep -rn` for this item's exact id in upstream `WeilConjectures`: no result.
- `rg` in `dag/lean_names_upstream.json`: only the unrelated constant-twist, field-curve,
  and filtration declarations; no exact theorem. The chosen declaration name is fresh.

Validation: `scompile.py NF lem-weil-pbc-etale-constant-shriek-rel-dim-1` compiled this delivered
file in isolation against the published library and private side overlay, with no errors or
warnings. The node copy changes only `lean`, using the signature extracted by the project's
statement reader. The worker runs `deliver2.py --no-push`; independent reading and delivery
are reserved for the second reader.


## Second reading by NF

Independent review with the delivered node, module, dependency nodes and source open.
I read Stacks `more-etale.tex`, `lemma-constant-shriek-rel-dim-1` (0GKX), including
its proof and the preceding compact-support conventions. The source assumes a
Noetherian affine finite-dimensional base and torsion Noetherian coefficients.
The node explicitly specializes this to finite commutative coefficients and an
integer algebra of finite type. These imply the source hypotheses; this is the
node's intended specialization, not a restriction introduced by the Lean.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. Finite commutative ring Lambda: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
   There is no field, nontriviality, primality or invertibility assumption.
2. Finitely generated integer algebra A and S = Spec A: `(A : Type u)
   [CommRing A] [Algebra.FiniteType ℤ A]`, with the actual term
   `Spec (CommRingCat.of A)` throughout. The canonical integer algebra introduces
   no additional choice of structure.
3. Scheme X and h : X -> S: `{X : Scheme.{u}}` and the displayed morphism binder.
   These use the recorded Mathlib Scheme and its morphisms.
4. Separated, affine, smooth of relative dimension one: `[IsSeparated h]
   [IsAffineHom h] [SmoothOfRelativeDimension 1 h]`. I read the Mathlib classes:
   separated means closed diagonal; affine means affine preimages of affine opens;
   relative smoothness means locally standard smooth charts of that dimension and
   implies Smooth. This matches `def-sbc-smooth-morphisms`, including empty fibres.
5. The ambient finite-type and qcqs convention adds no hypotheses here: Spec A is
   affine, h affine makes X affine and h quasi-compact, and smoothness gives local
   finite presentation and hence local finite type. Thus X and S are qcqs and h is
   finite type. No extra finiteness or Noetherian instance occurs in the signature.
6. Finite Lambda-module M: `(M : ModuleCat.{u + 1} Λ) [Finite M]`. Finite here is
   finite as a set, as the node requires; for finite Lambda it also agrees with
   finite generation. Lambda-linearity is preserved by the category of values.
7. Constant sheaf on X_et: `(constantSheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ)).obj M`. I read Mathlib `constantSheaf`: it is the constant
   presheaf followed by sheafification, exactly the dependency's construction.
8. Degree-zero input in the bounded-below category: `DerivedCategory.Plus.singleFunctor
   (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0`. Its Mathlib definition
   lifts the ordinary single cochain complex into Plus; no boundedness assumption
   on the output beyond the specified bounded-below category has been inserted.
9. Each compactification: `(c : Compactification h) [QuasiCompact c.i]`.
   I read `WeilConjectures.Compactification.Defs`: c contains Z, open immersion i,
   proper g and `comm : h = i ≫ g`. Its structure alone does not require i
   quasi-compact, so the explicit condition precisely matches the node's datum.
10. Compact support Rh_!^c: `rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} Λ) c`. I read its definition in the upstream Derived.LowerShriek
    module: it is `D+(i_!) ⋙ R+(g_*)`. I also read the underlying recorded
    `openImmersionLowerShriek`, `lowerStar`, and `rightDerivedLowerStarPlus`
    declarations. This is Rp_* j_!, with exact extension by zero; it does not
    derive the underived composite. All coefficient-category instances are supplied
    for ModuleCat by the imported framework, not additional theorem assumptions.
11. Every integer q, every c: `(c ...) [QuasiCompact c.i] (q : ℤ)` are universal
    arguments. Exchanging these two universal quantifiers makes no mathematical
    change. There is no sign, upper bound or chosen-only compactification.
12. H^q is `DerivedCategory.Plus.homologyFunctor ... q`, whose definition I read:
    inclusion into the derived category followed by its homology functor. The
    conclusion is exactly `Scheme.IsConstructibleEtaleModuleSheaf` of that sheaf.
    I read this dependency's full definition and its LocallyClosedStratification
    and LocallyConstantDatum ingredients: a finite partition realized by immersions,
    constructible parts, inverse image to each stratum and an etale trivialization
    by finite constant modules. This retains both finite values and module structure.

I opened all twelve statement-dependency node records and the declarations used
from their modules. The conventions-only dependency defines no separate object.
The derived-categories module explicitly records the same ModuleCat-valued encoding
used here; its torsionCohomology predicate need not occur in this statement.
No dependency interface repair, new definition node or statement correction is
needed. There are no sibling modules or `statement_change` to audit.

Edge cases: zero module, zero coefficient ring, A the zero ring (empty base), empty
source, missing fibres, nonreduced base and all residue characteristics are allowed.
The relative dimension is fixed to one, not an unbound dimension parameter; no
claim for dimension zero has been accidentally substituted. q = 0 and negative q
are included. No family index or nonemptiness assumption occurs. Universe u is
explicit and arbitrary; the coefficient/module universe u+1 is the recorded small
etale convention and allows finite coefficients and finite modules by transport.
No independent site-universe equation or extra size assumption is imposed.

Independent searches used different terms from the worker:

- LeanFinder: `finite constant etale module cohomology with proper support
  constructible affine smooth curve` returned eight algebra/etale-locus results,
  none the statement.
- Loogle: `AlgebraicGeometry.SmoothOfRelativeDimension` returned twelve geometry
  declarations (the class, permanence and local chart facts), no compact-support
  constructibility statement. An initial query also containing the invalid name
  `CategoryTheory.Finite` was discarded and replaced by this valid query.
- msearch grep: `constructible.*(shriek|support)|shriek.*constructible` returned
  zero Mathlib hits.
- Direct case-insensitive rg in Mathlib, upstream WeilConjectures, project
  lean/Sheaf, and dag/lean_names_upstream.json for constant/shriek and
  constructible/affine/relative-dimension combinations. I opened the upstream
  curve-normalization assertions and project EtaleLowerShriekConstantConstructible:
  they concern algebraically closed field curve assertions or underived etale
  extension by zero, respectively. Neither is this relative smooth-curve theorem.
  Constant twists concern other coefficient categories. The lisse-relative-line
  module merely cites this node in its proof. No exact existing declaration found.

H5/H6/H8/H9 inspection: no new definitions, hidden data, extra conclusions or
proved helpers; the sole theorem has whole proof `by sorry`. The source/blueprint
module and theorem docstrings are present. The theorem docstring carries each of
the node's six proof steps and their cited nodes. All variables and the sole
universe u are bound; no local notation, private declaration, local instance or
statement let is present. The node lean.statement agrees with the module signature.

Mismatches found: none. Changes: appended this independent reading only; the Lean
and node were left intact. Validation: prescribed scompile.py compiled both the
sandbox probe and library-named file cleanly (3.5 s and 3.9 s), with no errors or
warnings. Delivery dry run and push follow below through deliver2.py.
