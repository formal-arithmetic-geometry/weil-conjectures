## Worker report

The module `Sheaf.AlgebraicGeometry.EtalePullbackTwistTorWindow` states
`AlgebraicGeometry.Etale.etale_pullback_twist_tor_window`. Its only theorem has
proof `sorry`; its docstring contains all five DAG proof steps and their node
references. The node's mathematical statement, statement dependencies and proof
are unchanged. No new nodes or dependency repairs are needed.

Three construction helpers belong to this statement and are listed in
`lean.declarations`. `pullbackTwistComplexMonoidal` exposes the existing canonical
signed-total-tensor monoidal structure with the canonical sheaf tensor supplied
explicitly. It constructs no new tensor product. `pullbackTwistComplex` is the
composition of ordinary module-valued etale `upperStar` with `tensorRight` of the
existing `finiteEtaleTateTwist`, applied termwise by `mapHomologicalComplex`, and
then shifted. `pullbackTwistDerived` applies the exact `mapDerivedCategory`
inverse image, the existing `derivedTensor` with that same twist placed in degree
zero, and shifts the whole product. All three helpers have real definitions;
none chooses data from an existence assertion or contains a postponed proof.
No local instance, notation, private abbreviation or implicit variable is used.

Hypothesis and clause correspondence:

- The field is `k : Type u`, `[Field k]`, its positive characteristic is
  `[CharP k p]` and `_hp : 0 < p`. The prime and inequality are `_hell : ell.Prime`
  and `_hne : ell ≠ p`. The setting node is rendered by explicit binders, as its
  recorded `lean.note` instructs: `T T' : Over (Spec (CommRingCat.of k))` with
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on both structure maps.
  These last two classes mean finite type. `f : T' ⟶ T` is a k-morphism, and
  `f.left` is its underlying scheme morphism. No compactification or condensed
  coefficient structure from the setting node is needed in this ordinary-etale
  specialization.
- `n : ℕ` permits zero. Everywhere `N` is the natural number `ell ^ n`.
  The prime hypothesis implies `1 ≤ N` (including `n=0`), so no independent
  hypothesis about N is added. `R : Type (u+1)`, `[CommRing R]`, `[Finite R]`, and
  `hR : ((ell ^ n : ℕ) : R) = 0` render a finite commutative coefficient ring
  annihilated by N. In a unital ring this equality is equivalent to NR=0.
- Ordinary small-etale categories are exactly `DerivedCategoryModule R T.left`
  and `Sheaf T.left.smallEtaleTopology (ModuleCat.{u+1} R)`, and the analogous
  categories on T'. No pro-etale, condensed, or structure-sheaf derived category
  occurs.
- `Scheme.finiteEtaleTateTwist T'.left (ell ^ n) R hR c` is precisely the recorded
  roots-of-unity scalar extension and its nonnegative tensor powers; its zeroth
  value is the constant ring-module sheaf. `c : ℕ` excludes no nonnegative twist.
- `a b : ℤ` and `_hab : a ≤ b` render the interval. The first conjunct quantifies
  over every `K`, with `DerivedCategory.isBoundedConstructible R T.left K` and
  `DerivedCategory.hasTorAmplitudeIn R T.left a b K`. The former is the existing
  finite-value constructible-cohomology predicate, with boundedness included;
  the latter tests every module sheaf placed in degree zero.
- Every representing `P : CochainComplex ... ℤ` is quantified, with
  `Nonempty (DerivedCategory.Q.obj P ≅ K)`. No selected resolution or augmentation
  is imposed. The next hypotheses say for every degree that `tensorRight (P.X i)`
  is `exactFunctor`, `Scheme.IsConstructibleEtaleModuleSheaf (P.X i)`, and
  `IsZero (P.X i)` if `i < a ∨ b < i`.
- For every `c : ℕ` and `s : ℤ`, the first three conclusion clauses assert
  exactness of tensoring with each term of `pullbackTwistComplex`, constructibility
  of each term, and `IsZero` outside `[a-s,b-s]` respectively.
- The next clause applies the dependency's `MorphismProperty.kFlat` to
  `HomologicalComplex.quasiIso` in exactly the same sheaf-complex category, using
  the explicit canonical total-tensor monoidal structure. This two-sided
  preservation-of-quasi-isomorphisms formulation equals the node's acyclic-test
  formulation: apply preservation to an acyclic complex's map to zero in one
  direction, and use tensor compatibility with mapping cones in the other.
  Signed symmetry interchanges tensor factors. This is the ordinary-sheaf
  interface explicitly exposed by the recorded `def-pc-kflat-complex` module;
  no new K-flat predicate is introduced.
- `Nonempty (DerivedCategory.Q.obj (pullbackTwistComplex ...) ≅
  pullbackTwistDerived ...)` is the actual derived representative assertion,
  an isomorphism in the derived category, not merely cohomology isomorphisms.
  The next clauses state bounded constructibility and Tor amplitude `[a-s,b-s]`
  for exactly that derived object.
- The second main conjunct quantifies independently over every bounded
  constructible K of Tor amplitude `[a,b]`. It asserts bounded constructibility
  and Tor amplitude `[a,b]` for `(upperStar ... f.left).mapDerivedCategory.obj K`.
  It requires no supplied P. Thus the final preservation assertion is not
  accidentally restricted to the chosen-representative clause.

Dependency declarations inspected and used:

- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  with `Etale.DerivedCategoryModule`, `DerivedCategory.Q`, homology and the
  recorded bounded-derived vocabulary. Its public coefficient module gives the
  actual signature of `DerivedCategoryModule`.
- `def-weil-pbc-etale-constructible-sheaf`:
  `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `Scheme.IsConstructibleEtaleModuleSheaf`. Read the full finite-module-value
  stratification definition, not just the record's name.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`, exposing
  the bounded `Etale.DerivedCategory.hasTorAmplitudeIn` of the coefficient module.
  Its full signature tests all degree-zero module sheaves and every integer q.
- `def-pc-cochain-complex-modules`: Mathlib's
  `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex` (lines 153–158),
  specialized to the ordinary etale module-valued sheaf category.
- `def-pc-flat-sheaf-modules`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` publicly exposes
  `CategoryTheory.exactFunctor`. The record explicitly instructs its use on
  `tensorRight` in the `Sheaf (ModuleCat R)` encoding. `IsFlatOnSite` itself takes
  `SheafOfModules`, a different encoding, and is not privately duplicated here.
- `def-pc-kflat-complex`:
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` publicly exposes
  `CategoryTheory.MorphismProperty.kFlat`. Read its actual definition in
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`, including both
  localizer-morphism tests, and the record's Q58 ordinary-sheaf interface note.
- `sk-def-sfb-dc-setting`: inspected `compactificationOverField` and its over-field
  structure-map binders in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  Its note says the setting is explicit binders rather than a new predicate.
  The unrelated condensed compactification module is not imported.
- `def-weil-pbc-inverse-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `Etale.upperStar` and
  its adjunction. The public derived `UpperLowerStar` import supplies its exact
  `mapDerivedCategory` extension; read both interfaces.
- `lem-asd-finite-etale-twist-line`:
  `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`,
  `Scheme.finite_etale_torsion_twist_line`; its public
  `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist` gives
  `Scheme.finiteEtaleTateTwist`. Read both full definitions and the line theorem.
- Bounded constructibility uses the existing
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `Etale.DerivedCategory.isBoundedConstructible`; its definition was read in full.
  It combines precisely the dependency's constructible-sheaf predicate with
  bounded cohomology, avoiding a new boundedness predicate.
- Proof-only Mathlib imports are `AlgebraicGeometry.Noetherian` (read
  `LocallyOfFiniteType.isLocallyNoetherian`, `IsNoetherian`, the Spec instances,
  and `QuasiCompact.compactSpace_of_compactSpace` in its morphism module) and
  `Algebra.Homology.BifunctorShift` (read both shift isomorphisms, the sign formula
  and `Functor.instCommShift₂IntCochainComplexIntMap₂CochainComplex`). The node's
  line-flat-model and scalar-flat-model proof dependencies have no Lean records
  in the read DAG, so there are no recorded proof modules to import for them.
  Neither is needed to type the statement; the future proof uses their statements
  as the docstring describes.

Edge cases checked before drafting: zero objects and zero coefficient ring are
allowed (there is no `Nontrivial R`); the empty scheme and empty stratification
are allowed; `a=b` permits a one-degree model. Positive and negative shifts both
use degree j+s, giving exactly `[a-s,b-s]`. `s=0` gives the original interval.
`c=0` uses the actual constant sheaf defined by the recorded twist, not an
arbitrary line. `n=0` gives N=1, and NR=0 then permits precisely the zero ring;
that legitimate edge case remains included. No N-flatness of R, etaleness of f,
flatness of f, or invertibility hypothesis beyond the field setting is imposed.
Site object universe u+1 and morphism universe u are retained, with the existing
coefficient/module size u+1; the field and schemes have universe u.

Searches performed through the prescribed wrapper:

- LeanFinder: "Pullback of bounded flat constructible etale complexes tensor a Tate
  line and shift preserves K flatness and Tor amplitude": 8 hits concerning
  scheme flat base change, formally etale tensor products, and ordinary module
  flatness/exactness. None states this ordinary-etale complex theorem.
- Loogle: `"kFlat", "shift"`: successful, zero hits.
- Mathlib grep: `finiteEtaleTateTwist|hasTorAmplitudeIn`: successful, zero hits.
- LeanSearch: "Pullback and Tate twist preserve flat constructible etale complexes
  and shifted Tor amplitude": 8 hits, including `SheafOfModules.pullback`,
  `Functor.sheafPullbackConstruction.preservesFiniteLimits`, and ordinary
  `Module.Flat.lTensor_shortComplex_exact`; none gives this statement.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the item id, the proposed full names, and
  pullback/twist/Tor vocabulary found the existing ingredients listed above,
  not this theorem. Inspected `FiniteFlatConstructibleTotalTensor`,
  `FlatConstructibleTensor`, `NoetherianCtfFlatModel` and
  `KFlatSingleTensorRepresentative` to reuse the exact sheaf/tensor/K-flat
  interfaces instead of defining copies. No exact existing statement was found.

Sources read directly in the supplied literature checkout:
`etale-cohomology.tex`, `lemma-when-ctf` (03TT), `lemma-pullback-ctf` (0963),
`lemma-tensor-product-constructible` (095I) and `section-kummer` (03PK).
The line theorem supplies the rank-one specialization; the last source's root
construction matches the recorded finite Tate twist definition. The original
node statement is well-typed and consistent with these sources; no statement
correction or disputed assertion is necessary.

Validation: the delivered module was compiled by `scompile.py` in module mode,
first in its private sandbox module and then with its actual library module name.
Both passed cleanly under the ordinary 60-second per-file limit. Diagnostic
`#check` commands were removed. An initial cast mismatch was repaired by casting
the natural power `ell ^ n` into R, and the monoidal-structure definition uses
`@[instance_reducible]` to avoid the class-definition reducibility warning.

## Second reading by Q114

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
