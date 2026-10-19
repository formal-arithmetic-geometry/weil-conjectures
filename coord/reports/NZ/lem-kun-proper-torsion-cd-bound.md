## Worker report

The module `Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound` states
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le`.
Its only theorem proof is `sorry`; no definition or proof was added otherwise.
The node is unchanged except for its `lean` field. There are no new nodes,
dependency replacement modules, statement corrections, or disputed statements.

Hypothesis and conclusion correspondence:

- Schemes and the given morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Properness: `[IsProper f]`, using the recorded Mathlib definition. Its universal
  closedness implies quasi-compactness of the morphism, giving finite type from
  locally finite type; this imposes no quasi-compactness assumption on `Y`.
- Nonnegative integer dimension bound: `(d : ℕ)`. Naturals parametrize exactly
  nonnegative integers; no case is lost.
- Every scheme-theoretic fibre has dimension at most `d`:
  `hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)`.
  The `WithBot ℕ∞` bottom is negative infinity, so empty fibres are included.
- An arbitrary abelian sheaf on the small étale site:
  `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Torsion: `hF : Scheme.IsTorsionAbelianSheaf F`, the dependency's actual
  colimit-of-multiplication-kernels predicate. This does not require sectionwise
  torsion or one global annihilator.
- Degree and strict inequality: `(q : ℤ) (hq : 2 * (d : ℤ) < q)`.
  Since `d` is nonnegative, all degrees in the conclusion are positive.
- `R^q f_* F = 0`: `IsZero` of `DerivedCategory.Plus.homologyFunctor ... q`
  applied to `rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f` of
  `DerivedCategory.Plus.singleFunctor ... 0` applied to `F`. This is precisely
  degree-q cohomology of the bounded-below derived image of the degree-zero sheaf.
- No Noetherian, constructibility, torsion-order invertibility, ground-field,
  or quasi-compact-target binder occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`:
  `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`. The dependency record names
  this declaration but lists the underived module; the actual defining module is
  additionally imported. No replacement notion is needed.
- Mathlib's `DerivedCategory.Plus.singleFunctor` and
  `DerivedCategory.Plus.homologyFunctor`, whose definitions respectively put a
  sheaf in degree zero and restrict ordinary derived-category cohomology.

Every proof dependency with a recorded module is imported (public for statement
imports, ordinary for proof imports). `def-weil-algebraic-closure` and
`thm-sc-finite-type-torsion-cd` have no recorded module and cannot yet be imported.
The theorem docstring carries all six proof steps, including empty fibres,
finite-type fibre vanishing, the stalk computation, and stalk conservativity.

Edge cases checked: `d = 0` asserts vanishing in all positive degrees;
`q = 2*d` is deliberately excluded. Empty fibres satisfy the bound because bottom
is below every finite dimension. Empty `X` and empty `Y` are permitted, with the
pointwise dimension hypothesis vacuous for empty `Y`. Zero sheaves are allowed.
Positive-characteristic torsion and sheaves without a global annihilator remain
allowed. The arbitrary universe `u` and the recorded sheaf coefficient universe
`u + 1` match the dependency declarations. No generic coefficient category is
substituted for abelian sheaves.

Source read: `literature/stacks-project/etale-cohomology.tex`,
`lemma-cohomological-dimension-proper` (Tag 095U), lines 18785 onwards.
Its statement is exactly properness plus a uniform fibre-dimension bound,
with arbitrary abelian torsion coefficients and strict vanishing above twice the bound.

Searches:

- LeanFinder via `msearch.py`: "Higher direct images of torsion etale sheaves for
  proper morphisms vanish above twice the fibre dimension". Eight results, including
  `DerivedCategory.isZero_of_isGE` and `DerivedCategory.isZero_of_isLE`, but no match.
- Loogle via `msearch.py`: `"cohomological"`. Twelve spectral-object declarations;
  none is the proper étale direct-image bound.
- Mathlib grep via `msearch.py`: `torsion.*proper|proper.*torsion|higherDirectImage`
  in `AlgebraicGeometry`: zero hits.
- LeanSearch via `msearch.py`: "Proper morphisms have higher direct images of torsion
  etale sheaves zero above twice the fibre dimension". Service unavailable (Internal
  Server Error); this supplies no evidence of absence.
- `rg` of project `lean/Sheaf` and upstream `WeilConjectures` for proper/torsion,
  higher-direct-image, and derived-pushforward patterns found the generic derived
  pushforward and base-change results, module-coefficient higher direct images,
  and uses of cohomological-dimension bounds, not this theorem.
- `rg` for the item id in upstream `WeilConjectures`, and the chosen full theorem
  name in upstream declarations, `dag/lean_names_upstream.json`, and `lean/Sheaf`:
  no duplicate declaration found.

Validation: `scompile.py NZ lem-kun-proper-torsion-cd-bound` on the delivered file
passed on the server, nice 19, two threads, 60 seconds per file, without warnings
or errors. The delivered file took 2.9 seconds; required side-only imports were
compiled by the tool into its private overlay. No local compiler or build ran.

## Second reading by NZ

I independently read the sandbox node, its six proof steps, all five statement
 dependency records, the actual dependency declarations, and Stacks
`etale-cohomology.tex`, lemma-cohomological-dimension-proper (Tag 095U), including
its preceding section context. The source assumes only a proper morphism, the
uniform fibre dimension bound, and an abelian torsion sheaf. There is no standing
Noetherian or ground-field assumption. The node needs no correction.

Object/hypothesis/conclusion checklist (every verdict: matches):

1. Arbitrary schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
   These are Mathlib schemes, with an arbitrary explicitly bound universe `u`.
2. Properness: `[IsProper f]`. I read the Mathlib class, which extends separated,
   universally closed and locally finite type. Universally closed supplies
   quasi-compactness of the morphism, so this is finite type as in the node;
   it does not require the target to be quasi-compact.
3. Nonnegative integer bound: `(d : ℕ)`, representing exactly the integers ≥ 0.
4. All scheme-theoretic fibres have Krull dimension ≤ d:
   `hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)`.
   I read `Scheme.Hom.fiber`: its pullback is along `Y.fromSpecResidueField y`,
   with the two recorded fibre projections. I read `topologicalKrullDim`: it
   is `Order.krullDim (IrreducibleCloseds T)`, so these are the node's strict
   chains of nonempty irreducible closed subsets, with empty-space dimension ⊥.
5. Every abelian sheaf on the small étale site:
   `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
   This uses the dependency's site and coefficient universe, not module sheaves
   over a fixed finite ring or a constructible subcategory.
6. Torsion: `hF : Scheme.IsTorsionAbelianSheaf F`. I read its full construction:
   positive integers ordered by divisibility, multiplication kernels, canonical
   inclusions, and `IsIso (colimit.desc D c)`. It is the precise dependency
   predicate, not sectionwise torsion or a uniform annihilator assumption.
7. Degree and bound: `(q : ℤ) (hq : 2 * (d : ℤ) < q)`. This quantifies over
   exactly the requested degrees, all positive since d ≥ 0.
8. Vanishing of the higher direct image: `IsZero` of the displayed degree-q
   `DerivedCategory.Plus.homologyFunctor` applied to
   `rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f` applied to
   `DerivedCategory.Plus.singleFunctor ... 0` of F. I opened all three
   definitions. The single functor places F in degree zero; the derived functor
   is `(lowerStar ... f).rightDerivedFunctorPlus`; homology is restriction of
   derived-category cohomology. I also opened `lowerStar`, which is sheaf
   pushforward along étale base change, with sections F(W ×_Y X). Thus the
   object is exactly R^q f_* F, and categorical `IsZero` is exactly its vanishing.
9. Explicit exclusions in the node: no binder or implicit section variable
   adds Noetherianity, target quasi-compactness, a field, constructibility or
   invertibility of torsion orders. All theorem variables and universes are bound.

Edge cases: empty fibres have dimension ⊥ and satisfy hd; empty X is allowed;
empty Y makes hd vacuous and is allowed. The zero sheaf is allowed. At d = 0
all positive q are covered, while q = 2d is excluded exactly as requested.
Negative q cannot satisfy hq. There is no indexed family in this statement;
its only universal index is y, and the empty case is covered. Characteristic-p
torsion and torsion sheaves without a common annihilator are included. The
scheme/site/sheaf universes agree with the recorded dependencies and introduce
no extra universe variable or size hypothesis.

Independent searches, using wording different from the worker's:

- LeanFinder via msearch: “Cohomology sheaves of the derived pushforward of
  torsion abelian etale sheaves vanish beyond twice the relative dimension of
  a proper map”. Eight generic t-structure/single-complex vanishing hits,
  including `DerivedCategory.isZero_of_isLE`; none supplies this geometric bound.
- Loogle via msearch: `"IsProper", "IsZero"`: zero hits.
- Mathlib grep via msearch in AlgebraicGeometry:
  `cohomologicalDimension|cohomological_dimension|fiber_dimension_le|relativeDimension`.
  Ten hits concern smooth/étale relative dimension, not this vanishing theorem.
- Independent rg across project Sheaf, upstream WeilConjectures and Mathlib
  AlgebraicGeometry for proper/torsion, the source lemma name and the proposed
  declaration. No duplicate statement found. I opened the potentially relevant
  upstream Derived/UpperShriek discussion and the project's
  EtaleProperDerivedDirectImageAdjoint: both cite a dimension bound in their
  proof plans but state adjoint existence, not the bound. Proper base-change
  isomorphisms and curve Picard-torsion results are also different statements.
  The worker's recorded LeanSearch service failure remains a failure, not
  evidence of absence.

No new definition nodes or dependency modules were delivered, and none is needed:
all five statement dependencies give the required notions. There is no
statement_change, no corrected citer verdict to check, and no target change.
The declaration and module docstrings name the source and blueprint id. The
proof plan follows all six node steps (including the empty-fibre argument,
finite-type cohomological bound, explicit stalk computation, and conservativity).
The sole theorem proof remains `sorry`; no hollow definition, helper proof,
private notation or local instance is introduced. No mathematical mismatch was
found, so the Lean and node were left unchanged; only this review was appended.

Second-reader validation: scompile.py passed on the server (nice 19, two
threads, default 60 seconds per file). The delivered module took 2.9 seconds,
with no errors or warnings; side-only imports were compiled in the private
overlay. The node's lean.statement is verbatim the file's theorem signature,
and every Lean line is at most 100 characters. No local compiler or build ran.
