## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteSupportDefectConservativity` states
`AlgebraicGeometry.Etale.finiteSupportDefectConservativity`. Its sole proof is `sorry`;
there are no new definitions, axioms, dependency repairs, or statement corrections.

Clause-by-clause correspondence:

- The schemes W, S and V are arbitrary `Scheme.{u}`; `h : W ⟶ S` is the given morphism.
- `i : V ⟶ W` with `[IsClosedImmersion i]` is the given closed immersion.
- `[IsFinite (i ≫ h)]` states precisely that f = h composed with i is finite.
- `A : Type (u + 1)` with `[CommRing A] [Finite A]` is a finite commutative ring.
  This is the recorded six-functor coefficient size convention, with modules and
  sheaves in universe u+1 and schemes in u. No nonzero ring assumption is made.
- `K : DerivedCategory.Bounded (Sheaf W.smallEtaleTopology (ModuleCat A))`
  is exactly K in D^b(W_et,A). `K.obj` is its image under the full inclusion in D(W_et,A).
- `_hK` states `IsZero` of the exact inverse image of K under the inclusion of
  the open complement of the image of i. The inclusion is constructed directly as
  `Scheme.Opens.ι (X := W) ⟨(Set.range i.base)ᶜ,
  i.isClosedEmbedding.isClosed_range.isOpen_compl⟩`. Closedness follows from the
  given closed immersion. Thus no choice of a different open, no additional
  geometric hypothesis, and no arbitrary restriction functor is introduced.
  Exact inverse image is `(upperStar (ModuleCat A) j).mapDerivedCategory`.
  The node explicitly identifies this support condition with the cohomology-stalk
  condition, so the latter is not imposed as an additional hypothesis.
- The first conjunct is `IsZero ((lowerStar (ModuleCat A) h).rightDerivedFunctor.obj K.obj)
  ↔ IsZero K.obj`: precisely Rh_*K = 0 iff K = 0. IsZero is categorical vanishing,
  rather than equality to a particular chosen zero object.
- The second conjunct quantifies over every bounded L with exactly the same
  open-complement vanishing condition, and every morphism `f : K ⟶ L`.
  It states `IsIso (Rh_*.map f.hom) ↔ IsIso f`.
  The full bounded inclusion sends f to `f.hom`; full faithfulness identifies the
  two notions of invertibility. K was arbitrary to begin with, so this is
  reflection of isomorphisms on the entire supported bounded subcategory.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` and its closed-embedding property.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` is the unbounded module category;
  `DerivedCategory.Bounded` (Mathlib TStructure) is the recorded bounded subcategory.
  The former module was read using `scompile.py --source`, since the older
  slopmaster2 source tree does not contain that synchronized module.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` and `upperStar`; their derived constructions
  are exposed by `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.
  The current framework expresses the canonical derived direct image as
  `lowerStar.rightDerivedFunctor` (or `lowerStar.rightDerivedFunctorPlus` on D+).
  Its restriction to bounded source objects is the node's derived direct image;
  testing zero and invertibility after the full inclusion in D is equivalent to
  doing so in D+. No boundedness of Rh_*K is assumed.
- `def-weil-geometric-point` has the recorded inline field/morphism encoding,
  `IsAlgClosed` and `Scheme.SpecToEquivOfField`, whose signatures and docstrings
  were read. No geometric point binder is necessary when using the node's
  equivalent open-complement restriction condition. The geometric stalk test is
  retained in the proof plan and its proof dependency import.

All already stated proof-dependency modules are imported without `public`:
`Sheaf.AlgebraicGeometry.OpenClosedRecollement`
(`exists_functorial_distTriang_openClosed`),
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
(`ringedToposDerivedPushforwardComposition`),
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
(`Functor.exactFunctor_derivedFunctor`),
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
(`moduleSheaves_colimits_forgetful`),
`WeilConjectures.SixFunctors.Finite.Exact`
(`preservesFiniteColimits_lowerStar_of_isFinite`),
`WeilConjectures.SixFunctors.Finite.Stalk` (`lowerStarSheafFiberIsoPi`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
(`Scheme.isIso_of_isIso_sheafFiber_map`), and Mathlib derived `ExactFunctor`
(the `IsTriangulated` instance on `mapDerivedCategory`).
The theorem docstring includes all four steps of the node's proof with their DAG ids.

Source checked: the supplied Varshavsky PDF, §§3.2.2(I) and 3.2.4, including the
last paragraph of 3.2.4: the supported defect vanishes because its direct image
vanishes and its support is finite over the projection base. The current blueprint's
`lem-trf-local-term-locality.proof.md` was also read. This item is the general
sheaf-theoretic finite-support input, not a new assertion about the internal-Hom stalk.

Edge cases checked mathematically:

- K = 0 satisfies the support condition and both vanishing assertions.
- V empty makes the complement all of W, forcing K = 0; no nonempty support or
  nonempty geometric fibre is assumed.
- The finite composite may have empty fibres. Their stalk products are zero;
  for any point upstairs its own image fibre supplies the needed factor.
- A closed immersion with all of W as its image has empty open complement,
  so the support condition is automatic, and finite-pushforward conservativity
  is the resulting assertion. Nilpotent closed thickenings cause no extra assumption.
- The zero coefficient ring, the empty W or S, and cohomology concentrated in
  arbitrary degrees are allowed. No constructibility, properness of h, nonzero
  coefficient, characteristic, or invertibility hypothesis has been added.
- The cone of a map between bounded supported objects remains bounded and
  supported, giving the second conjunct with no extra condition on the map.

Searches for an existing exact statement (all msearch queries recorded by the wrapper):

- LeanFinder: "Derived etale direct image reflects zero objects and isomorphisms for
  bounded complexes supported on a closed subscheme finite over the base".
  Eight hits concerned étale morphisms and étale slice categories, not conservativity.
- Loogle: `CategoryTheory.Functor.ReflectsIsomorphisms, CategoryTheory.Limits.IsZero`.
  Zero hits; no geometric finite-support theorem.
- LeanSearch: "Derived pushforward is conservative on complexes supported on a finite
  closed subscheme". Eight hits were topological pushforward or structure-module
  pushforward declarations, not this theorem on étale coefficients.
- Mathlib grep: `finite.*(conservative|stalk)|support.*(pushforward|direct.image)`
  under AlgebraicGeometry. Ten hits concerned unrelated finite-type stalks and
  quasi-finite morphisms; none gives the assertion.
- `rg` of the project source and `lean/Sheaf` for finite-support conservativity,
  then for the chosen declaration name, found no exact statement. The broader
  support search found existing supporting results, including recollement,
  rather than a duplicate of this assertion.
- `grep -rn` of the item id in upstream WeilConjectures and `rg` in
  `dag/lean_names_upstream.json` found no attached declaration.

No mathematical defect was identified. Every variable and universe is explicit.
Validation uses only the required `scompile.py` per-file wrapper and `deliver2.py`.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
