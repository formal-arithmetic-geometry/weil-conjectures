## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectSums` states
`AlgebraicGeometry.Etale.derivedDirectImage_and_globalSections_preserveCoproducts`, with a
single postponed proof and no new definitions. Its two conjuncts are precisely assertions
(1) and (2) of Stacks Project Tag 0F11. I read that source at
https://stacks.math.columbia.edu/tag/0F11; the local literature checkout contains only the
citation indices, so the original blueprint path was unavailable locally.

Hypothesis and conclusion correspondence:

- `n : ℕ` and `hn : 1 ≤ n` render the integer coefficient modulus `n ≥ 1`.
  `ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))` is the category of modules over the canonical universe lift of `Z/nZ`.
  Mathlib’s `ULift.ringEquiv : ULift (ZMod n) ≃+* ZMod n` identifies the coefficients
  exactly; this changes no mathematical coefficient ring or module sheaf.
- In clause (1), `{X Y : Scheme.{u}} (f : X ⟶ Y)` is an arbitrary morphism of schemes;
  `[QuasiCompact f] [QuasiSeparated f]` are exactly the two morphism hypotheses.
  `f.torsionEtaleCohomologicalDimension < ⊤` renders `kuncd(f) < infinity` using the
  dependency's numerical torsion dimension, not a replacement coefficient-specific bound.
- Clause (1)'s functor is the existing unbounded
  `rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) f`, from the ordinary derived
  category of module-valued sheaves on `X.smallEtaleTopology` to that on `Y`.
  `∀ I : Type w, PreservesColimitsOfShape (Discrete I) ...` says it preserves every
  set-indexed coproduct, with the canonical image of its coprojections. The definition
  of preservation sends every colimiting cocone to a colimiting cocone, so it identifies
  the canonical comparison and asserts more than an abstract objectwise isomorphism.
- In clause (2), `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]` is exactly
  a qcqs scheme, and `X.torsionEtaleCohomologicalDimension < ⊤` is its finite torsion
  étale cohomological dimension. This clause binds its own scheme and is independent of
  the morphism quantified in clause (1), as in Tag 0F11.
- Clause (2)'s functor is the existing unbounded
  `rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) X`, whose target is
  `DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))`. The same discrete-colimit preservation
  assertion renders commuting with all set-indexed direct sums. Neither clause restricts
  the family to bounded, constructible, or uniformly bounded-below complexes.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` has a convention-only record and defines no extra
  notion. I use Mathlib's `Scheme`, `QuasiCompact`, `QuasiSeparated`, `CompactSpace`,
  and `QuasiSeparatedSpace`; the morphism class source signatures and docstrings were read.
- `def-kun-cd`: `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`,
  `AlgebraicGeometry.Scheme.torsionEtaleCohomologicalDimension` and
  `AlgebraicGeometry.Scheme.Hom.torsionEtaleCohomologicalDimension`. I read their full
  definitions: infima in `ℕ∞` of nonnegative torsion-sheaf vanishing bounds. The morphism
  definition uses the bounded-below abelian direct image on sheaves in degree zero.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories` and
  the source `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` identify the coefficient
  categories as `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ))`.
  I read their full definitions and docstrings. This is the existing module-valued
  encoding of the constant-ring module category, not a second SheafOfModules encoding.
- `def-weil-pbc-direct-image`: the recorded
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` supplies `Etale.lowerStar`.
  Its unbounded and bounded-below derived versions are respectively
  `Etale.rightDerivedLowerStar` and `Etale.rightDerivedLowerStarPlus`, in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; I read their
  definitions and imported that module directly. The unbounded functor is the generic
  `Functor.rightDerivedFunctor` of the same recorded ordinary direct image.
- `def-weil-pbc-global-sections-functor` is a Mathlib node: its match is
  `CategoryTheory.Sheaf.Γ`, in `Mathlib.CategoryTheory.Sites.GlobalSections`. I read it,
  its terminal-object instance and its sections comparison. The source declaration
  `Etale.rightDerivedGlobalSections`, in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, is the right derived functor
  of exactly this `Sheaf.Γ`; its full signature and docstring were read.
- `lem-kun-finite-cd-acyclic-complex`:
  `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`,
  `CategoryTheory.Functor.exists_rightDerived_computes_acyclic_of_finite_dimension`.
  Its full signature and seven-step docstring were read; it supplies the natural total
  derived comparison on arbitrary complexes of acyclic terms, with no boundedness.
- `lem-kun-grothendieck-derived-coproducts`:
  `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`,
  `DerivedCategory.isColimit_mapCocone_grothendieckSum`. The recorded module was absent in
  the older local checkout; `scompile.py --source` returned the live source, which I read
  in full. I import the recorded live wrapper, rather than relying on the older local
  original module’s signature or compiled export. It uses the actual termwise coproduct
  cocone and localizes its legs. No dependency interface is repaired or copied.

Every stated proof dependency is imported as part of the proof plan. The declaration's
six numbered paragraphs follow the node's six proof steps, naming the coefficient
comparison, filtered-colimit, module-colimit, Grothendieck, injective-resolution,
unbounded acyclic-complex, and module-derived-coproduct nodes at the steps where used.

Edge cases checked before finalizing the signature: `n = 1` is retained (the zero ring
and zero module category), while `n = 0` is excluded exactly by `hn`. Empty and singleton
index types are retained by unrestricted `I`; the empty coproduct is zero and the
singleton comparison is the identity. The empty scheme and zero complexes are retained.
There is no nonzero-ring, invertibility-of-n, properness, finite-type, or field hypothesis.
Clause (1) does not require X or Y separately to be qcqs. The index universe `w` is
explicit and independent: preservation is stated for every discrete shape in that chosen
indexing universe, without an added smallness hypothesis or equality to the scheme
universe. Site objects have universe `u+1` and coefficient modules have universe `u+1`,
following the recorded derived-category and six-functor conventions.

Searches for existing statements:

- `msearch.py ... leansearch`: query “The unbounded derived pushforward and derived global
  sections of etale Z/n module sheaves commute with arbitrary direct sums when torsion
  cohomological dimension is finite”; service unavailable, Internal Server Error.
- `msearch.py ... leanfinder`: query “Derived direct image and derived global sections of
  etale Z/n module sheaves preserve arbitrary coproducts under finite torsion cohomological
  dimension”; eight hits about condensed/light-condensed abelian categories, AB4/AB5 and
  locally constant modules, with no matching theorem.
- `msearch.py ... loogle`: query `"PreservesColimitsOfShape", "rightDerived"`; zero hits.
- `msearch.py ... grep`: query
  `cohomologicalDimension|finiteCohomological|[Dd]erived.*[Cc]oproduct|[Cc]oproduct.*[Dd]erived`
  in `Algebra/Homology`; zero hits. The broader query
  `etale.*[Cc]oproduct|[Cc]oproduct.*etale|cohomologicalDimension|finiteCohomological`
  also returned zero hits.
- `rg` by `lem-kun-0f11`, dimension and derived-coproduct vocabulary in both source trees
  and `lean/Sheaf` found the related existing
  `rightDerivedLowerStar_preservesCoproducts_of_finite_dimension`, which has only clause
  (1), a finite arbitrary coefficient ring, and an explicit coefficient-module vanishing
  bound. It does not state this item.
- The current shared upstream tree also contains
  `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts` and its theorems
  `preservesCoproducts_rightDerivedLowerStar` and
  `preservesCoproducts_rightDerivedGlobalSections`. I read both full signatures and the
  definitions of `HasFiniteCohomologicalDimension` and
  `HasFiniteCohomologicalDimensionMorphism`. Those assume coefficient-specific finite
  dimension for an arbitrary ring and index only in `u+1`; they do not state the node's
  numerical torsion-CD hypotheses and general chosen indexing universe. They are useful
  proof tools, but are not exact existing declarations of this item. No notion is
  redefined here; the new theorem only states the exact source hypotheses and conclusions.
- Searching the chosen full declaration name in Mathlib, both source trees, the project's
  modules and the upstream name index found no existing declaration of that name.

No statement correction, new node, dependency module or disputed statement is needed.


Universe diagnosis: the first elaboration with the small type `ZMod n` failed to infer
`IsGrothendieckAbelian.{u+1} (ModuleCat.{u+1} (ZMod n))`, since the supplied module-category
instance uses a ring in the same universe as its module carriers. The final signature
uses `ULift.{u+1} (ZMod n)` and Mathlib’s existing ring structure and `ULift.ringEquiv`.
This supplies the ordinary coefficient lift required by the recorded six-functor API;
no scheme universe, index universe, vanishing bound, or other hypothesis is restricted.
Both clause functors therefore have exactly the established `Λ : Type (u+1)` form.

Validation: `scompile.py NO lem-kun-0f11` compiled the final module cleanly through the
side overlay, both as a sandbox file and at its library module path, with no errors or
warnings. The compiler options disable auto implicits;
all universe and object variables are explicitly bound. No proof other than `sorry`
occurs in the module. The item’s node copy changes only `lean`.


## Second reading by NO

I reread the node copy, its Stacks source (Tag 0F11 / Lemma 59.96.3), the recorded
dependency signatures, and the delivered module. The node introduces the integer
`n ≥ 1`; an arbitrary scheme morphism `f : X ⟶ Y` with quasi-compact and
quasi-separated hypotheses and finite torsion étale cohomological dimension; and,
independently for clause (2), a qcqs scheme `X` with finite torsion étale
cohomological dimension. Clause (1) concludes that the unbounded étale derived
direct image `Rf_*` on `Z/nZ`-module sheaves preserves set-indexed direct sums.
Clause (2) concludes the same for unbounded derived global sections
`RΓ(X, -)` with target `D(Z/nZ)`.

The Lean rendering is item-by-item: `(n : ℕ) (hn : 1 ≤ n)` is the coefficient
hypothesis; `{X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]`
is the arbitrary morphism and exactly its two morphism hypotheses;
`f.torsionEtaleCohomologicalDimension < ⊤` is the finite torsion-CD hypothesis;
and `∀ I : Type w, PreservesColimitsOfShape (Discrete I)
(rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) f)` is
clause (1)'s preservation of every set-indexed coproduct. The second conjunct
binds `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]`, exactly the
qcqs scheme condition, repeats the finite torsion-CD hypothesis for this
independent `X`, and uses
`rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) X`
with the same unrestricted discrete-index preservation conclusion. `PreservesColimitsOfShape
(Discrete I)` is the canonical categorical formulation of commuting with the
node's direct sums, including the coprojection comparison. The theorem is
universe-polymorphic in `w`, so it covers set-indexes in every universe.

I checked the recorded declarations for `Scheme`, `QuasiCompact`,
`QuasiSeparated`, `CompactSpace`, `QuasiSeparatedSpace`, the torsion-CD
definitions, the module-valued derived categories, `rightDerivedLowerStar`, and
`rightDerivedGlobalSections`; each is the notion used by the node. The global
sections dependency is Mathlib's `CategoryTheory.Sheaf.Γ`, with the small étale
site's terminal object. The two homological-algebra dependencies state the
finite-CD unbounded acyclic-complex computation and the Grothendieck derived
coproduct construction used by the proof. No dependency module is unusable, so
no private copy, new node, or dependency repair was needed.

Edge cases are retained: `n = 1` gives the zero coefficient ring and is allowed;
`n = 0` is excluded exactly by `hn`; empty and singleton index types are allowed
(the empty coproduct is zero and the singleton comparison is the identity); zero
complexes and the empty scheme are not excluded; no nonzero-ring, field,
properness, finite-type, constructibility, or boundedness hypothesis was added.
The characteristic is handled by the torsion-CD hypothesis exactly as in the
source.

For one-definition-per-notion checks I searched the project and source trees with
`rg` for the node name and for derived étale coproduct terminology, inspected the
existing finite-CD direct-image and Künneth/Coproducts modules, and ran
`msearch.py` LeanSearch, LeanFinder, Loogle, and grep searches recorded in
`searches.jsonl`. The existing Künneth declarations require a coefficient-specific
finite-CD predicate and a fixed `u + 1` index universe, so they are not this
node's exact statement. No exact declaration exists in Mathlib, the source tree,
or the project.

I found no mismatch and made no semantic change. The worker's `ULift.{u + 1}
(ZMod n)` coefficient is necessary to inhabit the established
`ModuleCat.{u + 1} Λ` interfaces; it is canonically equivalent to `ZMod n` and
does not alter the mathematical coefficient ring. The node copy's only change from
the base node is its `lean` record, whose statement is verbatim the theorem
signature.
