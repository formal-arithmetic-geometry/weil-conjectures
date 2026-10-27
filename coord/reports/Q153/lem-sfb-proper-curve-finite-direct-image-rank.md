## Worker report

The module `Sheaf.AlgebraicGeometry.ProperCurveFiniteDirectImageRank` states
`AlgebraicGeometry.proper_curve_finite_direct_image_rank` with one expected `sorry`.
There are no new definitions, dependency repairs, statement corrections, or other
postponed theorems. Only the item's `lean` field changes.

Source read: Stacks varieties.tex, lemma-degree-pullback-map-proper-curves,
Tag 0AYZ, especially its opening proof paragraph identifying the coherent structure
direct image's rank with the degree. The item's accepted seven-step proof is
included in the theorem docstring, with the same supporting node references.

Hypotheses, in order:

- `{k : Type u} [Field k]` gives the arbitrary base field.
- `{X Y : Scheme.{u}}`, `sX` and `sY` give the two schemes with their structure
  morphisms to `Spec (CommRingCat.of k)`.
- `[IsIntegralCurve sX] [IsIntegralCurve sY]` uses the recorded curve notion:
  both schemes are integral, separated and finite type over k, of dimension one.
  The class uses topological dimension; `Scheme.dim_eq_topologicalKrullDim`
  identifies it with the local-ring dimension used in the DAG discussion.
- `[IsProper sX] [IsProper sY]` gives properness over k.
- `(f : X ⟶ Y) (hf : f ≫ sY = sX)` states exactly that f is a k-morphism.
- `[IsDominant f]` is density of its image.
- The explicit `Module.Finite` instance uses
  `(Scheme.Hom.dominantFunctionFieldAlgebra f).toModule`. Thus the finite
  extension hypothesis concerns precisely the generic stalk pullback algebra,
  rather than an arbitrary field embedding. The right side of the rank equality
  explicitly uses the same module instance.

Conclusion, clause by clause:

- `IsNoetherian X ∧ IsNoetherian Y`: Mathlib's class extends both
  `IsLocallyNoetherian` and `CompactSpace`, precisely the required meaning.
- `IsFinite f ∧ IsAffineHom f`: finite and affine, both explicitly included.
- `RingedSpace.IsCoherent X.toRingedSpace (SheafOfModules.unit X.ringCatSheaf)`
  and its Y version: coherence of both structure modules.
- The third coherence assertion applies that identical predicate to
  `(Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)`.
  Mathlib's pushforward is `SheafOfModules.pushforward f.toRingCatSheafHom`:
  its sections are the sections on the inverse image, and its scalar action is
  restriction along the actual structure-sheaf map of f.
- `genericPoint Y` is the canonical generic point of the integral scheme Y.
  Applying `RingedSpace.moduleStalkFunctor Y.toRingedSpace (genericPoint Y)`
  to this direct image gives the actual module stalk over `Y.functionField`,
  definitionally the structure-sheaf stalk at that point.
- The equality of `Module.rank` values is exactly
  `dim_{k(Y)} F_eta = dim_{k(Y)} k(X) = d`. The right-hand dimension is finite
  by the hypothesis. Cardinal-valued rank expresses this without the convention
  that natural-valued finrank is zero for an infinite-dimensional vector space.
  It implies finite dimension of the left side as part of the equality, rather
  than assuming that dimension is finite. In the finite case it is the degree
  recorded by `FieldExtension.degree`, whose finite branch is `Module.finrank`.
- No smoothness, normality, flatness or separability hypothesis occurs.

Recorded dependency declarations read and used:

- `Field`: Mathlib.Algebra.Field.Defs, through the imported field/scheme modules.
- `IsIntegralCurve`, `IsVariety`:
  WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective.
- `IsProper` (and its separated/universally closed parent classes):
  Mathlib.AlgebraicGeometry.Morphisms.Proper.
- `Scheme.functionField` and its field instance:
  Mathlib.AlgebraicGeometry.FunctionField, publicly exposed by the recorded
  WeilConjectures.AlgebraicGeometry.FunctionField module. This is the dependency
  node's explicit arbitrary-integral-scheme clause, not its component-product
  construction for general curves.
- `Scheme.Hom.dominantFunctionFieldAlgebra`:
  Sheaf.TraceFormula.LocalDimensionFormula. Read its construction from
  `Scheme.Hom.functionFieldMap` in
  WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback: dominance identifies
  generic points, then the definition uses the actual stalk map.
- `FieldExtension.degree`: Sheaf.FieldTheory.FieldTower. Finite extension is
  Mathlib's `Module.Finite`; vector-space dimension is `Module.rank`.
- `IsGenericPoint`, `genericPoint`, `genericPoint_spec`: Mathlib.Topology.Sober.
- `Scheme.Modules.pushforward`: Mathlib.AlgebraicGeometry.Modules.Sheaf,
  exposed through Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction,
  the recorded module of def-pc-module-pullback. Its pullback adjunction is
  unnecessary for this direct-image statement.
- `IsLocallyNoetherian`, `IsNoetherian`: Mathlib.AlgebraicGeometry.Noetherian;
  `CompactSpace`: Mathlib.Topology.Defs.Filter.
- `IsFinite`, `IsAffineHom`: Mathlib.AlgebraicGeometry.Morphisms.Finite
  and its affine-morphism import.
- `RingedSpace.IsCoherent`: WeilConjectures.AlgebraicGeometry.Coherent,
  publicly imported by the recorded Sheaf.AlgebraicGeometry.CoherentFiniteType.
  The exact finite-type-kernel predicate is used, rather than the latter
  module's quasi-coherent/finite-type conjunction.
- `PresheafOfModules.moduleStalkFunctor` and `stalkObj`:
  WeilConjectures.Topology.PresheafModuleStalkFunctor. For the sheaf on the
  scheme, the dependency record directs consumers to
  `RingedSpace.moduleStalkFunctor`, read in
  WeilConjectures.Algebra.Homology.ModuleStalkFunctor. Both use the same
  Mathlib stalk carrier and action. No new stalk construction is introduced.

The stated proof dependencies are also imported (without public): the dimension
comparison, locally Noetherian coherence criterion, finite-pushforward coherence,
affine-pushforward stalk localization, finite-algebra integrality and integral
localization fraction comparison. The proper-over-separated and finite-type
Noetherian facts are Mathlib declarations already exposed by their statement
imports. The noncontraction finiteness node has no recorded Lean module to import.

Edge cases checked before writing: the identity of a proper integral curve has
field degree and generic rank one; inseparable Frobenius retains its full
inseparable degree; normalization of an integral singular proper curve has
rank one, with no normality of the target or flatness of the morphism imposed.
Integral dimension-one hypotheses exclude empty and zero-dimensional schemes;
a constant map is excluded by dominance onto a dimension-one target.
No restriction on characteristic or on the arbitrary universe u is imposed.

Searches run using msearch.py for this item (also recorded in searches.jsonl):

- leanfinder: `A dominant map between proper integral curves is finite and the
  pushforward structure sheaf is coherent with generic rank equal to function
  field degree`. Eight hits, including IsFinite, IsDominant and
  finite_appTop_of_universallyClosed; none states this theorem.
- loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsDominant`.
  Zero hits.
- grep: `(genericRank|generic.rank|finrank).*(pushforward|direct.image)|(pushforward|direct.image).*(genericRank|generic.rank|finrank)`.
  Two hits about submodule pushforwards in linear algebra, not sheaf direct image.
- rg on lean/WeilConjectures and lean/Sheaf for the node id, proposed name and
  finrank/pushforward combinations: coherent cohomology finrank statements only.
  The source `Hom.finrank_genericPoint_eq_finrank_functionField` additionally
  assumes finite flat and concerns fiber degree; it does not state this result.
- grep -rn for the exact node id in lean/WeilConjectures: no matches.

Server validation: scompile.py compiled the file both under its sandbox name
and its final library module name, cleanly (2.1 s and 2.8 s). Every variable
and universe is explicit; autoImplicit and relaxedAutoImplicit are disabled.

## Second reading by Q153

I reread the node and completed signature against the source and the dependency
interfaces. This is a worker self-check; the maintainer's independent review is
still required, as specified in the dispatcher brief (no additional agents).
The conjunction includes both Noetherian schemes, finite and affine f, all three
coherence statements and the generic rank equality. The k-morphism compatibility
and properness of both structure maps are present. The finite-field-extension
instance and right-hand dimension share the canonical dominant stalk algebra.
The left side is the actual sheaf-module stalk with its inherited action.
The choice of cardinal-valued rank preserves the finite dimension assertion.
No mismatch requiring a node correction or dependency repair was found.
