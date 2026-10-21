## Worker report

The module `Sheaf.Algebra.Homology.RoosConeCalculus` states
`CategoryTheory.RoosConeCalculus.roos_cone_calculus`, with one `sorry`, and gives real
definitions of its component maps and clause predicates. There is no new Roos
object, functor, transition map, or augmentation. All are taken from
`Sheaf.CategoryTheory.StrictRoosModel`. The added statement dependency
`def-weil-strict-roos-model` is already landed and defines exactly the construction
that this node describes. This follows the maintainer's note in the node's stage-1
review. No statement correction and no new nodes are needed.

The source was read at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md`,
the Cones paragraph. It explicitly uses exact countable products on the pro-etale
site to compute strict Roos fibres and says that cones and canonical augmentations
commute. The node provides the expanded sign calculations. The theorem docstring
carries all eight proof steps, including those calculations and their DAG citations.

Hypotheses and clauses, in order:

* A scheme X is `(X : AlgebraicGeometry.Scheme.{t})`. The original small pro-etale
  site is `AlgebraicGeometry.Scheme.ProEt.topology X`; its category is Mathlib's
  `Scheme.ProEt`, with object universe t+1 and morphism universe t. No equality of
  these universes is imposed.
* The arbitrary, possibly noncommutative ring sheaf is
  `R : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)}`. Its module category is the
  dependency's `ringedSiteModules.{max u (t + 1)} R`. The arbitrary universe u
  allows larger coefficients; the common universe contains the site, as required
  for the sheaf/module and derived-category constructions. The sole derived-size
  datum is `[HasDerivedCategory.{w} ...]`, as in the recorded derived-category
  dependency. It is standard localization data, available in a sufficiently large
  universe, not a mathematical restriction on the ring or tower.
* A strict tower of complexes is encoded by
  `CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules ... R) ℤ`. The dependency's
  `HomologicalComplex.asFunctor` turns this into a tower of cochain complexes.
  These are equivalent presentations, with commuting differentials and transitions
  encoded in the functor-valued differential. Here n means the source's positive
  level n+1, so no positive level is lost. Strict maps are complex morphisms f;
  evaluation gives the strictly commuting levelwise maps.
* The actual termwise product is `roosP N`, the actual one-minus-transition map is
  `roosU N`, and H is `roosF`. The former two are existing public abbreviations for
  `∏ᶜ` and `towerTransitionEndomorphism`; the last is literally the shifted cone
  functor. There is no existence hypothesis on products in the theorem: the
  module-sheaf product instance supplies them.
* The reordered coordinates H^q = P^q ⊕ P^(q-1) are the existing `roosχ` followed
  by biproduct braiding and reindexing. The public helper `v` is the actual
  `roosProj` in degree q and `ucoord` is `mappingCocone.snd` in degrees q,p with
  q-1=p. These are the two projections of precisely that canonical isomorphism.
  `CoordinateCalculus` states separately that d followed by v is vd and d followed
  by u is `-ud - v s`, hence exactly `(dv,-du-sv)`. It also states both diagonal
  map equations with the existing `roosPmap`. The first conjunct of the theorem
  is `roosF.Additive`, asserting the additive-functor clause.
* The next conjunct quantifies over every strict f, assumes only
  `∀ n, QuasiIso ((complexOfFunctorsToFunctorToComplex.map f).app (op n))`, and
  concludes `QuasiIso (roosF.map f)`. It imposes no boundedness, surjectivity,
  Mittag-Leffler, or extra convergence hypothesis.
* `DerivedRoos N` asserts that the actual product cone of N, mapped by Q with
  its actual projections, is limiting, and that the localized
  `mappingCocone.triangle (roosU N)` is distinguished. Its first map is precisely
  Q of v, its second is Q of s, and its last is the actual cocone boundary with
  Q's shift comparison. This records the specified localized Roos triangle,
  rather than merely an abstract isomorphism of objects. The final clause is
  `IsDerivedLimit` for the evaluated localized tower. It holds for every choice
  of `HasProduct` for that family, by the unique projection-preserving product
  isomorphism. The preceding limiting-cone assertion guarantees existence, so
  this universal product-choice clause is not a vacuous substitute for existence.
* The theorem supplies one coherent comparison `cs : roosF.CommShift ℤ` and one
  family `e f : H(Cone f) ≅ Cone(H f)`. A `CommShift` includes its zero and
  addition coherence and its isomorphisms are natural. `ShiftFormula cs`
  specifies both coordinates after the canonical degree reindexing and the
  actual product projections: coefficient 1 on v, coefficient `r.negOnePow`
  on u. Thus it is exactly `(v,u) ↦ (v,(-1)^r u)`, including negative r.
  The existing `RoosShift.commShift` and signed formula from
  `lem-weil-roos-comm-shift` are imported as the proof tool for this comparison;
  the theorem asserts joint compatibility on the existing `roosF`, rather than
  defining another shift or Roos model.
* `ConeFormula f (e f)` gives four equations after the actual cone and product
  projections. In its output order they read b=b, b'=b', a=a, c=-a'. They
  uniquely determine `(b,a,b',a') ↦ (b,b',a,-a')` and the isomorphism field gives
  an inverse chain map. `ConeCompatibility` quantifies over every strictly
  commuting square and requires the associated cone map naturality equation.
  Its last two equations require preservation of `mappingCone.inr` and of
  `mappingCone.triangle f |>.mor₃` after `cs` at shift 1. Mathlib's latter
  boundary is the node's -p; no boundary sign has been omitted.
* Any compatible j_n:M→N_n is exactly a cone j over `N.asFunctor`.
  `augmentation j` is an abbreviation for the dependency's `roosAugment` with
  these component maps. Its compatibility proof is literally `j.w`.
  `CoordinateCalculus` requires v of this map to be the product lift of j_n
  and u to be zero. The witness `hnat : AugmentationNaturality ...` requires
  `augmentation j ≫ H(f) = g ≫ augmentation j'` for each levelwise augmented
  strict square, not just a chosen or nonempty natural map.
* `ConeAugmentation e hnat` requires the augmentation on a tower of cones to
  become the induced mapping-cone map of the two augmentations. Its premise
  explicitly identifies the two levelwise cone coordinates with those induced
  by j and j'. The extra variable c permits a supplied identification of its
  source with the chosen augmented cone; c=identity is the literal canonical
  augmentation case. It asserts the composite equality for every such c, so
  the canonical case is included and no choice of cone completion is made.
* `ShiftAugmentation cs` quantifies over a shifted levelwise augmentation and
  a source comparison c, specifies exactly that its first coordinate is the
  induced shifted j_n, and requires the chain-map identity with `cs`. In
  particular c=identity and the actual shifted source give the shifted
  augmentation in the node. The zero second coordinate is supplied by the
  earlier augmentation formula, so the sign multiplies zero as required.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the exact Mathlib `SheafOfModules` and its abelian structure.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, its shift and triangle interfaces.
* `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`,
  `NatTrans.ofOpSequence`, supplying the strict tower interpretation; objects
  here are the full functors they construct, rather than another tower type.
* `Mathlib.CategoryTheory.Limits.Shapes.Products`: `piObj`, `Pi.π`, `Pi.lift`,
  `Pi.map`; countable products from `Limits.Shapes.Countable`.
* `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit` and `IsDerivedLimitTriangle`; the actual
  localized triangle is additionally asserted, stronger than forgetting its maps.
* `Sheaf.CategoryTheory.StrictRoosModel`: `roosP`, `roosU`, `roosPmap`, `roosF`,
  `roosχ`, `roosProj`, `roosAugment`; its full definitions, signatures and
  coordinate lemmas were read. This landed dependency is added to stmt_deps.
* `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`: `ProEt.products_derived`.
  Its signature, proof and docstring identify the actual localized product cone
  and arbitrary products of quasi-isomorphisms.
* `Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso`:
  `CochainComplex.quasiIso_of_roos_coordinates`, with arbitrary endomorphisms;
  its full coordinate and diagonal-map hypotheses were read.
* `Sheaf.Algebra.Homology.RoosCommShift`: `RoosShift.commShift`,
  `commShift_inl`, `commShift_inr`, `ConeFormula`, and `chain_shift`, read in full.
  This is a proof import used to transport the existing signed coherent shift to
  the complex-of-towers presentation and enforce its cone compatibility.
* `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated` and
  inverse rotation, imported by the recorded derived-limit module.
* Publicly importing `ProEtaleSurjectiveTowerDerivedLimit` exposes its already
  defined `surjectiveTower_hasSheafify` and
  `surjectiveTower_wEqualsLocallyBijective` instances in the exact coefficient
  universes. These are inherited infrastructure, not additional hypotheses.

Edge cases checked before and during the coordinate reading: the zero tower and
zero source augmentation give zero in every coordinate; a constant tower retains
1-T rather than incorrectly setting it to zero; f=0 and f=identity have the
specified negative fourth component; r=0 gives the identity comparison, r=1 and
r=-1 give the same negative sign on u, and r+s has the product of signs.
The source permits unbounded complexes and arbitrary transition maps, both
retained. An empty scheme and the zero ring are permitted; no nonempty or
nontrivial hypothesis occurs. The index set is the required infinite countable
positive tower, reindexed by ℕ, not an arbitrary possibly empty family.
There are no disputed statements or known node faults.

Searches for an exact existing statement:

* msearch leanfinder, query "Strict Roos fibre functor on towers of cochain
  complexes preserves mapping cones and augmentations": eight hits including
  `mappingCone.map_δ`, `mapHomologicalComplexXIso`, and spectral-object cone
  functors. These concern a functor applied degreewise to an ordinary complex,
  not the Roos double-cone formula and augmentations together.
* msearch loogle, query `"mappingCone", "map"`: twelve cone constructors,
  projections and cochain formulas; no strict Roos calculus theorem.
* msearch grep, query `roos|Roos`, subdirectory `Algebra/Homology`: zero Mathlib
  hits.
* msearch leansearch, query "Homotopy inverse limit Roos fibre preserves mapping
  cones shifts and quasi-isomorphisms": eight hits on ordinary cone shifts,
  localization and additive-functor cone comparisons; no complete statement.
* rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `roos|Roos|lem-pe-roos-cone-calculus`, followed by
  `roosF|roosConeCalculus|roos_cone_calculus|ConeFormula` in the homology and
  category-theory directories: found the strict model and the coherent shift
  dependency above, plus other derived/normalization Roos statements. They do
  not assert the four-coordinate double-cone comparison or the full natural
  cone/augmentation compatibility. The upstream search for this node id gave
  no match. The complete predicate name and theorem name are new.

Validation: scompile.py compiled this delivered file in sandbox and library
positions, cleanly, in 13.5 s and 14.4 s. All definitions have concrete data;
the sole postponed result is the named theorem for this DAG node. All variables
and universes are explicitly bound. No global build or live-file edit was run.

## Second reading by N7

The dispatcher assigned one worker and explicitly forbade starting other agents.
This section records a second reading by the same worker, not a claim of an
independent reviewer; the maintainer's independent delivery review remains due.

I reopened the node and the completed Lean file and checked each clause against
the predicates described above. The initial elaboration exposed a definitional
transparency mismatch between `roosF.obj N` and `mappingCocone (roosU N)`;
I gave ucoord an explicit existing-fibre domain and used the existing library
transparency options. I also exposed the existing sheafification instances in
public imports and made the localized product family explicit. These changes
alter no mathematical hypotheses or clauses. A final pass checked all four cone
projection targets and the last minus sign, the boundary equality with the same
coherent cs, the two differential equations, and that augmentations use the
existing `roosAugment`. I checked that existence of the localized product is
asserted before quantifying over choices of that product, that no unbounded or
negative-shift case is discarded, and that the cone/shift augmentation predicates
include the literal induced cases with c=identity. No mathematical mismatch was
found and no source statement correction was made.
