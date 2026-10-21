## Worker report

The delivery states `AlgebraicGeometry.ProEtale.PrincipalReduction.principal_reduction_cone_calculus`
in `Sheaf.Paper.PrincipalReductionConeCalculus`. The sole theorem has proof `sorry`.
The four auxiliary declarations contain actual terms: the standard cone coordinates, the signed
four-summand permutation, an abbreviation of the dependency's scalar chain map, and an abbreviation
of the canonical derived extension followed by exact scalar restriction. No mathematical node,
dependency interface or informal statement is changed.

I read the item's statement and ten proof steps; all three statement-dependency nodes and the
signatures/docstrings recorded below; the current blueprint first-reduction proof (Cones paragraph);
and Stacks `derived.tex`, `definition-cone` (Tag 014E), lines 2470–2489. The boundary in this delivery
is the negative projection specified by `def-weil-abstract-derived-category` and Mathlib's
`mappingCone.triangle`, rather than the positive projection appearing in Stacks' elementary cone
triangle. The module docstring carries all ten proof steps with their DAG inputs.

Hypotheses and ambient objects:

| Node hypothesis/object | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite E/Q_l | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Valuation ring and chosen uniformizer pi | The dependency's `DerivedNakayama.integerRing l E` and `Padic.coefficientExtensionUniformizer l E`. The coefficient-extension definition chooses one uniformizer; this is the same choice used in `AdicCompletion`'s actual quotient rings and transitions. The theorem supplies `d` and pins its action at every profinite test object, every continuous function and every point to multiplication by that uniformizer. It does not assume an unspecified endomorphism. |
| Arbitrary scheme X | `(X : Scheme.{u})`, with no geometric hypotheses |
| R = p_X^* underline(O_E) | Exactly `AdicCompletion.Modules l E X`, internal modules over `AdicCompletion.ring l E X`, whose underlying ring is `condensedRingObj (DerivedNakayama.integerRing l E) X` |
| Unbounded cochain complexes | `CochainComplex (Modules l E X) ℤ`, with no boundedness or flatness assumption |
| D(R), localization, shift, cone | `DerivedCategory`, `DerivedCategory.Q`, Mathlib integer shifts, and `CochainComplex.mappingCone` from the recorded derived-category dependency |
| All positive n | The Lean index `n : ℕ` denotes mathematical level n+1, exactly as in `AdicCompletion`; this is a bijective reindexing of the positive levels. |

Every clause is rendered as follows, in the order of the theorem's conjuncts:

1. `D` is a family of endofunctors on complexes; `hobj n M` fixes its objects to the actual
   `mappingCone (scalar l E X d n M)`. The scalar abbreviation is exactly
   `DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M`.
2. The first conjunct fixes `χ` to transport along `hobj` followed by
   `principalConeCoordinates`, which is Mathlib's `homotopyCofiber.XIsoBiprod` followed by
   `biprod.braiding`. Hence the coordinates are the specified `(M^q,M^(q+1))`, including
   the differential `(dx+pi^(n+1)y,-dy)`, rather than freely chosen biproduct coordinates.
3. The next conjunct fixes `(D n).map g` degreewise, under those coordinates, to
   `biprod.map (g.f q) (g.f (q + 1))`. Functoriality and naturality of `T` and `j` are
   included in their types as functors and natural transformations.
4. `T n : D (n+1) ⟶ D n` has the component formula `biprod.map (𝟙 _) (pi.f (q+1))`,
   using the same dependency scalar chain map for pi. This is exactly `(x,pi y)`.
5. `j n : 𝟭 _ ⟶ D n` has component `biprod.inl`, exactly `(m,0)`. The next equation is
   `j_(n+1) ≫ T_n = j_n`.
6. `QuasiIso g → QuasiIso ((D n).map g)` states quasi-isomorphism preservation for every
   chain map, without requiring scalar multiplication on its terms to be injective.
7. The target of `κ n` is precisely `DerivedCategory.Q ⋙ reductionFunctor l E X n`, where
   that functor abbreviates `AdicCompletion.derivedReduction ... n ⋙ AdicCompletion.restrict ... n`.
   Thus its value is the dependency's actual `integralLevel (Q M) n`, not a supplied arbitrary
   derived tensor model. Each `κ n` is a natural isomorphism on all complexes. The theorem
   supplies a coherent `sF n : reductionFunctor ... n |>.CommShift ℤ`, states `.Additive`, and
   states `Functor.IsTriangulated` with exactly that structure passed explicitly. This supplies
   an additive exact derived endofunctor; shift structures are conclusions, not extra hypotheses.
8. `Q(T_n(M)) ≫ κ_n(M) = κ_(n+1)(M) ≫ integralStep (Q M) n` identifies the transitions with
   the dependency's canonical derived transitions, after the specified integral restriction.
9. `Q(j_n(M)) ≫ κ_n(M)` equals the actual unit of
   `Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)` at `Q M`. This is
   the canonical reduction map, with its normalization fixed, not just an isomorphism of objects.
10. `Φ n f` is a chain isomorphism from `D_n(Cone f)` to `Cone(D_n(f))`. Its degreewise equation,
    after canonical cone coordinates on both sides, is `principalConeInterchange`.
    That helper is the literal biproduct morphism with components `(b,b',a,-a')`.
    The final A-coordinate is written `A.X (q + 1 + 1)`, exactly A^(q+2).
11. `sD n : (D n).CommShift ℤ` supplies a coherent family of natural shift isomorphisms.
    Its displayed degreewise formula uses `r.negOnePow` only on the second coordinate,
    plus the standard `shiftFunctorObjXIso` reindexing. It is exactly `(x,(-1)^r y)`
    for every integer r, including negative integers. Coherence at zero and under addition
    is part of the `CommShift` structure.
12. The square with maps `a,b`, commutativity proof `h`, and its image commutativity proof `h'`
    states naturality of `Φ` under every chain-map square. The two proof arguments merely type
    the standard cone maps: `h'` follows by applying the functor to `h`; they place no additional
    condition on the square. Shift naturality is already part of the natural-isomorphism type
    supplied by `sD`.
13. The next two squares state commutation of `Φ` and the shift comparison with each adjacent
    `T n`. All tower arrows are composites of these, so this is compatibility with every
    tower transition, with no extra independently chosen longer arrows.
14. The cone-inclusion equation is `D_n(inr f) ≫ Φ_n(f) = inr(D_n(f))`.
15. The boundary equation uses `(mappingCone.triangle f).mor₃`, exactly the negative projection,
    followed by the `sD n` comparison for shift 1. Its other side is `Φ_n(f)` followed by
    `(mappingCone.triangle (D_n(f))).mor₃`. It therefore retains the required shift and sign.
16. The cone-coaugmentation equation identifies `j_(Cone f) ≫ Φ_n(f)` with the standard
    `mappingCone.map` on `(j_A,j_B)`, using `j`'s naturality square. The shift-coaugmentation
    equation identifies `j_(M[r])` followed by the shift comparison with `j_M[r]`.
17. The last equation says that `κ` also identifies the strict shift comparison with the
    supplied exact shift structure on the canonical derived functor, using Q's actual
    `commShiftIso`. This makes the localized exactness statement use the very signed
    comparisons displayed above.

Dependency declarations reused (the recorded source and docstrings were read):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and the strong monoidal
  `upperStarFromPoint`. These are the recorded pulled-back coefficient construction.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` and its shift structure. The module uses the existing derived-category
  instance of the internal-module framework, without choosing another abelian or localized category.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`:
  `AdicCompletion.Modules`, `derivedReduction`, `restrict`, `integralStep`, and `quotient`.
  These are exactly the positive-level derived reductions, canonical transitions and units.
- `Sheaf.Paper.DerivedNakayamaResolution`: `DerivedNakayama.integerRing`, `scalarOnComplex`,
  `scalarOnModules` and the two-term resolution statement. The scalar construction is reused.
- `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`:
  `CochainComplex.mappingCone.map`, `inr`, `triangle`; the coordinate helper uses
  `HomologicalComplex.homotopyCofiber.XIsoBiprod`.

The stated proof inputs are imported without `public`: the bounded-flat independent-coefficient
criterion, independent-coefficient K-flat resolution, site derived tensor descent,
`Mathlib.Algebra.Homology.BifunctorShift` (the tensor-complex definition), the resolution module,
and the triangulated-category module supplying the triangle-morphism isomorphism lemmas.
No proof input requires a new declaration or a dependency repair for this statement.

Edge cases checked against the formulas:

- Mathematical n=1 is Lean n=0; the adjacent map compares pi^2 and pi, with multiplication by
  pi in the shifted coordinate. No n=0 mathematical assertion is accidentally imposed.
- Zero complexes and the empty scheme remain allowed. Everything is a categorical biproduct
  or natural transformation; there are no nonemptiness hypotheses on X or its site.
- A complex killed by pi is allowed: its reduction cone retains both M and M[1]. This checks
  that no termwise injectivity hypothesis has entered the statement.
- For f=0 and f=id, the same four-coordinate permutation and negative-projection boundary
  make sense. The last coordinate of the boundary square is positive after the shift-1 sign.
- r=0 gives `(x,y)`; r=1 and r=-1 both give `(x,-y)`. The integer `negOnePow` covers all
  negative shifts, and `CommShift` retains coherence under adding shifts.
- There is no constraint on the characteristic of X and no boundedness, constructibility,
  flatness or completeness hypothesis on M. The coefficient and site universes are the
  same published internal-module conventions as the dependency, with no new universe equation.

Searches actually run:

- `msearch.py ... leanfinder` query: “The cone of multiplication by a scalar on cochain complexes
  is a functor that commutes with mapping cones and all integer shifts compatibly with quotient
  transition maps”. Eight hits included `mappingCone.mapHomologicalComplexXIso'_hom`,
  `map_δ`, `mapHomologicalComplexXIso_eq`, `mapHomologicalComplexXIso`, `descCochain`,
  `shiftIso`, `mapHomologicalComplexXIso'`, and `mapHomologicalComplexXIso'_inv`.
  These supply ordinary cone coordinate/shift comparisons, not this simultaneous scalar-cone
  interchange and canonical reduction tower assertion.
- `msearch.py ... loogle` query: `"mappingCone", "shift"`. Five hits: `shiftTriangleIso`,
  `shiftTrianglehIso`, `shiftIso`, and the two
  `shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv` lemmas. I read `shiftIso` and the
  standard cone-map and boundary signatures in their Mathlib sources. None states the item.
- `msearch.py ... grep` query: `mappingCone.*(map|shiftIso)|scalar.*cone`, restricted to
  `Algebra/Homology`. Twenty-five hits concerned ordinary cones, homotopy-category spectral
  objects, additive termwise functors and the standard shift isomorphism; no exact match.
- `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `principalReduction|principal_reduction|reductionCone|reduction_cone`, and principal/scalar-cone
  phrases found `DerivedCategory.reductionConeIso` in `Complete.AdicTower`, the site-Koszul
  quotient tower module, and ordinary-ring principal-reduction comparison modules. I read
  `AdicTower.reductionConeIso` and its naturality/unit/transition declarations: they concern
  constant sheaves of modules over a ring, not the present pulled-back continuous ring objects,
  and do not assert this strict cone-of-cone comparison. `DerivedNakayamaResolution` provides
  the scalar action and a natural cone comparison, which this delivery reuses and refines.
- The final exact-name search in Mathlib, `lean/WeilConjectures` and `lean/Sheaf` found no
  `principalConeCoordinates`, `principalConeInterchange`, or
  `AlgebraicGeometry.ProEtale.PrincipalReduction.principal_reduction_cone_calculus`.
  A `PrincipalReduction` namespace in `DerivedReductionResolutionIndependence` belongs to
  `SheafOfModules`, not this namespace, and defines a different exact-sections setup.

There is no `STATEMENT-DISPUTED` flag and no statement correction. Initial elaboration found
that the concrete canonical derived functor does not expose an inferable `CommShift` instance;
its coherent shift structure is now supplied as a conclusion and explicitly related to the
strict formula. Opening the published `CategoryTheory.Obj` scope resolves the coefficient
ring-object instances without adding assumptions or another construction.

Validation: `scompile.py NH lem-pe-principal-reduction-cone-calculus` compiled the delivered
module cleanly in its sandbox name and its actual library module name (12.2 s and 17.4 s).
There are no warnings apart from the permitted use of `sorry`; every variable and universe
is bound explicitly. The single postponed theorem is the statement of this DAG node.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
