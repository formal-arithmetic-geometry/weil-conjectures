## Worker report

The module `Sheaf.SixFunctors.EtaleGenericPerfectHom` states
`AlgebraicGeometry.Etale.etaleGenericPerfectHom`.  It uses the finite commutative
coefficient ring `A : Type (u + 1)`, schemes `S,S' : Scheme.{u}`, an arbitrary
morphism `g : S' ⟶ S`, bounds `a ≤ b` and `c ≤ d`, objects `P,N` in the recorded
étale derived category, a cover by étale charts, and bounded complexes on those
charts.  The cover hypothesis gives, on every chart, an isomorphism from the
complex `E` to the pullback of `P`, vanishing outside `[a,b]`, and maps in each
degree exhibiting `E.X n` as a retract of a finite constant free module.  The
`hN` hypothesis is exactly vanishing of the cohomology sheaves of `N` outside
`[c,d]`.

The local chart clauses are rendered by `Scheme.Cover`, `CochainComplex` over
`Sheaf (U.X i).smallEtaleTopology (ModuleCat A)`, `IsZero (E.X n)` for the
outside degrees, and the maps `ι, π` with `ι ≫ π = 𝟙`.  The two conclusion
intervals are the predicates `IsZero` on `DerivedCategory.homologyFunctor` for
`H = RHom_S(P,N)` and `H' = RHom_{S'}(P',N')` outside `[c-b,d-a]`.  Here `P'` and
`N'` are the canonical derived pullbacks via
`Functor.leftDerivedFunctor ((g)^*[ModuleCat A])`.  The displayed `ev` and `ev'`
are the derived tensor-Hom counits preceded by the canonical derived tensor
symmetry.  The existential `β` has source the derived pullback of `H` and target
`H'`; its equation is the evaluation characterization after the canonical
comparison `leftDerivedUpperStarTensorIso`.

Recorded declarations used are:

- `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`;
- `AlgebraicGeometry.Etale.derivedHom`,
  `AlgebraicGeometry.Etale.derivedTensorHomAdjunction`, and the derived Hom
  closed structure from `WeilConjectures.SixFunctors.Etale.Derived.Hom`;
- `AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory` and
  `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso` from
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` and
  `...UpperStarMonoidal.Comparison`;
- `AlgebraicGeometry.Etale.derivedTensorSymmetry` from
  `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`;
- `AlgebraicGeometry.Etale.upperStar` and `mapDerivedCategory` from the recorded
  étale pullback framework.

The edge cases checked were `P = 0`, `N = 0`, `g = 𝟙 S`, an empty target
scheme `S'`, `a = b`, `c = d`, a complex concentrated in an endpoint degree,
and a degreewise idempotent summand of a finite free module (including rank
zero).  The interval arithmetic gives the expected endpoint shifts in each
case, and the evaluation equation remains meaningful for the zero objects and
identity pullback.

Searches for an existing declaration were made with:

- `msearch.py ... leanfinder "inverse image derived internal Hom bounded finite projective complex etale sheaves"`; it returned only unrelated LightCondensed internal-Hom declarations, so no match;
- `msearch.py ... loogle "derivedHom tensor pullback finite projective"`; it returned no hits (the bare identifier is not in the search environment);
- `msearch.py ... grep "perfect.*Hom|finite.*projective.*pullback" WeilConjectures`; it returned no hits;
- `rg` over `lean/Sheaf` and `WeilConjectures`, which found the generic étale `derivedHom`, the canonical tensor symmetry, and the monoidal pullback comparison, but no theorem with this finite-projective chart hypothesis and interval conclusion.

The module compiles with `scompile.py`; its only proof is the required `sorry`.

## Second reading by Q58

A second pass read the node, the full theorem signature, and the module.  The
finite ring, scheme morphism, four integer bounds, inequalities, derived objects,
cover, local quasi-isomorphism, boundedness, retract maps, and bounded cohomology
hypotheses all appear explicitly.  The two interval clauses use `c - b` and
`d - a` exactly.  The pullback objects use the exact constant-coefficient derived
pullback, and `β` is an isomorphism whose equation uses the derived tensor
comparison and both evaluation counits.  No properness, smoothness, flatness,
cohomological-dimension, or boundedness assumption was added.  No mismatch was
found.
