## Worker report

The module `Sheaf.Algebra.Homology.NilpotentActionKoszulUnit` states
`CategoryTheory.nilpotentActionKoszulUnit`, with exactly one postponed theorem.
Its five helper definitions contain real data: the existing right total tensor
bifunctor with its instances, the recorded rearrangement of towers into complexes,
the right tensor Koszul tower, its two canonical summand inclusions, and the
sheaf endomorphism induced by the existing presheaf global-section action.
No independent mathematical notion or definition node is introduced.

Hypotheses and ambient objects:

- The site is `C : Type uC`, `[Category.{vC} C]`, `J : GrothendieckTopology C`,
  with `[EssentiallySmall.{r} C]`. Both site universes stay independent of the
  module universe r. The canonical sheafification and locally bijective instances
  are exposed as `[HasSheafify J AddCommGrpCat.{r}]` and
  `[J.WEqualsLocallyBijective AddCommGrpCat.{r}]`, giving Mathlib's abelian category.
- `R : Sheaf J CommRingCat.{r}` is a sheaf of commutative rings. Its underlying
  ring sheaf is `(sheafCompose J (forget₂ CommRingCat RingCat)).obj R`, and the
  module category is the recorded `ringedSiteModules.{r}` on this ring sheaf.
- `t : (SheafOfModules.unit ...).sections` is a genuine compatible global section,
  with no terminal object assumed. `@id (R.obj.obj U) (t.val U)` only makes its
  ring carrier explicit for exponentiation; it does not change the section.
- `[HasExactLimitsOfShape (Discrete ℕ) ...]` is exactness of countable products.
  The two `[HasDerivedCategory.{w} ...]` binders choose the unbounded derived
  categories of module sheaves and strict towers in a common morphism universe.
- All complexes are `CochainComplex ... ℤ`. There is no boundedness, regularity,
  K-flatness, Noetherianity, or uniform exponent across an outer tower.

Clause-by-clause rendering:

1. The strict Roos model is the recorded `roosF`, a shifted mapping cone of the
   recorded `towerTransitionEndomorphism` on termwise products. Its `roosχ`
   coordinates are `(shifted,product)`, so the displayed `(v,u)` in the node is
   reordered by the biproduct braiding. Its differential and strict maps are the
   dependency's actual cone differential and diagonal product maps.
2. Positive j is represented by `m : ℕ` with j=m+1. The actual complexes are
   `principalKoszul R t m`, with the recorded strict `(t,1)` transitions in
   `principalKoszulTower R t`. The functor `spKoszulRightTensor` is exactly
   `curriedTensor.map₂CochainComplex`. Composing with that tower and the recorded
   `koszulTowerComplex`/`koszulTowerComplexMap` forms `spKoszulRightTower R t`.
   Thus the order is Q tensor L, rather than just a claim about an unspecified
   cone or a left tensor model.
3. The existential functor Z, natural transformations i and p, and equation hi
   give a natural sequence on all complexes. The second conjunct is the genuine
   `ShortComplex.ShortExact` assertion in complexes of strict towers, for every Q.
4. Each Z level is identified with Q[1] by the actual complex isomorphism ζ.
   The seventh conjunct pins its transition to `spKoszulScalar R t` under ζ and
   the canonical shift-coordinate isomorphisms. It is not the constant tower
   with identity transition.
5. The family χ identifies the actual tensor terms with Q^k biprod Q^(k+1).
   Its inverse is pinned in the first conjunct to
   `spKoszulRightCoordinatesInv`: the right unitor, the degree-zero unit of the
   single complex, the target/source inclusions of the principal mapping cone,
   and the actual total-tensor summand inclusions. These are real constructions,
   so χ is not an arbitrary coordinate isomorphism.
6. The third conjunct says `i` is `(x,0)` in these fixed coordinates. The fourth
   says p is `k.negOnePow • biprod.snd` under ζ and the canonical shift
   identification, exactly `(x,y) ↦ (-1)^k y`.
7. The fifth conjunct is the differential formula: its first summand is
   d_Q followed by biprod.inl, and its second is
   `(k+1).negOnePow • endoPow (spKoszulScalar ... (Q.X (k+1))) (m+1)`
   into the first target summand plus d_Q into the second. This is precisely
   `(dx+(-1)^(k+1)t^j y,dy)`. The sixth conjunct fixes strict transitions to
   `biprod.map (𝟙 _) (spKoszulScalar ... (Q.X (k+1)))`, i.e. `(x,ty)`.
8. u is one natural transformation from the identity on all unbounded complexes
   to `spKoszulRightTower R t ⋙ roosF`. The eighth conjunct pins its degree
   k+1 component, after `roosχ`, to `biprod.lift 0 (Pi.lift i).f`. This is
   exactly the specified zero-homotopy chain map. The dependent type annotation
   `@id (Q ⟶ roosP ...)` fixes only the product lift's source and target.
   The formula does not mention any nilpotence exponent.
9. The ninth conjunct quantifies over every Q and a≥1 and assumes on every
   site object U and degree k that `(t_U)^a • x = 0` for all local sections x.
   This is exactly termwise annihilation as a sheaf morphism, not annihilation
   only on global sections or only on cohomology. It concludes `QuasiIso (u.app Q)`
   and vanishing of `RF.obj (DerivedCategory.Q.obj (Z.obj Q))` for every actual
   total right derived inverse limit RF with its `IsRightDerivedFunctor` unit.
   This is the same derived-limit characterization as the recorded dependency.
10. Naturality on every R-linear chain map is the type `NatTrans` of u, i and p.
    It asserts literal chain-map equality, rather than equality only in D(R).
    The last conjunct uses `Functor.whiskerLeft T u` for any strict outer tower T;
    this is a genuine strict map of n-towers. The exponent function a : ℕ → ℕ
    is positive at each level and may vary arbitrarily. Every component is a
    `QuasiIso`; no common exponent or cohomological bound appears.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`, with Mathlib's abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`: localization of ℤ-cochain complexes.
- `Sheaf.CategoryTheory.StrictRoosModel`, `roosF`, `roosP`, `roosχ`,
  and the explicit augmentations; the statement uses the actual functor and
  its coordinates, rather than restating a Roos interface.
- `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`, `principalKoszul`,
  `principalKoszulTower`, `globalSectionMultiplication`, `endoPow`,
  `koszulTowerComplex`, and `koszulTowerComplexMap`. The recorded left-tensor
  model remains intact; this item's demanded right tensor uses the same
  Koszul complexes/transitions and actual Mathlib tensor bifunctor.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`
  and `Functor.map₂CochainComplex`; the sheaf tensor structure and its
  independent-coefficient instances are imported through the Koszul dependency.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`: total derived limit
  with the same smallness, coefficient universe and derived-functor predicate.
- Proof import `Sheaf.CategoryTheory.StrictRoosComparison`, `strictRoosComparison`.
  It is used by proof step 4; no replacement or specialized size assumption is
  made in this statement.
- Proof imports `Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` and
  `CochainComplex.homOfDegreewiseSplit_f`, together with the triangulated Qh;
  and `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`. These are the
  recorded Mathlib matches for the last two proof dependencies.
- `PresheafOfModules.sectionsSMul` is reused to define the sheaf scalar
  endomorphism; no new sectionwise scalar construction is substituted.

Edge cases checked before and after writing:

- t=0 and a=1: Z has zero transitions; the Roos contraction applies at once.
- t a unit: nilpotence forces Q to be the zero complex; the implication and
  all natural transformations still make sense, including the zero ring.
- Q=0, the empty site, and complexes unbounded in both directions are included.
  No nonempty-object, terminal-object or boundedness binder was introduced.
- The first level m=0 uses t^(0+1), never a fictitious t^0 first level.
- At k=-1,0 the quotient signs are -1,+1 and its chain map to Q[1] has the
  negative shift differential. The two mixed terms in d² cancel in every degree.
- Tower sections need not commute with transition maps; no splitting of the
  sequence as towers is asserted. Degreewise tensor splittings give exactness.
- A tower with exponents a_n=n+1 is admitted, regardless of whether a common
  annihilating exponent exists.

Searches for an existing statement (all through the prescribed tools or read-only rg):

- msearch leanfinder, query: “An unbounded complex of module sheaves killed by
  a power of t is quasi-isomorphic via the canonical unit to the Roos limit of
  its principal Koszul tensor tower”. Eight hits: generic cm5b resolutions,
  representation resolutions and derived truncations; no matching theorem.
- msearch loogle, query `"Koszul"`: zero hits.
- msearch grep, query `nilpotent.*[Kk]oszul|[Kk]oszul.*nilpotent`: zero Mathlib hits.
- msearch leansearch, query: “A sheaf complex annihilated termwise by a power
  of a global section is quasi-isomorphic to its principal Koszul completion
  via the canonical Roos unit”. Eight hits about sheaf units, generic injective
  resolutions, sheafification and quasicoherent presentations; no matching theorem.
- rg of the same nilpotent/Koszul pattern in `lean/WeilConjectures` and `lean/Sheaf`:
  `Paper.NilpotentKoszulCompletionUnit` and `Paper.NilpotentKoszulGradedTower`
  concern constant coefficient scalars over schemes and finite lists. Their
  statement does not give arbitrary ringed sites, termwise scalar annihilation,
  the principal right-tensor coordinate formulas, or the specified natural chain unit.
- rg for the item id in `lean/WeilConjectures`: no hit. rg for every proposed
  declaration name in Mathlib, upstream, Sheaf and `dag/lean_names_upstream.json`:
  no preexisting declaration.

The latest blueprint tower proof and its `_section.md` were read. No mathematical
statement correction, disputed statement, missing dependency, or new DAG node was
needed. Only the item's `lean` field changes. The seven-step natural-language proof
is in the theorem docstring. No proof is supplied in Lean at stage 2.

Validation: scompile.py compiled both the sandbox and the actual module with no
errors or warnings. An earlier pass needed explicit source/target types for the
product lift and an explicit ring carrier for t; both were repaired, without
changing the mathematical statement or imposing new assumptions.

## Second reading by Q112

This dispatcher-started worker was instructed not to start other agents; the
maintainer supplies the independent delivery review. I made a separate second
pass with the node and full Lean signature open. Every hypothesis and all ten
clause groups are matched above. I checked particularly the right tensor order,
the t^(m+1) positive indexing, the quotient's (-1)^k sign, the Roos coordinate
ordering, actual short exactness of tower complexes, all-chain-map naturality
before nilpotence, local rather than just global annihilation, and arbitrary
level-dependent exponents. The carrier and product annotations described above
were the only elaboration corrections. The helpers have explicit real data;
there are no private declarations, local notations, file-local instances,
auto-bound variables, auxiliary postponed theorems or unrecorded objects.
