## Worker report

Wrote `lean/Sheaf/CategoryTheory/ComplexExtDiskSphere.lean`, with the main statement
`CategoryTheory.exists_complexExtDiskSphere`. Its sole theorem has proof `by sorry`.
The unchanged node statement is rendered by the data structure `ComplexExtDiskSphere`.
No other DAG statement is stated, no node is corrected, and no new notion requires a
new definition node. The two helper definitions only express the endpoint action and
the inclusion of an actual short exact sequence into the already recorded Yoneda quotient.

The earlier blocker has cleared: `lem-coef-yoneda-derived-ext-comparison` now records
`Sheaf.CategoryTheory.YonedaDerivedExtComparison`, whose current source was checked both
in the shared checkout and with `scompile.py --source`. No dependency repair was needed.

Hypotheses and conventions:

- The arbitrary abelian category is `(A : Type u) [Category.{v} A] [Abelian A]`, with
  independent object and morphism universes. These are the only premises of the theorem.
- Integer complexes are `CochainComplex A ℤ`; the objects M and I are in A, and all
  degrees are unrestricted `ℤ`. The letters M in the two disk formulas instantiate
  the independent objects A and B of the prose, not an identification between them.
- Ext-one is `YonedaExtension.Classes V U 1`, in the order kernel V, quotient U:
  actual finite exact sequences modulo endpoint-fixed zigzags. In degree one every
  endpoint-fixed arrow is an isomorphism, so this is precisely fixed-endpoint
  isomorphism classes. The two `YonedaDerivedExtComparison` values supply the Baer
  group laws `classGroup`, with geometric Baer construction specified by `baer_sum`
  and `baer_exists` in the dependency. Every equivalence uses those group laws
  explicitly with `@AddEquiv`; there is no unrelated group instance or replacement
  of the Yoneda carrier by derived Ext.
- The theorem existentially includes those already available comparison data,
  instantiated using `HasExt.standard A` and `HasExt.standard (CochainComplex A ℤ)`.
  Thus it adds no small-Ext, enough-injectives, enough-projectives, or resolution
  premise. `HasExt.standard` exists for every abelian category, in `max u v`.
  The general data structure also supports independent smaller Ext universes.
- The sphere is the existing `(singleFunctor A n).obj M`, with M in degree n and
  zero elsewhere. The disk is existing `CochainComplex.doubleId M n`, the specialization
  of `HomologicalComplex.double (𝟙 M)` at n,n+1. Its differential is the identity
  under `doubleXIso₀`, `doubleXIso₁`, by `double_d`. No second disk/sphere is defined.
- `Y.cycles n` is the recorded complex API's cycle object, canonically the kernel
  of the differential in degree n. `Y.Acyclic` is exactness at every degree;
  in an abelian category this means image equals kernel. `X.homology (n-1)` is
  the quotient of cycles by boundaries, exactly the stated cohomology object.

Clause-by-clause correspondence:

1. `disk_left M Y n` is an additive equivalence from
   `Classes Y (doubleId M n) 1` to `Classes (Y.X n) M 1`, hence
   Ext¹_Ch(DⁿM,Y) ≅ Ext¹_A(M,Yⁿ).
2. `disk_right X M n` is from `Classes (doubleId M n) X 1` to
   `Classes M (X.X (n+1)) 1`, hence Ext¹_Ch(X,DⁿM) ≅ Ext¹_A(Xⁿ⁺¹,M).
3. `sphere_left M Y n hY`, where `hY : Y.Acyclic`, is from
   `Classes Y ((singleFunctor A n).obj M) 1` to `Classes (Y.cycles n) M 1`.
4. `sphere_right X M n hX`, where `hX : X.Acyclic`, is from
   `Classes ((singleFunctor A n).obj M) X 1` to `Classes M (X.cycles (n+1)) 1`.
5. `hom_complex X Y h` assumes for every integer k
   `Subsingleton (Classes (Y.X k) (X.X k) 1)`, exactly the vanishing of the
   component Ext-one groups, and gives an additive equivalence to
   `CochainComplex.HomComplex.CohomologyClass X Y 1`.
   `HomComplex.Cochain` is the product of component Hom groups indexed by all integers
   (implemented with equality-indexed triplets); Mathlib's differential `δ_v` is
   d_Y h minus (-1)^r h d_X, and `CohomologyClass` is cocycles modulo coboundaries.
   Its `homologyAddEquiv` identifies it with the usual H¹ of `HomComplex X Y`.
6. `hom_complex_split` states the off-diagonal clause for every actual short exact
   sequence S and every family of component `Splitting`s σ: its Yoneda class maps
   to `CohomologyClass.mk (cocycleOfDegreewiseSplit S σ)`. The component of that
   cocycle is σ.s followed by d_E followed by σ.r, exactly the upper-right block
   of the differential when E is identified with Y⊕X. The helper
   `shortExactYonedaExtension` retains precisely S's maps and endpoints, with real
   data and the supplied short-exactness proof. It makes no choice and has no sorry.
7. `injective X I n`, with `[Injective I]`, maps
   `Classes ((singleFunctor A n).obj I) X 1` additively to
   `(X.homology (n-1) ⟶ I)`. There is no acyclicity assumption on X.
8. The four `disk_*_naturality` / `sphere_*_naturality` fields state naturality in
   both endpoints, using `doubleIdMap`, `singleFunctor.map`, component maps, and
   `cyclesMap`. For sphere formulas both relevant complexes are acyclic, exactly
   the full subcategory where the isomorphism is claimed. `mapOne` is a real
   construction using the canonical comparison, Ext.mk₀, and Ext.comp. By the
   dependency's naturality field these are actual pullback/pushout actions on
   Yoneda classes, not unconstrained maps.
9. `hom_complex_naturality` states the Hom classification's endpoint compatibility
   on every cocycle, by `Cocycle.precomp` and `Cocycle.postcomp`. The quotient map
   `CohomologyClass.mk` is surjective, so this is naturality on all cohomology classes.
   `injective_naturality` states compatibility with `homologyMap` in X and
   postcomposition between arbitrary injective objects I,I'.

Dependency declarations used (sources and complete declaration docstrings inspected):

- `def-sp-abelian`: Mathlib.CategoryTheory.Abelian.Basic, `CategoryTheory.Abelian`
  (the node's mathlib_match, rather than a missing lean record).
- `def-sp-injective-resolutions`: Mathlib.CategoryTheory.Preadditive.Injective.Basic,
  `CategoryTheory.Injective`; the statement uses the object notion, not resolutions.
- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `CochainComplex`, `DerivedCategory`, `HasDerivedCategory` and standard localization.
- `lem-coef-yoneda-derived-ext-comparison`:
  Sheaf.CategoryTheory.YonedaDerivedExtComparison, `YonedaExtension`,
  `YonedaExtension.Classes`, `YonedaExtension.classOf`, `YonedaDerivedExtComparison`,
  and `nonempty_yonedaDerivedExtComparison`. Its carrier, group law, comparison
  normalization, geometric Baer operation and endpoint naturality are reused directly.
- Disks: WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective,
  `CochainComplex.doubleId`, `doubleIdMap`; their Mathlib underlying construction is
  Algebra.Homology.Double, `HomologicalComplex.double`.
- Spheres: Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors,
  `CochainComplex.singleFunctor`. Hom cohomology: HomComplexCohomology,
  `CochainComplex.HomComplex.CohomologyClass`; splitting cocycle: DegreewiseSplit,
  `CochainComplex.cocycleOfDegreewiseSplit`.

All stated proof-dependency modules are imported (non-public for proof-only uses):
HomologicalComplexAbelian (degreewise exactness), Sheaf.CategoryTheory.PushoutShortExactSequence,
ShortComplex.SnakeLemma, CategoryTheory.Abelian.Refinements, ShortComplex.Exact,
and Preadditive.Injective.Basic. The theorem docstring carries all eleven proof
steps from the node, including Baer addition, duality indices and naturality.

Edge cases checked before finalizing the statement:

- Every integer degree, including zero and negative degrees; no boundedness or
  nonnegative-degree condition. Disk right is n+1; injective sphere is n-1.
- Zero objects and zero complexes: all formulas give the expected zero groups.
- The zero category is allowed: no nonzero-object or nonempty-test-family premise.
- A nonacyclic X is allowed in the injective clause; for X=S^(n-1)M it gives Hom(M,I),
  which detects the crucial shift. Acyclicity is imposed only for the two sphere
  cycle formulas, not for disks or the general Hom classification.
- No componentwise Ext vanishing is assumed in the disk and acyclic-sphere formulas.
- Degreewise split extensions are classified by the actual off-diagonal cocycle,
  preventing a mere arbitrarily chosen group isomorphism from satisfying that clause.
- Object/morphism universes u,v are independent; no hidden equality is imposed by
  the choice of standard Ext universe.

Searches for existing declarations (full search results remain in searches.jsonl):

- `msearch.py ... leanfinder "Natural Yoneda Ext one disk sphere complexes degreewise split
  extensions Hom complex"`: 8 hits, principally `homOfDegreewiseSplit`, its component
  formula and triangle constructions. These construct the cocycle and triangle but
  do not assert the six Yoneda isomorphisms; the cocycle construction is reused.
- `msearch.py ... loogle "CochainComplex.cocycleOfDegreewiseSplit,
  HomologicalComplex.eval, Ext"`: 0 hits. Earlier preserved Loogle query for
  Ext/CochainComplex/HomComplex also returned no matching classification.
- `msearch.py ... leansearch "Extensions of cochain complexes by disks spheres and
  degreewise split extensions computed by Hom cohomology"`: 8 hits including
  `HomComplex`, `CohomologyClass`, `cocycleOfDegreewiseSplit`, `coboundaries`, and
  `ProjectiveResolution.extEquivCohomologyClass`. The resolution comparison needs
  an actual resolution and is not this arbitrary-category, arbitrary-complex statement.
- `msearch.py ... grep "doubleId|cocycleOfDegreewiseSplit|Ext.*disk|Ext.*sphere"
  Algebra/Homology`: 7 hits, the degreewise-split cocycle and Mathlib double
  corepresentability; no matching extension classification.
- `rg` in Mathlib, upstream WeilConjectures and side Sheaf for disk/sphere, double,
  HomComplex, YonedaExtension and candidate names found the upstream doubleId and
  doubleIdMap and the newly landed Yoneda comparison, all reused; no target theorem.
- Search for the item id in upstream WeilConjectures found no attachment. Search of
  the project for the proposed names and for short-exact Yoneda constructors found
  no existing duplicate. The prior worker's three search records were retained.

Source check: read the node's agent-authored eleven-step proof, the recorded Stacks
extension conventions via the dependency source, the historical blueprint paragraph,
and the current main-20261015 `sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`.
The latter still uses the same coefficient-adjunction paragraph. This auxiliary tool
is agent-formulated, as the node says; no unavailable Gillespie lemma is claimed as
an exact source and no change to the blueprint unit is made.

Validation: file-only compilation through scompile.py was clean after making the
explicit Baer Add structures visible to inverse-equivalence projections. No sorry
occurs in any definition. The only postponed proof is the main named theorem.
The final delivery dry run is recorded by the prescribed wrapper; the independent
second reading is left to the next worker, as instructed.

## Second reading by ND

The node introduces an abelian category `A`; complexes `X,Y : CochainComplex A ℤ`;
objects `A,B : A`; and an integer `n`.  It asserts, in order: the two disk
`Ext¹` identifications; the two sphere identifications under acyclicity of the
appropriate complex; the degreewise-vanishing `Ext¹`/`H¹ Hom` identification;
the off-diagonal cocycle formula for every degreewise split short exact sequence;
and the injective-sphere formula without source acyclicity.  It also requires
Baer-additive structure and naturality in both endpoints (and in the Hom and
injective formulas).

The Lean rendering is `ComplexExtDiskSphere` and its existence theorem
`exists_complexExtDiskSphere`.  `A`, `[Category.{v} A]`, and `[Abelian A]` are
the only theorem hypotheses.  The Yoneda carrier is exactly
`YonedaExtension.Classes ... 1`, with the recorded comparison group structures;
the disks are the existing `CochainComplex.doubleId`, spheres are
`singleFunctor`; cycles and acyclicity are the existing complex API.  Fields
`disk_left`, `disk_right`, `sphere_left`, `sphere_right`, `hom_complex`,
`hom_complex_split`, and `injective` match the seven conclusion clauses and
their quantifier order.  The remaining fields state the endpoint, sphere,
Hom-cocycle, and injective naturality required by the source.  `mapOne` is the
canonical comparison-induced pullback/pushout action, and
`shortExactYonedaExtension` retains the actual short exact sequence; neither is
an arbitrary map or hollow definition.  The theorem supplies exactly the
standard `HasExt` instances and no extra finiteness, boundedness, or universe
equalities.

Explicit clause audit (in `Classes V U 1`, V is the kernel and U the quotient):

| Node clause | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary abelian category | `A : Type u`, `Category.{v} A`, `Abelian A` | Exact; u,v independent. |
| Integer complexes, objects and degrees | `X Y : CochainComplex A ℤ`, `M : A`, `n : ℤ` | Exact; M is independently quantified in each field. |
| Fixed-endpoint Yoneda classes with Baer addition | `YonedaExtension.Classes V U 1`, `cA.classGroup`, `cC.classGroup` | Exact; degree-one endpoint-fixed arrows are isomorphisms. |
| Disk in degrees n,n+1 with identity differential | `doubleId M n` | Exact; its definition is `HomologicalComplex.double (𝟙 M)`. |
| Sphere only in degree n | `(singleFunctor A n).obj M` | Exact. |
| Cycles and acyclicity | `Y.cycles n`, `Y.Acyclic` | Exact; kernel and exactness in every degree. |
| Ext¹(DⁿM,Y) ≅ Ext¹(M,Yⁿ) | `disk_left : Classes Y (doubleId M n) 1 ≃+ Classes (Y.X n) M 1` | Exact. |
| Ext¹(X,DⁿM) ≅ Ext¹(Xⁿ⁺¹,M) | `disk_right : Classes (doubleId M n) X 1 ≃+ Classes M (X.X (n+1)) 1` | Exact. |
| Y acyclic: Ext¹(SⁿM,Y) ≅ Ext¹(M,ZⁿY) | `sphere_left`, with only `hY : Y.Acyclic` | Exact. |
| X acyclic: Ext¹(X,SⁿM) ≅ Ext¹(Zⁿ⁺¹X,M) | `sphere_right`, with only `hX : X.Acyclic` | Exact; n+1 is retained. |
| Every component Ext¹ vanishes | `∀ k : ℤ, Subsingleton (Classes (Y.X k) (X.X k) 1)` | Exact vanishing; group structure supplies zero. |
| Ext¹(X,Y) ≅ H¹Hom(X,Y) | `hom_complex`, target `CohomologyClass X Y 1` | Exact; Mathlib's quotient by `coboundaries` is H¹. |
| Off-diagonal differential under every splitting | `hom_complex_split S hS h σ` | Exact; `cocycleOfDegreewiseSplit` has components `(σ p).s ≫ S.X₂.d p q ≫ (σ q).r`. |
| Injective I, arbitrary X: Ext¹(X,SⁿI) ≅ Hom(Hⁿ⁻¹X,I) | `injective X I n`, `[Injective I]`, target `X.homology (n-1) ⟶ I` | Exact; no acyclicity or resolution assumption. |
| Natural group isomorphisms | Six `@AddEquiv`s and the six `_naturality` fields | Exact; endpoint action is `mapOne`, Hom action is cocycle pre/postcomposition, final action is homology precomposition and postcomposition. |

The source was read directly: `homology.tex`, lines 1260–1460, Tags 010J,
010K and 010L, assumes precisely an abelian category and fixes endpoint maps,
pullbacks, pushouts, and Baer sums. Its size comment does not impose enough
injectives: the theorem uses the unrestricted `max u v` Yoneda carrier and
`HasExt.standard`. The blueprint coefficient-adjunction paragraph does not
state the six formulas; their eleven-step agent argument in this DAG node is
therefore the mathematical source of the auxiliary calculation. Mathlib
`HomComplex.δ_v` gives `d_Y h + (-1)^(r+1) h d_X`, exactly the node's
`d_Y h - (-1)^r h d_X`. No hidden standing hypothesis was found.

Edge cases checked: all `n,k : ℤ` (including zero and negative degrees), zero
objects and zero complexes, the zero category, and non-acyclic sources in the
injective clause. There is no variable index set here (the index is ℤ);
empty schemes and characteristic restrictions do not apply. No characteristic, nonzero, or
nonempty assumption is introduced; the sphere acyclicity hypotheses occur only
where the node has them, and the injective clause has none.

Searches used `msearch.py` LeanFinder/Loogle/grep, `rg` over Mathlib and
`WeilConjectures`, and the upstream-name search.  They found only the generic
`HomComplex`, `CohomologyClass`, `cocycleOfDegreewiseSplit`, `doubleId`, and
`singleFunctor` constructions; no disk/sphere Yoneda classification.  The
recorded dependency declarations (`CategoryTheory.Abelian`, `Injective`,
`DerivedCategory`/`HasDerivedCategory`, and
`YonedaDerivedExtComparison`) were opened and their signatures match their
node statements.  No mismatch was found, so no statement or dependency was
changed.  The module compiled cleanly with `scompile.py`; no warnings occurred
beyond the named theorem's permitted `sorry`.

Independent search details: LeanFinder query `Yoneda Ext one disk sphere cochain
complex natural additive equivalence` returned 8 hits (derived `Ext.homAddEquiv`,
single-complex cochain equivalences, and resolution-dependent Ext computations).
Loogle query `"Ext", "singleFunctor"` returned 8 hits about single-functor
morphisms and derived Ext naturality. Grep query
`Ext.*(double|single)|[Yy]oneda.*([Dd]isk|[Ss]phere)` returned 21 hits about
double/single maps and derived Ext. None states this classification. Direct
`rg` searches of the side project and upstream source found no duplicate.
There are no new nodes, dependency modules, statement corrections, or repair
notes for this item. The only second-reader change is this review report.
