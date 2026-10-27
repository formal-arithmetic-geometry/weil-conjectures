## Worker report

The module `Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization` states
`AlgebraicGeometry.ProEtale.StrictTower.towerAdjunctionRealization` with `sorry`.
Its only helper, `termwiseAdjunction`, is real data: the whiskering by `ℕᵒᵖ` of the
recorded module adjunction, with its actual unit and counit. No new category,
coefficient sheaf, pullback, direct image, derived functor or open extension is defined.
The node is unchanged except for `lean`. There are no new nodes or dependency repairs.

Hypotheses and clauses, in order:

| Node text | Lean rendering |
| --- | --- |
| A commutative ring B | `variable (B : Type (u + 1)) [CommRing B]`; no finite-ring or topology assumption |
| Every scheme and scheme map | `X Y Z : Scheme.{u}`, `f : X ⟶ Y`, `g : Y ⟶ Z`; no geometric property of f |
| Small pro-etale site and constant coefficients | Recorded `Scheme.ProEt.topology`, `coefficients B X`; the diagram realization uses `Scheme.proEtaleSiteModel X` and its transported topology |
| Strict positive-index towers | Recorded `Towers B X = ℕᵒᵖ ⥤ Modules B X`, with `n` representing positive index `n+1` |
| Ordinary unbounded derived categories | Recorded `Derived B X = DerivedCategory (Towers B X)`, with the standard localization instance |
| Canonical constant-section map is a ring-sheaf isomorphism | First conjunct: `IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat (CommRingCat.of B))` |
| Natural in B and compatible with ring maps | Second conjunct: the commuting square for every `C`, `[CommRing C]`, `φ : B →+* C`; the sheaf maps are `constantSheaf.map (CommRingCat.ofHom φ)` |
| Compatible with identities | Third conjunct: the coefficient map at `𝟙 X` equals the inverse-image identity supplied by `Adjunction.leftAdjointIdIso` from the canonical direct-image identity |
| Compatible with composition | Fourth conjunct: `constantRingIso B (f ≫ g) = Scheme.proEtaleRingCompositeCoefficients ...`; this uses the specified inverse-image compositor, not an arbitrary isomorphism |
| Exact module inverse image and exact tower inverse image | Fifth conjunct: `PreservesFiniteLimits` and `PreservesFiniteColimits` for `modulePullback B f` and `towerPullback B f` |
| Termwise left adjunction | The actual data `termwiseAdjunction B f : towerPullback B f ⊣ towerDirectImage B f`; fifth conjunct records its evaluated unit and counit as the module unit and counit |
| Module-sheaf realization on the small diagram site | Sixth conjunct: existence of `T`, `R`, and `M : ringedSiteModules R ≌ Towers B X`; the covering-sieve criterion specifies exactly the vertical product topology and the presheaf equality specifies `R(j,U)=B_X(U)` after the recorded site transport; `M.functor` is additive and exact |
| Grothendieck abelian category | Seventh conjunct: `IsGrothendieckAbelian.{u + 1} (Towers B X)` |
| Every complex has a K-injective resolution | Eighth conjunct: for every `K : CochainComplex (Towers B X) ℤ`, there are `I` and `s : K ⟶ I` with `I.IsKInjective ∧ QuasiIso s` |
| Termwise direct image preserves K-injectives | Ninth conjunct: K-injectivity of `((towerDirectImage B f).mapHomologicalComplex (.up ℤ)).obj I` whenever `I.IsKInjective` |
| Everywhere-defined total right derived direct image | Tenth conjunct: `(R B f).IsRightDerivedFunctor` for the actual `rightDerivedFunctorUnit` on homotopy categories, and invertibility of that unit on every K-injective complex |
| Derived adjunction induced by the termwise unit and counit | Eleventh conjunct identifies the specified `adj B f` with `(termwiseAdjunction B f).mapDerivedCategoryRightDerivedAdjunction`; equality of adjunction data fixes both unit and counit, including the canonical localization comparisons |
| Exact open extension and restriction | Last conjunct quantifies over every `j : U ⟶ X` with `[IsOpenImmersion j]`, and gives preservation of finite limits and colimits for `towerJ B j` and `towerPullback B j` |
| Open derived adjunction with termwise unit and counit | Last equality identifies `jAdj B j` with the derived whiskering of `moduleJAdj B j`, transported along the canonical `rightDerivedFunctorIsoMapDerivedCategory` for the exact restriction functor |
| Infinite rings and unbounded complexes, no transition assumptions | All rings in the coefficient universe are allowed; complexes use every integer degree, and `Towers` is the entire functor category with no surjectivity or boundedness predicate |

The normalization equalities deliberately name the existing derived-adjunction construction.
Its definition in `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`
is `Adjunction.derived` applied to the ordinary homotopy-category adjunction with
`mapDerivedCategoryFactorsh.hom` and `rightDerivedFunctorUnit`.
Thus it determines the localized ordinary unit and counit, rather than merely asserting
existence of some adjunction. The open equality uses the recorded transport from total
right derivation of exact restriction to its exact descent. Expanded component formulas
were costly to elaborate; the data equalities preserve the same normalization.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation of `SheafOfModules` and its existing abelian instance.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`,
  `NatTrans.ofOpSequence`; the statement uses their full functor category encoding.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the standard localization used by the recorded tower operations.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: `coefficients`, `Modules`,
  `Towers`, `Derived`, `constantRingIso`, `modulePullback`, `moduleDirectImage`,
  `towerPullback`, `towerDirectImage`, `G`, `R`, `adj` and their recorded instances.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `moduleJAdj`, `towerJ`, `J`, `jAdj`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleSheafInverseImage`,
  `proEtaleSheafAdjunction`, `proEtaleConstantInverseImageMap`, `proEtaleSiteModel`,
  `proEtaleModelTopology`; the constant map is exactly the adjunct of constant sections.
- `Sheaf.CategoryTheory.DiagramSiteRealization`:
  `CategoryTheory.exists_diagramSite_realization`; its site and coefficient formulas
  specialize to `J = ℕᵒᵖ` and the transported small pro-etale model.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`: `IsGrothendieckAbelian`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.

All recorded proof dependencies with available declarations are imported. Their modules
include the constant comparison, module adjunction, abelian inverse-image exactness,
independent-universe K-injective resolutions, total right derivation, exact-functor
derivation, general pre-derived adjunction, essentially constant ind/pro diagrams,
weakly-etale localization, ringed open comparison and localized module exactness.
The Mathlib matches for exact derived factorization and K-injective Hom comparison
are supplied by the exact-functor and derived K-injective imports. Nothing waits on
another item.

Edge cases checked against the signatures and source constructions: zero ring;
infinite ring; zero tower; nonsurjective transitions; arbitrary degrees in both
directions; identity maps and two composable arbitrary maps; empty schemes and
empty open immersion. All remain admitted. The index set is the specified nonempty
positive-integer tower, not an arbitrary empty diagram. Object universe `u+1` and
Hom universe `u` of the original pro-etale site are retained. `AsSmall.{u+1}` only
transports Hom sizes when forming the small diagram site. No independent lower
coefficient universe or equality of the original site universes is imposed.

Sources read: `literature/stacks-project/sites-modules.tex`,
`lemma-extension-by-zero` and `lemma-extension-by-zero-exact` (03DI, 03DJ);
`derived.tex`, `lemma-pre-derived-adjoint-functors-general` and
`lemma-pre-derived-adjoint-functors` (0DVC); the current blueprint's
`thm-cbc-complete-proetale.proof.md`; and the node's eight detailed proof steps.
The declaration docstring carries those eight steps in full.

Searches (2026-10-22):

- LeanFinder, "Constant coefficient inverse image and exact adjunctions on unbounded
  derived categories of strict towers of pro-etale module sheaves": eight hits,
  including `Adjunction.derived` and its unit/counit formulas; none states the full
  constant-coefficient strict-tower theorem.
- Loogle, `CategoryTheory.Adjunction, DerivedCategory`: zero hits.
- msearch grep,
  `proetale.*(tower|adjunction)|constantSheaf.*(pullback|inverseImage)|mapDerivedCategory.*adjunction`:
  one Mathlib file, `CategoryTheory/Sites/ConstantSheaf.lean`; general constant-sheaf API.
- LeanSearch with the same plain-language query: eight hits, including
  `SheafOfModules.PullbackConstruction.adjunction`, `constantSheafΓAdj`,
  `pushforwardPushforwardAdj`, `constantPresheafAdj`, `pullbackPushforwardAdjunction`,
  `Sheaf.isConstant_iff_mem_essImage`, `instIsLeftAdjointPullback`, `constantSheafAdj`.
  These give reusable ordinary constructions, not this theorem.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` found the recorded
  `StrictConstantTowerOperations` and `StrictTowerOpenExtension`, which are reused;
  tower evaluation and other coefficient systems do not state this full result.
- Direct searches for this node id and both new declaration names in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no match.

Validation: the full final module passed `scompile.py` in sandbox and library mode
with no errors or warnings (9.5 and 10.9 seconds). Earlier expanded normalization
formulas exceeded the file limit and were replaced by the exact adjunction data
identifications described above. No proof has been supplied and no limits were raised.
No statement dispute or source correction is needed.

## Second reading by Q103

Author self-check only; no independent worker was started, as the dispatcher brief
forbids sub-agents. The maintainer supplies the independent review.

With the node and final file open, I checked the coefficient isomorphism, ring-map
square, identity comparison and compositor; both module and tower exactness;
ordinary whiskered unit/counit; vertical small-site topology and coefficient
presheaf; Grothendieck property; existence and preservation of K-injectives;
total derived universal property; and both specified derived adjunctions.
The equality of full adjunction data, rather than an unnormalized `Nonempty`,
retains the unit/counit clauses. The underlying operations are the dependencies'
actual functors. I checked that no finite-ring, qcqs, transition-surjective or
boundedness binder appears, and that open immersion is required only for open
extension. The only change during this reading was replacing expanded normalization
component formulas by the equalities of the named induced adjunctions. No node
statement, hypothesis or conclusion was changed.
