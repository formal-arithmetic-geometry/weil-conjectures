## Worker report

The module `Sheaf.AlgebraicGeometry.RGammaUnboundedBounded` states
`AlgebraicGeometry.Etale.rGamma_unbounded_bounded`. Its proof is `sorry`.
No definition, node statement, or dependency record is changed.

Clause-by-clause correspondence:

- The scheme is `(T : Scheme.{u})`; the commutative coefficient ring is
  `(Λ : Type (u + 1)) [CommRing Λ]`. This is the dependency's six-functor encoding,
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, retaining module coefficients.
- `K : DerivedCategory.Plus ...` is the bounded-below derived object. The representing
  complex is `C`; `eC : DerivedCategory.Q.obj C ≅ DerivedCategory.Plus.ι.obj K`
  explicitly says that it represents this K. A representative is not assumed to be
  termwise bounded below.
- `I`, `J`, `a`, `b`, `ha`, `hb` are the two K-injective resolutions in the node.
  `CochainComplex.IsKInjectiveResolution` unfolds to `QuasiIso` and K-injectivity.
  `J` is any resolution used for the bounded-below recipe, hence includes its chosen
  `Kinj(C)`; the dependency's cohomology construction makes no additional choice of
  a different coefficient category.
- `Sheaf.Γ` with target `ModuleCat Λ` is global sections with its Λ-module structure.
  Its identification with sections at the terminal étale object is Mathlib's
  `Sheaf.ΓNatIsoSheafSections`. `mapHomologicalComplex (ComplexShape.up ℤ)` applies
  it termwise; `DerivedCategory.Q` views the result in D(Λ).
- `∃ u : I ⟶ J, Nonempty (Homotopy (a ≫ u) b)` supplies the augmentation-compatible
  comparison; the following universal clause says its homotopy class is unique.
  `IsIso (DerivedCategory.Q.map (...map u))` says precisely that the image of this
  comparison under sections and localization is the comparison isomorphism.
- `eI` and `eJ` identify the actual recorded `rightDerivedGlobalSections` on K with
  the two section complexes. Their displayed equation identifies their comparison
  with the image of u. For Λ = ℤ the same coefficient recipe is the abelian-sheaf
  construction in the dependency; no additional forgetful functor occurs.
- The final universal clause states naturality: a second bounded-below object K',
  its representative C', and any two resolutions are quantified explicitly. Every
  derived map `f : Q(C) ⟶ Q(C')` (equivalently a map K → K' via eC and eC') has lifts
  `p : I ⟶ I'` and `q : J ⟶ J'` compatible with the augmentations after localization.
  For every such pair the square `QΓ(u) ≫ QΓ(q) = QΓ(p) ≫ QΓ(u')` commutes.
  Thus naturality is not limited to maps that already have a chain-map representative
  C → C'. The unique-homotopy-class clauses make the comparison independent of
  representatives; identity and composition of induced maps follow by uniqueness.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategories` (publicly imported through
  `KInjectiveResolutions`), with the recorded upstream `Etale.DerivedCategoryModule`
  encoding, `DerivedCategory.Plus` and its inclusion. The torsion predicate is not
  relevant to this statement.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`,
  `CochainComplex.IsKInjectiveResolution`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and `Etale.cohomology`:
  the former is the total right derived functor of `Sheaf.Γ`; the latter composes
  it with derived homology. Both bounded and unbounded dependency records point here.
- Mathlib `DerivedCategory`, `DerivedCategory.Q`, `SheafOfModules` (the general
  module-sheaf dependency), `Sheaf.Γ`, and `Functor.mapHomologicalComplex`.
  The existing six-functor module-valued-sheaf encoding is used throughout, as
  required by the derived-category dependency; no private module-sheaf category.
- Proof-only import `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`, declaration
  `CochainComplex.etale_kinjective_resolutions_exist`, and Mathlib's
  `CochainComplex.IsKInjective.Qh_map_bijective` from
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.

Edge cases: the empty scheme, zero complexes, and the zero coefficient ring are not
excluded. No characteristic or noetherian condition is imposed. All integer degrees
are included. The coefficient and sheaf universes match the dependency's established
encoding. No boundedness of the terms of C, I, J is imposed beyond boundedness of K
in the derived category. Arbitrary two resolutions, including identical resolutions,
are allowed. No false or ambiguous node clause was found; no statement correction or
new dependency module was needed.

Searches made in this session:

- `msearch.py leanfinder`, query "bounded below derived global sections agrees with
  unbounded derived global sections via unique K-injective homotopy comparison":
  eight results, including `CochainComplex.IsKInjective.Qh_map_bijective`,
  `InjectiveResolution.isoRightDerivedObj`, generic exact-functor and boundedness APIs.
  None states this coefficient-preserving comparison with uniqueness and naturality.
- `msearch.py loogle`, query `rightDerivedFunctorObjQIso`: no hits (unknown identifier
  in the Mathlib search service). The upstream source of that name was then opened:
  it computes a right derived functor on a single K-injective complex, but does not
  state this node's two-resolution comparison and naturality.
- `msearch.py grep`, regex
  `rightDerived.*Plus|globalSections.*[Cc]ompat|[Cc]ompat.*globalSections` in
  `Algebra/Homology/DerivedCategory`: eight generic bounded right-derived hits,
  not the present statement.
- `rg` of the node id, proposed declaration name, and
  `rightDerivedGlobalSections.*[Cc]ompat` in upstream `WeilConjectures` and project
  `lean/Sheaf`: no exact comparison declaration. Further source searches located
  `Sheaf.Γ`, `mapHomologicalComplex`, and the generic K-injective comparison API.
  Their signatures and docstrings, and the blueprint source page, were read.

Validation: the expanded final statement compiled cleanly using `scompile.py` on the
server, nice 19, two threads, 60 seconds per file (reported compile time 2.0 seconds).
The initial draft omitted the uniqueness and naturality clauses; it was replaced
before delivery. Independent second reading is reserved for the dispatcher's next worker.


## Second reading by NG

I independently opened the item JSON, its blueprint source page, all six statement
 dependency nodes and their recorded declarations, the resolution-existence node and
module, and the Mathlib K-injective Hom comparison. I read Stacks `derived.tex`,
`lemma-K-injective` (070I), and `injectives.tex`,
`theorem-K-injective-embedding-grothendieck` (079P). The former assumes an abelian
category; the latter assumes a Grothendieck abelian category. These are available
for the recorded category of module-valued étale sheaves; neither assumes that T
is noetherian or that the coefficient ring is a field.

My object/hypothesis/conclusion checklist, matched to the actual signature:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary scheme T | `(T : Scheme.{u})` | Matches; no geometric property added. |
| Commutative ring Λ | `(Λ : Type (u + 1)) [CommRing Λ]` | Matches the dependency encoding, including the zero ring. |
| K in D⁺ of étale Λ-module sheaves | `K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))` | Matches the recorded `DerivedCategoryModule` carrier and bounded-below full subcategory. |
| C represents K | `C` and `eC : DerivedCategory.Q.obj C ≅ DerivedCategory.Plus.ι.obj K` | Matches, without requiring termwise boundedness. |
| Two resolutions a:C→I, b:C→J | `a`, `b`, `ha`, `hb` using `CochainComplex.IsKInjectiveResolution` | The opened abbreviation is exactly `QuasiIso f ∧ I.IsKInjective`; J may in particular be the bounded recipe's chosen resolution. |
| Γ(T,M)=M(T), retaining coefficients, termwise | `Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and `.mapHomologicalComplex (ComplexShape.up ℤ)` | Matches: `Sheaf.ΓNatIsoSheafSections` identifies Γ with terminal-object evaluation. No forgetful functor changes coefficients. |
| Unbounded RΓ of K | `(rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T).obj (DerivedCategory.Plus.ι.obj K)` | Opened the definition: the total right derived functor of exactly this Γ. |
| Agreement with Γ(T,J) in D(Λ) | `IsIso (DerivedCategory.Q.map (...map u))`, together with `eI`, `eJ` and their equation | Matches both section-complex models of the recorded RΓ object; the comparison itself is specified below, not an arbitrary isomorphism. |
| Augmentation-compatible unique homotopy class | `∃ u`, `Nonempty (Homotopy (a ≫ u) b)`, and the universal `u'` clause | Matches existence and uniqueness of the class, not uniqueness of the chain map. |
| Comparison is the image of that class | `DerivedCategory.Q.map (...map u)` in the isomorphism and `eI.hom ≫ ... = eJ.hom` | Matches termwise Γ followed by localization. |
| Natural in K | Final universal clause over C', I', J', K', eC', a', b', u', and every derived f | Matches: the two existence clauses supply lifts of every derived map, and the universal p,q clause asserts the commuting comparison square for any lifts. |
| Bounded recipe, and integral coefficients | Same module-sheaf construction for J; `rightDerivedGlobalSections` is also the recorded bounded dependency | Matches the node's explicit coefficient-preserving extension of its abelian-sheaf recipe. At ℤ it is the integral-module encoding of abelian sheaves. |

For naturality, `eC` and `eC'` identify all derived maps QC→QC' with
maps K→K'; the quantification is not restricted to chain maps C→C'. The order
of the binders gives the comparison u before the arbitrary second object and map,
as required. Independence of chain-map representatives follows from the explicit
homotopy uniqueness clause. The equation uses the correct composition order:
Γu followed by Γq equals Γp followed by Γu'.

Edge cases checked: the empty scheme and zero object are permitted; the zero ring
and all characteristics are permitted; cochain degrees range over all integers
(including 0 and negative degrees). There is no indexed-family nonemptiness
hypothesis. Identical resolutions are permitted. `universe u` and every object
and morphism variable are explicitly bound. The coefficient universe is the
established six-functor universe of the dependency, not a new restriction to
finite rings or fields. No termwise injectivity or boundedness is silently assumed.

Independent searches used different wording from the worker's searches:

- `msearch.py leanfinder`: “two K-injective resolutions global sections canonical
  homotopy equivalence natural comparison”. Eight hits concern ordinary
  `InjectiveResolution.iso`, `homotopyEquiv`, and their right-derived naturality;
  these resolve objects with ℕ-indexed injective resolutions, not arbitrary
  ℤ-indexed K-injective resolutions in this node.
- `msearch.py loogle`: `HomotopyEquiv.map`; the service reports an unknown
  identifier and no hit. I did not treat this failed lookup as evidence of absence.
- `msearch.py grep`: `rightDerivedGlobalSections|ΓNatIsoSheafSections`; results
  give the terminal-object sections comparison, not this theorem.
- Direct `rg` across Mathlib homological algebra, upstream `WeilConjectures`, and
  project `lean/Sheaf`, using `Γ.*[Hh]omotopy`, comparison/K-injective combinations,
  and the proposed declaration name. I opened the nearby project's
  `KInjectiveComparisonPrinciple`: it states precomposition bijectivity, not the
  RΓ comparison. I also opened upstream `rightDerivedFunctorObjQIso`: it computes
  R(F) on one K-injective object and does not state this two-resolution uniqueness
  and naturality theorem. The upstream name index gives no duplicate theorem.

There are no new definition nodes or dependency modules in this delivery, and no
`statement_change` to audit. The existing dependency modules supply the actual
notions used, so no private replacement or missing notion is needed. The module
introduces no definitions, instances, or notation. Its sole theorem has a `sorry`
proof; its docstring has the blueprint/source and all four proof steps, including
the homotopy comparison, preservation by Γ, uniqueness, and naturality.

Mismatches found: none. Changes: appended this independent second-reading record;
left the Lean module and node signature unchanged. The node's `lean.statement`
was checked by exact string equality against the full theorem signature.
