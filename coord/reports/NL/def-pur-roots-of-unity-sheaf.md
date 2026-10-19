## Worker report

The node is already implemented in the published module
`Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`, by group Q16. The shared node
already records its reviewed implementation. This delivery records `existing: true`
for `AlgebraicGeometry.Scheme.proEtaleRootsOfUnitySheaf`, retaining the complete list
of its accompanying declarations. It supplies no Lean file, no new node and no
dependency module. The statement, dependencies and every other non-lean node field
remain unchanged. A fresh NK second reading is left to the independent reader.

I read the module in the shared library and confirmed its published source with
`scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`. The source
returned by that command agrees with the existing shared module. The hypothetical
replacement module used in an initial compile/dry-run exploration has been removed
from this sandbox; no duplicate module or cosmetic source change is delivered.

The following is the hypothesis-by-hypothesis and clause-by-clause correspondence.
All names in the next list are in `AlgebraicGeometry.Scheme` unless qualified.

- Arbitrary scheme S: `(S : Scheme.{u})`. The small pro-etale site is `S.ProEt` with
  `ProEt.topology S`. No affineness, nonemptiness, characteristic or invertibility
  restriction appears. Positive N is encoded by `(N : ℕ)` and `hN : 0 < N` for the
  module and transition constructions. The kernel definition is also defined at
  N=0, without excluding any of the node's positive exponents.
- Structure sheaf: `proEtaleStructureSheaf S`; the underlying presheaf is
  `(ProEt.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ`. Thus the sections are precisely
  global sections of the test scheme and its maps are pullback of functions.
- Units: `proEtaleUnitsSheaf S`, whose underlying presheaf applies
  `CommMonCat.units`, `CommGrpCat.toAddCommGrp`, and `AddCommGrpCat.uliftFunctor` to
  those same rings. Its sections are `ULift (Additive Γ(U,O_U)ˣ)`. The lift changes
  universe only, and additive addition denotes multiplication of units. These
  restrictions are exactly those induced by the structure-ring restrictions.
- N-th power map: `proEtaleUnitsPower S N` is `N • 𝟙 (proEtaleUnitsSheaf S)`.
  A natural-number multiple is the N-th power in this additive presentation of
  units. Its type is a morphism of abelian sheaves, including additivity and
  naturality with respect to every restriction.
- Roots sheaf: `proEtaleRootsOfUnitySheaf S N` is
  `kernel (proEtaleUnitsPower S N)`. The inclusion is
  `proEtaleRootsOfUnityInclusion S N = kernel.ι (proEtaleUnitsPower S N)`.
- Section formula: `existsUnique_proEtaleRootsOfUnitySections` identifies sections
  with `Additive (rootsOfUnity N ((proEtaleStructureSheaf S).obj.obj U))` by a unique
  additive equivalence compatible with that inclusion. The definition
  `proEtaleRootsOfUnitySections` selects this uniquely characterized equivalence.
  The subgroup `rootsOfUnity` consists of units with N-th power one. Restrictions
  are inherited from the natural kernel inclusion, so the formula describes the
  same sheaf rather than an unrelated sectionwise family.
- N-torsion: `proEtaleRootsOfUnity_nsmul` states `N • x = 0` for each test object U
  and each section x, with no invertibility assumption.
- Constant-ring module: `proEtaleRootsOfUnityCoefficientRing S N` is exactly
  `CategoryTheory.constantZModRingSheaf.{u + 1} (ProEt.topology S) N`, the
  sheafification of the constant lifted ZMod N ring presheaf.
  `proEtaleRootsOfUnityModule S N hN` applies the recorded torsion-sheaf theorem's
  `CategoryTheory.torsionSheafModule` to this same abelian sheaf and its N-torsion
  theorem. Its scalar action is the uniquely normalized action from that theorem.
- Divisibility transition: for positive N and N' and `h : N ∣ N'`,
  `proEtaleRootsOfUnityTransition` is the canonical `kernel.lift` of the inclusion
  of μ_N' followed by `(N' / N) • 𝟙 G_m`. Consequently it is exactly the stated
  power map, including naturality. Its well-definedness is the named theorem
  `proEtaleRootsOfUnityTransition_condition`, with the power calculation in its
  proof docstring.
- Linearity over ZMod N': `proEtaleRootsOfUnity_nsmul_of_dvd` gives N'-torsion of
  μ_N. `proEtaleRootsOfUnityTransition_linear` states sectionwise linearity for
  the two specified canonical N'-actions. `proEtaleRootsOfUnityTransitionModule`
  bundles that very additive transition as a morphism of module sheaves.
- Prime powers: `(ℓ : ℕ) (hℓ : ℓ.Prime)` and
  `proEtaleRootsOfUnityTransition_prime` identify the transition from exponent
  ℓ^(r+2) to ℓ^(r+1) with the ℓ-th power map. `proEtaleRootsOfUnityTower` uses
  `Functor.ofOpSequence` to give an actual `ℕᵒᵖ`-indexed inverse system. Its index
  r denotes the node's r+1, so it begins with μ_ℓ and covers every r≥1.

Dependency declarations read and used by the existing implementation:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its recorded site is the
  Mathlib `Scheme.ProEt` with `ProEt.topology` used throughout the module.
- `Sheaf.AlgebraicGeometry.ProEtaleStructureSheaf`:
  `AlgebraicGeometry.Scheme.proEtaleStructurePresheaf`,
  `proEtaleStructurePresheaf_isSheaf`, `proEtaleStructureSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleUnitsSheaf`:
  `AlgebraicGeometry.Scheme.proEtaleUnitsPresheaf`,
  `proEtaleUnitsPresheaf_isSheaf`, `proEtaleUnitsSheaf`.
- The Mathlib leaf `def-pur-abelian-sheaf-kernel` records
  `CategoryTheory.sheafIsAbelian` in `Mathlib.CategoryTheory.Sites.Abelian`, with
  `CategoryTheory.Limits.kernel`, `kernel.ι` and `kernel.lift`. Its record explains
  that the sheaf inclusion creates limits; these are the canonical kernels used.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  a transparent abbreviation for the existing `SheafOfModules` on arbitrary sites.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  the sheafification of the constant presheaf, as specified by its full signature.
- `Sheaf.CategoryTheory.TorsionSheafConstantModule`:
  `CategoryTheory.existsUnique_constantZModSheafModuleStructure`,
  `constantZModRingSheaf`, `torsionSheafModuleStructure`, `torsionSheafModule`, and
  `torsionSheaf_hom_linear`. Its fixed-group action is uniquely characterized by
  integer representatives and semilinear restriction, not an arbitrary action.

Edge cases checked: N=1 gives the zero kernel and its module over ZMod 1; empty S
and empty test objects permit zero section rings and trivial unit groups; N
sharing the residue characteristic is allowed because no Kummer surjectivity is
claimed; N=N' makes the quotient exponent one; target N=1 gives the map to the
zero sheaf; ℓ prime ensures positivity of every tower exponent. Site object and
morphism universes retain their actual sizes, and abelian coefficients are in
u+1. No equality of site universes or characteristic restriction was imposed.

Searches performed in this session:

- `msearch.py NK def-pur-roots-of-unity-sheaf leanfinder`: "The sheaf of roots of
  unity on the small pro-etale site, as kernel of the power map on units, with
  transition maps". Eight hits: general sheaf APIs, `rootsOfUnity` subgroup
  results and `restrictRootsOfUnity`; none is the complete sheaf definition.
- `msearch.py ... loogle`: `rootsOfUnity, CategoryTheory.Sheaf`; zero hits.
- `msearch.py ... grep`: `rootsOfUnitySheaf|proEtaleRootsOfUnity|unitsSheaf` in
  Mathlib `AlgebraicGeometry/`; zero hits.
- `rg` in upstream `WeilConjectures`: found `Scheme.rootsOfUnitySheaf` in
  `AlgebraicGeometry/Sites/Kummer.lean`. Its full signature uses
  `X.smallEtaleTopology`, so it does not match this pro-etale node. Searching the
  node id found no upstream implementation of this node.
- `rg` in project `lean/Sheaf`: found the exact Q16 module and all its recorded
  declarations, including transitions and the inverse system. This is the exact
  existing implementation reused by this delivery, not evidence of absence.
- Mathlib source inspection: `rootsOfUnity` is the subgroup of units with the
  specified power condition; `constantSheaf` is sheafification of the constant
  presheaf; `sheafIsAbelian` supplies the abelian-sheaf kernel API.

Source verification: the local literature files named in the node are absent,
so I read [Stacks 03PK](https://stacks.math.columbia.edu/tag/03PK),
[Stacks 03P4](https://stacks.math.columbia.edu/tag/03P4), and
[Stacks 03CY](https://stacks.math.columbia.edu/tag/03CY). The sectionwise roots
functor and kernel description agree with 03PK. The unique extension of a
constant-presheaf action to its sheafified ring is 03CY. The pro-etale site is
specified by this DAG node and its recorded site dependency. No source-based
statement correction is needed. No STATEMENT-DISPUTED issue was found.

Validation: the existing item module was compiled successfully with the prescribed
`scompile.py NK def-pur-roots-of-unity-sheaf` wrapper, without errors or warnings.
The final delivery contains an existing-declaration record only; `deliver2.py`
checks the primary and every accompanying declaration by importing the published
module and running fresh `#check` probes. The final dry-run result is recorded
below when available. Nothing is pushed by the worker.

## Second reading by NL

The node introduces an arbitrary scheme `S`, a positive integer `N`, the small pro-etale
site `S.ProEt` with structure sheaf `proEtaleStructureSheaf S`, units
`proEtaleUnitsSheaf S`, and the sectionwise power map. The published declaration
`AlgebraicGeometry.Scheme.proEtaleRootsOfUnitySheaf S N` is the kernel of
`proEtaleUnitsPower S N`, with type
`Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}`. Its accompanying declarations
identify sections with `Additive (rootsOfUnity N Γ(U,O_U))`, provide the canonical
`ZMod N` torsion module, define the transition `u ↦ u^(N'/N)` for `N ∣ N'`, and
assemble the prime-power inverse system. Each clause has the corresponding
published declaration listed in `lean.declarations`; the node and implementation
agree item by item. Verdict: pass; no statement or dependency mismatch.

Edge cases checked: `N = 1` gives the kernel of the identity and the zero `ZMod 1`
module; the total definition also accepts `N = 0`; `N = N'` gives the identity-power
transition; empty schemes and test objects are covered; no characteristic or
invertibility assumption is imposed; prime `ℓ` ensures positive tower exponents; the
site and coefficient universes remain `u` and `u + 1`.

I searched the current Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
with `msearch.py` (LeanFinder and Loogle) and `rg`. Mathlib has only the ring-level
`rootsOfUnity`, upstream has a distinct small-etale roots sheaf, and the exact
pro-etale declaration is the already-landed Q16 module. I read the dependency
signatures and the published source via `scompile.py --source`; no hollow definition,
unbound variable, or duplicate notion was found. No repair was needed. The node copy
records `existing: true` for the published declaration and all accompanying clauses.
