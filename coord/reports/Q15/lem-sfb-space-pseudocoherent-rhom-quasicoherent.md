## Worker report

States `AlgebraicGeometry.AlgebraicSpace.pseudoCoherent_rhom_quasiCoherent` in
`Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentRHomQuasiCoherent`.
The only postponed proof is this named theorem. Its docstring reproduces all six
accepted DAG proof steps and names their dependencies. No theorem was proved here.
The current live node is split/reviewed but has no Lean record. Its stage-1 review
was preserved. The stage-handoff instruction in brief-stage2 §0 authorizes recording
its stage-2 statement; the previous stage-1 refusal does not apply.

Clause-by-clause correspondence:

- The scheme `S` and algebraic space over it are `{S : Scheme.{u}}` and
  `(X : AlgebraicSpace S)`. All universes are explicit (`u w`); the derived morphism
  universe is arbitrary `[HasDerivedCategory.{w} X.SmallModules]`.
- `K L : X.DerivedModules` are objects of the full unbounded derived category of the
  already recorded equivalent small affine etale ringed model. This is the existing
  size convention and definition, not a restriction to scheme objects or to QCoh.
- `L` has quasi-coherent cohomology in both alternatives: `hL : X.derivedQCohProperty L`.
  Factoring this common assumption outside the disjunction preserves both cases.
  The predicate transports cohomology through `X.smallModuleEquivalence.inverse` and
  uses the recorded Mathlib `SheafOfModules.IsQuasicoherent` on the original site.
- Case (i): the left disjunct is the recorded
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  X.smallStructureSheaf K`. Its definition uses bounded complexes of finite-free
  retracts on covering sieves. It imposes no lower or upper bound on L.
- Case (ii): the right disjunct contains `X.IsPseudoCoherent K`, the new definition
  described below: etale-local bounded-above finite-free models.
- The second part of case (ii) quantifies `∀ V`, a covering sieve `T`, every arrow
  `f : U ⟶ V` in it, then `∃ c : ℤ`. The condition `∀ n, n < c → IsZero ...`
  says exactly that the restriction of the n-th cohomology of L to U is zero.
  Slice restriction is exact, so this is the local cohomological lower bound.
  The bound lies inside the covering-member quantifiers; no uniform bound is used.
  A covering on the affine etale basis is equivalent to etale neighbourhoods at
  every point: every scheme chart has an affine open cover and coverings of the
  basis generate the original topology. Refining by the neighbourhoods yields the
  displayed sieves; conversely their jointly surjective scheme charts supply those
  neighbourhoods. No quasi-compactness of X is required for this equivalence.
- The conclusion `X.derivedQCohProperty (X.derivedHom.obj (op K, L))` is exactly
  quasi-coherent cohomology of the canonical K-injective internal derived Hom.
- There is no Noetherian, separation, finite type, quasi-compactness, support or
  global boundedness assumption or extra conclusion. Derived tensor and direct
  image do not occur in the conclusion and need no added choices or hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its small etale site, ring sheaf and `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules` with the same abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; cohomology is `homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`,
  the original-site specialization of Mathlib `IsQuasicoherent`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`, its local predicate and package.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly reexports the
  generic `CategoryTheory.derivedInternalHomOfUniverses`; the ordinary ModuleCat
  specialization is not used. `X.derivedHom` is the recorded small-site instance.
- Added existing dependency `def-sfb-space-derived-module-calculus`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `derivedHom`, and the underlying `SmallModules` and equivalence
  from `AlgebraicSpaceSmallRingedModel`. Its actual existing data are reused.
- The new definition imports the proved upstream
  `CategoryTheory.module_overFunctor_preservesZero` from
  `WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal` to form restricted complexes;
  and Mathlib `SheafOfModules.free` for finite free terms. No helper theorem is added.

Stated proof-dependency modules are imported without `public`: the upstream scheme
perfect and pseudo-coherent Hom results, `RingedSiteStrictPerfectHom`,
`RingedInternalHomShiftOfUniverses` (which reexports the recorded exact restriction),
and upstream `PerfectComplex`. The remaining proof nodes currently have no Lean
records, so there is no module to import for them. Their proof roles are explicit
in the theorem docstring; they are not required to type its statement.

Edge cases checked: the zero source and zero target satisfy the expected conclusion;
finite free rank zero is allowed (`Fin 0`), as are zero complexes. On the empty space
the empty covering sieve is available and imposes no spurious model or bound.
Non-quasi-compact spaces with componentwise increasing lower bounds are allowed
because c is chosen separately for each cover arrow. Perfect K permits unbounded L.
Pseudo-coherent K alone does not remove the lower-bound hypothesis. Independent
localization universe w is retained; no site/derived universe equality is imposed.

Searches: msearch leanfinder queried derived Hom quasi-coherence on algebraic spaces
and pseudo-coherent complexes of sheaves on algebraic spaces. It returned ordinary
scheme module categories, finite-presentation and quasi-coherence declarations, no
match. msearch leansearch queried pseudo coherent complex on an algebraic space;
it returned ordinary quasicoherent presentation data, no local complex predicate.
Loogle `SheafOfModules.IsQuasicoherent, IsPerfectOnRingedSite, IsPseudoCoherent`
returned no hits (unknown identifier IsPerfectOnRingedSite). Earlier retained Loogle
`SheafOfModules.IsQuasicoherent, DerivedCategory` returned no hits. msearch grep
`PseudoCoherent|LocallyBoundedBelow` and `derived.*[Hh]om|[Pp]seudo[Cc]oherent`
returned no hits. Direct rg in Mathlib, upstream WeilConjectures, Sheaf and DAG
found scheme/ring pseudo-coherence, but no absolute algebraic-space predicate or
this theorem; scheme Hom theorems apply only to schemes, and the older
`pseudoCoherentRHomQuasiCoherent` also assumes Noetherian. The matching algebraic-space
module-calculus node is reused. `blueprint_refs.py search pseudo-coherent` found
0 blueprint nodes; ancestor returned None, preserved in the new definition provenance.
The machine-readable msearch outputs are retained in the new node mathlib_searches
and sandbox searches.jsonl. No node statement is corrected or disputed.

Validation: both delivered modules compiled separately, in dependency order, through
scompile.py on the server. Both library compiles returned zero with no warnings.
The initial definition compile required importing the recorded zero-preservation
lemma before activating it; this was repaired without introducing a private instance
or adding a hypothesis.

## New nodes

`def-sfb-space-pseudocoherent-complex` defines
`AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent` in
`Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex`.
It existentially chooses a complex P representing K, then on covering sieves of
every object chooses bounded-above complexes of finite free sheaves and
quasi-isomorphisms to the exact slice restrictions of P. Upper bounds vary by
cover member and ranks by degree. Source: the algebraic-space use of Stacks 0A8A,
08HE, the ringed-site definition 08FT, and the finite-free characterization 08E5/08E7
on scheme charts. The definition contains real formulas and no sorry. Its only
notion absent from the library is this absolute etale-local condition; the existing
scheme `IsPseudoCoherent`, relative-space `IsPerfectRelativeToScheme`, and ordinary
ring predicates do not accept an arbitrary derived module on the small etale site
of an algebraic space. Three kinds of searches and DAG searches are recorded in
its mathlib_searches. It uses the existing small-model calculus rather than
redefining sites, module categories, derived categories, or restriction.

## Second reading by Q15

No independent worker reading: the dispatched brief prohibits starting agents and
authorizes direct delivery. The maintainer supplies the independent review.
A final self-check compared the node with both files: common hL factored correctly,
case (i) has no boundedness restriction, case (ii) has genuinely local lower bounds,
and the conclusion concerns the existing K-injective RHom on the equivalent site.

Preflight repair: added the `import_flags: []` field required by the live new-node
validator, and separated the two bracketed dependency citations. No statement or
Lean signature changed.
