## Worker report

The module `Sheaf.Paper.ScalarModelFiniteFlatResolution` states the two clauses of
`lem-sfb-scalar-model-finite-flat-resolution` as
`SheafOfModules.scalarModel_finite_flat_resolution_dvr` and
`SheafOfModules.scalarModel_finite_free_field`. Both proofs are `sorry`. The node's
statement, source and nine proof steps are unchanged. The statement dependency list gains
only the already existing `def-sf-site-constant-module-functor`. ND's landed module
and node record remain unchanged; independent-coefficient helpers are owned by the item. There are no new nodes and no statement correction.

The source was read at main-20261015, sec-proetale-coefficients,
`sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md`, Local models.
Its scalar resolutions, flat scalar extension and tensor calculation agree with this node.
The related `FiniteConstantModelResolution` module is restricted to continuous integral and
rational coefficients on a scheme's pro-etale site, and does not state this general-site
assertion or its derived-tensor clauses. It is therefore not an exact existing attachment.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A site C | `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`. Grothendieck topologies encode the sheaf site, with the recorded covering-site module publicly imported. |
| R a commutative ring | `(R : Type r) [CommRing R]` in the DVR case; `[Field R]` supplies the commutative ring in the field case. |
| R_C its constant ring sheaf | `CategoryTheory.independentConstantRing J R`, literally `(constantSheaf J CommRingCat).obj (CommRingCat.of R)`. |
| B a sheaf of commutative R_C-algebras | `(B : Sheaf J CommRingCat.{r}) (α : independentConstantRing J R ⟶ B)`. A commutative algebra sheaf is exactly this morphism of commutative ring sheaves. |
| P a finitely presented R-module | `(P : ModuleCat.{r} R) [Module.FinitePresentation R P]`. |
| P_C the constant module sheaf | `(commutativeConstantModuleIndependent J R).obj P`, constructed from the constant module presheaf and module sheafification along the actual constant ring unit. |
| M = B tensor over R_C with P_C | `scalarModel R α P` is exactly `changeOfRingsOfUniverses α` of that constant module sheaf. The existing change-of-rings construction sheafifies the sectionwise balanced tensor, retaining the B action. |
| R is a DVR | `[IsDomain R] [IsDiscreteValuationRing R]`, precisely the recorded Mathlib definition of a local PID which is not a field. |
| B is flat as an R_C-module | `hB : IsFlatOnSite ...` of the unit B-module restricted along the underlying ring-sheaf map induced by `α`. This is exactness of tensor with B over R_C, not flatness over B itself. |
| Finite integers m,n >= 0 | `∃ (m n : ℕ)`. No positivity hypothesis is imposed. |
| B^m, B^n | `scalarModelPower (unit ...) m` and `... n`, the existing finite categorical products of the unit module B. |
| Exact 0 -> B^m -> B^n -> M -> 0 | Maps `f`, `g`, a composability equation `h : f ≫ g = 0`, and `(ShortComplex.mk f g h).ShortExact`, including monicity, middle exactness and epicity. |
| The resulting two-term complex | `scalarModelTwoTerm f` abbreviates Mathlib `HomologicalComplex.double f` at indices `(-1 : ℤ), 0`. Its terms are the same finite free terms and its differential is the same `f`, with zero elsewhere. |
| Represents M in the unbounded derived category | A morphism `ε : scalarModelTwoTerm f ⟶ singleFunctor ... 0 ... M` with `QuasiIso ε`. The Q-image of this augmentation is an isomorphism in the recorded unbounded `DerivedCategory`. |
| Tensor computed using K-flat resolutions | `IsKFlatIndependentCoefficients (scalarModelTwoTerm f)` in the DVR case, and K-flatness of `M[0]` in the field case. These augmentations are actual K-flat representatives, not arbitrary assumed resolutions. |
| Every B-module sheaf N | `∀ N : scalarModelModules B` occurs after the single chosen resolution, so the same resolution works for every N. |
| M tensor derived with N | The fixed recorded `siteDerivedTensorIndependentCoefficients J B` applied to `(Q(M[0]), Q(N[0]))`; the order of factors is explicitly M then N. |
| Represented by [N^m -> N^n] in [-1,0] | `em` and `en` identify `(B^m) tensor_B N` and `(B^n) tensor_B N` with the indicated powers. The displayed double differential is `em.inv ≫ (siteSheafTensorRight N).map f ≫ en.hom`, so it comes from the same `f`. The conclusion is an isomorphism with Q of precisely this double complex, not merely the assertion that some complex of these ranks exists. |
| Field case without flatness of B | The second theorem has `[Field R]` and no `hB` or any alternative flatness assumption on B. |
| M is isomorphic to B^r for a finite r >= 0 | `∃ n : ℕ, Nonempty (scalarModel R α P ≅ scalarModelPower (unit ...) n)`. |
| M tensor derived with N is N^r in degree zero | For that same `n`, every N gives an isomorphism to `Q.obj ((singleFunctor ... 0).obj (scalarModelPower N n))`. |

Universes `u`, `v`, `r` and the derived localization universe `w` are independent and
explicitly declared. `EssentiallySmall.{r} C` is the recorded site-smallness convention
for the independent-coefficient unbounded tensor interface. No site object/Hom equality
is imposed. Sheafification and locally-bijective-equivalence instances for RingCat and
CommRingCat are named infrastructure for these same sheafifications; they add no
flatness, geometric or algebraic property. Choosing a common coefficient/module universe
includes arbitrary finitely presented scalar modules; no rank, torsion or cardinality
condition has been added. `HasDerivedCategory.{w}` is the recorded chosen localization
size. Every variable and universe is explicitly bound; no local notation or private
abbreviation is used in the statements.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; sheaves use the generated
  Grothendieck topology, with no restriction to a particular geometric site.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  `SheafOfModules.cochainModulesMonoidal` interface and its public imports, especially
  `changeOfRingsOfUniverses` and `siteSheafTensorRight` in
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`,
  defined by the existing `CategoryTheory.exactFunctor` tensor condition.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its resolution predicate.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, selected by the existing
  resolving-class localization theorem with its representative comparisons. This delivery
  does not choose a new derived tensor.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`: the existing
  `CategoryTheory.siteConstantModulePresheafGeneral` and
  `CategoryTheory.siteConstantModuleFunctorGeneral` remain publicly imported.
  The independent-coefficient helper declarations in the item generalize their explicit
  construction; see the H13 repair below.

The recorded proof dependencies were read and imported as proof imports when separate:
`Module.free_of_finite_type_torsion_free'` in `Mathlib.LinearAlgebra.FreeModule.PID`;
exact presheaf/constant sheafification from Mathlib's functor-category abelian and
sheafification interfaces; `CochainComplex.isKFlat_of_boundedAbove_flat` in
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`;
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients` in
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`; and
`CategoryTheory.kFlatTensorPreservesQuasiIsoIndependentCoefficients` in
`Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients`.
The derived-tensor descent module is public because the statement uses its canonical
functor. The tensor-complex dependency is the existing `CochainComplex.mapBifunctor`,
through the public K-flat/derived-tensor modules. Proof docstrings give all nine steps,
including finite-product compatibility of constant sheafification in the field case.

Edge cases checked before writing and on the completed statements:

- P=0 permits m=n=0, or the empty field basis; products over `Fin 0` give zero modules.
- B=0 and the empty/degenerate sheaf site are permitted; the statements become the zero
  exact sequence and zero tensor calculation. No nontriviality condition is imposed on B.
- For P=R/(pi) over a DVR the expected resolution has m=n=1 and differential pi. The
  tensor calculation gives [N --pi--> N], allowing nonzero degree -1 cohomology.
- Flatness over R_C is necessary in the DVR case: B=R_C/(pi) can kill the injectivity
  of that differential. The field theorem does not accidentally inherit that hypothesis.
- Zero N, rank-zero terms, arbitrary torsion N and arbitrary characteristics are covered.
- The double uses -1 and 0, not 0 and 1. The field result is a single in degree zero.
- The tensor clause quantifies over N after the chosen f; it does not choose different
  resolutions independently for each N.

Searches performed through `msearch.py` (actual results, 2026-10-21):

1. LeanFinder: `A finitely presented scalar module over a DVR gives a finite free
   resolution after flat extension to a sheaf of rings and computes derived tensor`.
   Eight hits: scalar algebra results such as `Module.free_of_flat_of_isLocalRing`,
   `Module.free_of_maximalIdeal_rTensor_injective`, and sheaf finite presentation;
   none states this ringed-site resolution/tensor theorem.
2. Loogle: `Module.FinitePresentation, IsDiscreteValuationRing`. Zero hits.
3. Mathlib grep: `scalarModel|constantModule|finiteFreeResolution`. Five hits, all
   condensed locally constant module namespace occurrences; no exact theorem.
4. LeanFinder: `Constant module functor to sheaves of modules over the constant sheaf
   of rings on a site independent coefficient universe`. Eight hits including
   `SheafOfModules.unit`, `SheafOfModules.toSheaf`, and condensed constant functors;
   no general-site independent-coefficient constant-module functor.
5. Loogle: `CategoryTheory.constantSheaf`. Twelve hits, including `constantSheaf` and
   `constantCommuteCompose`, confirming the ordinary constant-sheaf construction used.
6. Mathlib grep in `Algebra/Category/ModuleCat`:
   `constant.*[Mm]odule|[Mm]odule.*constant`. Zero hits.
7. Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for scalar models, constant
   modules, finite free resolutions and the exact node id. Existing specialized
   `FiniteConstantModelResolution` and constant-module interfaces were opened in full.
   The latter fix coefficients to max u v or identify site universes; the former has
   different coefficient objects and does not include the tensor assertions.
8. Direct rg in Mathlib, both project source trees and `dag/lean_names_upstream.json`
   for every proposed full-name stem (`scalarModelModules`, `scalarModelPower`,
   `scalarModelTwoTerm`, `scalarModel_finite`, `independentConstantRing`,
   `commutativeConstantModuleIndependent`, `siteConstantModulePresheafIndependent`):
   no existing declarations. The original dependency's declaration is retained by
   public import, not shadowed or renamed. The six independent-coefficient declarations
   have moved into the item module in the H13 repair; no new names were added.

Validation: the saved packet passed the requested initial `deliver2.py --no-push`
(commit d548b0fb573), but the independent maintainer's H13 ownership issue still
required the repair below. The revised single delivered file passed `scompile.py`: sandbox
name in 7.9 seconds and actual module name in 13.7 seconds, both clean. The saved Lean
signature matches the item record verbatim; the only changed item fields are `lean` and
the already described additional `stmt_deps` entry. The repaired packet contains exactly
one item node, one Lean module and this report. It is checked again with
`deliver2.py --no-push` before delivery. No global build was run.

No STATEMENT-DISPUTED issue or source statement fault was found.

## H13 repair

The return on immutable head 3881ef0399cf requires preserving ND's landed record for
`def-sf-site-constant-module-functor`, rather than replacing it with a record listing
only the independent-coefficient declarations. I followed its explicit second option:
removed that dependency node file and its separate helper module from the packet, and
moved all six declarations into `Sheaf.Paper.ScalarModelFiniteFlatResolution`:

- `CategoryTheory.siteConstantModulePresheafIndependent`
- `CategoryTheory.siteConstantModuleFunctorIndependent`
- `CategoryTheory.independentConstantRing`
- `CategoryTheory.independentConstantRingUnit`
- `CategoryTheory.independentConstantRingUnit_locallyBijective`
- `CategoryTheory.commutativeConstantModuleIndependent`

All six are now listed in the item's `lean.declarations`, with source docstrings tagged
to this owning item. The original module is publicly imported directly. Its two
exported declarations, file, ND record, and all existing users are untouched. The item
statement and both theorem signatures are unchanged. There are no dependency-node
replacements or additional modules in the repaired packet.

These helpers are needed because the existing dependency functor fixes scalar/module
universes to `max u v`, whereas this item's recorded derived-tensor API permits an
independent coefficient universe `r`. They construct the same constant module presheaf
with identity restrictions, followed by actual module sheafification along the constant
ring unit. The commutative presentation forgets commutativity of the actual constant
commutative ring sheafification. The only helper theorem postponed is local bijectivity
of this specified unit; its docstring explains that forgetting commutativity leaves the
section functions and covering sieves unchanged. All definition data remain explicit.

## Repair self-check by Q11

Read the repaired module against the saved node and current ND dependency record.
The DVR theorem still assumes flatness over the constant scalar ring, asserts a
ShortExact sequence, uses the same -1,0 double complex for its quasi-isomorphism to
M[0] and K-flatness, and chooses its resolution before quantifying over N. Its tensor
differential is still transported from that same resolution. The field theorem still
has no flatness hypothesis and uses the same finite rank in its free-model and
derived-tensor clauses. Zero P, zero B, rank zero, R/(pi), nonflat B in the DVR case,
and independent site/coefficient universes remain covered as described above.
The only change is declaration ownership and import placement: all twelve declarations
are owned by the item, with no replacement of ND's existing two-declaration record.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
