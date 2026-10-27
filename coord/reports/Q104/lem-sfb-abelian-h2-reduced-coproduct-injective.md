## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.abelian_h2_reduced_coproduct_injective`
in `Sheaf.AlgebraicGeometry.AbelianH2ReducedCoproductInjective`, with proof `sorry`.
It also supplies the previously missing canonical reduced-coproduct construction in
`Sheaf.AlgebraicGeometry.AbelianAffineReducedCoproduct`, owned by the new definition node
`def-sfb-abelian-affine-reduced-coproduct`. Neither existing module pullback, the existing
scalar pullback, the group law, nor the algebraic-space/site notions are defined again.

The original statement is unchanged. Its hypotheses and clauses correspond as follows:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Locally Noetherian scheme S | `(S : Scheme.{u}) [IsLocallyNoetherian S]` |
| Commutative group algebraic space A over S | `(A : AlgebraicSpace S) (g : CommutativeSpaceGroup A)`; the latter is a natural CommGroup on every functor-of-points value, not an arbitrary multiplication |
| Proper smooth finite presentation and the stated geometric fibres | `hA : Poincare.IsAbelianFamily (groupSpaceProjection A)`; it expands to chartwise smoothness, properness, local finite presentation and HasAbelianFibres. Properness supplies quasi-compactness and separatedness, hence the quasi-separatedness needed to upgrade local finite presentation to finite presentation. HasAbelianFibres quantifies over all algebraically closed fields and geometric maps and retains a representing scheme fibre with `IsAbelianVariety`, i.e. smooth, proper and connected. Over an algebraically closed field connectedness is geometric connectedness; the group law is inherited from g. |
| Proper means separated, finite type, universally closed | `MapIsProper` in the existing `AlgebraicSpaceMorphismProperties`: precisely those three predicates; no projectivity assumption |
| Smooth and finite presentation tested on etale charts | `MapIsLocally (@Smooth)` and `MapIsLocallyOfFinitePresentation`, as used by the existing abelian-family predicate |
| Line module convention | No line module is a parameter or conclusion of this node. The required dependency import `WeilConjectures.AlgebraicGeometry.Modules.Invertible` is retained; the general algebraic-space site has `IsLineModule`. No invertibility hypothesis is imposed on F or N. |
| Any affine S-scheme T=Spec R | `(R : Type u) [CommRing R] (t : Spec (.of R) ⟶ S)`; `Over.mk t` supplies the actual affine parameter, with `Iso.refl _` as its affine-coordinate identification |
| B=A times_S T | `ReducedCoproduct.family A (Over.mk t)`, the existing sheaf fibre product of the structural map and the represented scheme map |
| C=B times_T B | `ReducedCoproduct.square A (Over.mk t)` |
| f and q | `projection` and `squareProjection`; q is defined as p1 followed by f |
| Addition m and projections p1,p2 | `ReducedCoproduct.addition`, `first`, `second`; m pairs actual addition on the A-coordinates with the common T-coordinate, using the two existing fibre-product universal properties |
| Arbitrary R-module N | `(N : ModuleCat.{u} R)` only, with no finite, projective, flat, nonzero, or characteristic condition |
| F=O_B tensor_R N, G=O_C tensor_R N | The two `affineScalarPullback` objects in the source and target of `ReducedCoproduct.map`. This is the existing left adjoint to R-linear compatible sections; its original source construction is sheafification of chartwise O(U) tensor_R N. |
| Cohomology is right derived global sections of underlying additive sheaf | `cohomologyFunctor X n` is `SheafOfModules.toSheaf X.smallStructureRings` followed by Mathlib `Sheaf.functorH`. Mathlib H is Ext from the constant integer sheaf. The small affine etale site is the existing equivalent model of the original small etale ringed topos. No constant finite coefficient sheaf is substituted. |
| Canonical identifications m-star F=p1-star F=p2-star F=G | `coefficientComparison`, uniquely normalized on each pure section 1 tensor n via `CoefficientNormalized`; all three structure triangles are fixed by the actual fibre-product projections |
| The actual additive map D=m-star-p1-star-p2-star | `ReducedCoproduct.map` is literally the difference of those three `coefficientPullback` morphisms; each uses the same N and the same G |
| Injectivity in degree 2 | `Function.Injective (ReducedCoproduct.map ... N)` |
| Nonreduced/non-Noetherian T, every characteristic, N=0 | No hypothesis on Spec R beyond its map to S, no integer invertibility assumption, and no hypothesis on N beyond being an R-module |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, `Modules`, `IsLineModule`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (the contextual line convention).
- `Sheaf.AlgebraicGeometry.RegularGroupSpace`: `CommutativeSpaceGroup`,
  `groupSpaceProjection`, `groupSchemeMap`, `groupSpaceBase`.
- `Sheaf.AlgebraicGeometry.AbelianSpacePoincareData`: `Poincare.IsAbelianFamily`,
  `HasAbelianFibres`, `product`, `fst`, `snd`, `pair`, `addition`, `baseMap_eq`,
  `pullbackUnit`. These are the recorded declarations of
  `def-sfb-abelian-space-poincare-data`, which is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallStructureRings`, `smallModuleEquivalence`, `smallEtaleModelTopology`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`: `smallModuleTensorPullback`.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineScalarPullback`,
  `affineScalarSections`, `affineScalarAdjunction` and its chartwise tensor construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat` and the
  properties expanded by `Poincare.IsAbelianFamily`.
- Mathlib `Sheaf.functorH`, `Abelian.Ext.addEquiv₀` and short-exact-sequence `extClass`
  give the cohomology, degree-zero section evaluation, and connecting maps.

The existing proof-dependency modules are imported without `public`: Mathlib smoothness,
`WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift`, and
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality`.
`lem-sfb-abelian-coherent-exterior-base-change` and
`lem-sfb-projective-cohomology-coefficient-kunneth` currently have no Lean records;
they are proof prerequisites only, not notions needed to type this statement, so there is
no module to import yet. Their full proof steps are retained in the theorem docstring.

Edge cases were checked before writing: the zero ring gives the empty affine parameter
and zero coefficient sheaves; N=0 gives the zero-to-zero map; relative dimension zero or
one makes exterior degree two zero; characteristic two still retains the independent
ordered-basis coordinates e_i tensor e_j for i<j; nonflat N causes no problem because the
antisymmetric map is locally split. T may be nonreduced and non-Noetherian. The source and
coefficient universes are the shared size convention; no object/morphism universe equality
or derived-category localization-size hypothesis is introduced. Every universe and variable
is explicitly bound, with both auto-implicit options disabled.

Searches: msearch LeanFinder queried the full injectivity statement and returned eight
cotangent-complex, scheme, or group-cohomology hits, no match. Loogle query
`"cohomology", "coproduct"` returned 0. Mathlib grep
`AbelianScheme|AbelianVariety|cohomology.*[Cc]oproduct|primitive.*cohomology` returned 0.
The required node-id grep in WeilConjectures returned 0. Searches of both source roots
for reduced-coproduct and coefficient-pullback names found no algebraic-space coherent
version; scheme-only and constant/condensed coefficient maps were inapplicable. The
existing Poincare and affine-section constructions were reused. Additional LeanSearch,
LeanFinder, Mathlib grep, source grep and blueprint searches for the missing construction
are recorded, including exact service output, in the new node's mathlib_searches.

Source reading: opened the current blueprint direct-image unit (the distant ancestor),
Milne AV printed p.55 (PDF p.61), the Stacks ringed-site module/abelian cohomology comparison
(Tag 03FD), flat inverse-image exactness (04JC), tensor pullback (03EL), and cohomology
functoriality (01F8, 01FB). Milne concerns etale finite-adic coefficients; it is used only
for the group-law formula, as the original node explicitly says. The coherent arbitrary-ring
claim rests on the two explicit DAG prerequisites, not on a claimed reading of the WANTED
Mumford--Fogarty--Kirwan proposition.

Validation: scompile.py compiled both delivered modules individually in dependency order,
including their library paths, cleanly with no errors or warnings. All five postponed
named theorems (four construction properties and the item) have proof `sorry` and complete
source/proof docstrings. Definitions have real data; choices are only from uniquely
normalized existence theorems, never from bare existence of an arbitrary map.

No statement dispute or correction is needed. The only item fields changed are lean and
stmt_deps (adding the new construction and the already landed Poincare data node).

## New nodes

`def-sfb-abelian-affine-reduced-coproduct` supplies the actual map that this item needs,
using existing geometric and coefficient constructions. Its statement includes the unique
normalized flat cohomology family, unique coefficient comparison, base-changed addition,
its two structure triangles, flatness of the three maps, and the final difference.
Its module records all 20 declarations. The four postponed properties
`pullbackFamily_existsUnique`, `coefficientComparison_existsUnique`, `triangles`, and
`maps_flat` are expressly clauses of this owning definition node, not untracked theorems.
The first two choices determine their data uniquely. Sources and full proof plans appear
on each declaration. DAG and blueprint searches found no existing definition node for
this common-coefficient reduced coproduct. Mathlib and project searches found its
constituents, which are reused, but no declaration of the map or flat cohomology family.
The new node is in the item's chapter, inherits its unit and blueprint ancestry, and cites
only the existing definition nodes it actually uses.

## Second reading by Q104

I reopened the original node and both completed modules for a second pass; no separate
agent was started, in accordance with this assignment. The maintainer provides the
independent review. The table above was checked against the final signature and the
expansions of IsAbelianFamily, map, cohomologyFunctor and coefficientComparison.

I checked that the coefficient comparison is natural for every N and normalized on the
actual scalar-adjunction unit. It is not an arbitrary isomorphism. The pullback family's
boundary condition uses Ext classes of the underlying additive sheaves, and its degree-zero
normalization quantifies over every global module section. Thus no arbitrary linear map
can replace the geometric cohomology pullback. The difference has m first, then subtracts
p1 and p2, with common target G. The geometry is the original A/S with arbitrary affine T,
not just an abelian variety over a field or an already Noetherian affine base.

The first elaboration pass found unconstrained coefficient universes in functor composition
and missing explicit structure-ring types on 1. These were fixed by specifying the sheaf
cohomology universes and the types of the unit sections; no mathematical hypothesis changed.
Two resulting long lines were wrapped. The final server compile is clean. I also checked
that the published Poincare definitions import only their construction dependencies here;
no downstream Poincare theorem, which uses this item, is imported.
