## Worker report

The module `Sheaf.Paper.EtaleProEtaleScalarPullbackCube` states
`AlgebraicGeometry.ProEtale.etaleProEtale_scalar_pullback_cube`, with one postponed
proof, exactly the requested equality of the two canonical three-arrow composites.
No definition, additional hypothesis, new node, or statement correction is introduced.
The theorem docstring carries all five natural-language proof steps.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Arbitrary schemes X,Y | `{X Y : Scheme.{u}}` |
| Any scheme morphism f:X→Y | `(f : X ⟶ Y)`; no geometric property instances |
| Discrete commutative coefficient rings A,B | `{A B : Type (u + 1)} [CommRing A] [CommRing B]`; fixed-coefficient sheaves, with no topology on the rings |
| Unital ring homomorphism a:A→B | `(a : A →+* B)` |
| Ordinary unbounded D(Y_et,A) and every M | `(M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))`; not a Plus or Bounded subcategory |
| Constant-ring module sheaves | `Sheaf _ (ModuleCat.{u + 1} R)` is the published fixed-R presentation of modules over the constant sheaf R; the same presentation is used on both sites |
| C_Z^R=nu_Z^* | `(comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategory` |
| l_R=f_et,R^* | `L(Etale.upperStar (ModuleCat.{u + 1} R) f)` |
| p_R=f_proet,R^* | `L(upperStar (ModuleCat.{u + 1} R) f)` in namespace ProEtale |
| T_Z^e and T_Z^p | `pbcFixedScalarExtension Z.smallEtaleTopology a` and `pbcFixedScalarExtension (Scheme.ProEt.topology Z) a` |
| d_R:p_R C_Y^R ≅ C_X^R l_R | `directImageComparisonAmbientPullbackIso R f`; its definition is the recorded ordinary site square localized by `mapDerivedCategoryNatIso`, conjugated by the exact/left-derived comparison isomorphisms |
| K-flat-normalized c^e | `Etale.scalarPullbackIso a f`, directly, without replacing it by an arbitrary isomorphism |
| Canonical c^p | `scalarPullbackProEtaleIso a f`, the inverse of the scalar-adjunction mate of the exact restriction/pullback square |
| Canonical delta_Z | `pbcComparisonReduction Z a`, the scalar-adjunction mate of the exact comparison/restriction square |
| delta_X,l_AM ∘ T_X^p(d_A,M) ∘ c^p_C_Y^AM | The left side, in Lean's execution order, is `c^p.hom.app (C_Y^A.obj M) ≫ T_X^p.map (d_A.hom.app M) ≫ delta_X.hom.app (l_A.obj M)` |
| C_X^B(c^e_M) ∘ d_B,T_Y^eM ∘ p_B(delta_Y,M) | The right side is `p_B.map (delta_Y.hom.app M) ≫ d_B.hom.app (T_Y^e.obj M) ≫ C_X^B.map (c^e.hom.app M)` |
| Both paths have the specified endpoints | Lean checks equality in the same Hom type, from `p_B.obj (T_Y^p.obj (C_Y^A.obj M))` to `C_X^B.obj (T_X^e.obj (l_A.obj M))`; no casts or endpoint assumptions |
| No qc, qs, boundedness, coefficient flatness | None of these occur among the binders or inferred theorem parameters |

The coefficient universe is the existing `Type (u+1)` convention of the fixed-ring
small-site API. The small sites retain their original object/morphism universes;
there is no equality assumption forcing those universes together.

Dependency declarations read and used (including their full signatures and docstrings):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its morphisms.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`, the sheafification of the constant presheaf.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`
  and `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the underlying category is written
  explicitly in the M binder).
- `def-kun-projection-formula-map`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`,
  `rightDerivedLowerStarProjectionMap` and its canonical derived inverse-image
  functor `L(Etale.upperStar ...)`; no projection map is asserted invertible.
- `def-pur-etale-scalar-pullback-iso`: `Sheaf.Paper.PurEtaleScalarMateProjection`,
  `AlgebraicGeometry.Etale.scalarPullbackIso`; its existence/uniqueness statement
  specifies the representative-counit normalization.
- `def-weil-pbc-site-comparison-morphism`:
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparison`; its coefficient inverse image is the existing
  `comparisonUpperStar` used in the statement.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `Scheme.proEtaleConstantRingDerivedPullback` (intrinsic presentation); the fixed-ring
  presentation here uses the existing `ProEtale.upperStar` and its left-derived
  functor as in the published scalar-mate interfaces, for arbitrary rings.
- `sk-thm-pe-direct-image-comparison`:
  `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`, `ProEtale.directImageComparison`;
  its unconditional inverse-image square is exactly the localized square used by
  `directImageComparisonAmbientPullbackIso`, not its later qcqs direct-image clause.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`; the fixed-coefficient scalar functor
  used here is the already-published `pbcFixedScalarExtension` from
  `Sheaf.Paper.WitnessCompatibility`, fixed by actual derived restriction adjunction.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`:
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its specialized scalar face is the existing `scalarPullbackProEtaleIso`, and
  the comparison-site face is `pbcComparisonReduction`.
- `lem-sfb-ringed-derived-monoidal-comparisons`:
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons` and
  the publicly reexported `System` with its normalized composition and 2-iso data.

The canonical helper declarations `scalarPullbackProEtaleIso` and
`directImageComparisonAmbientPullbackIso` are already recorded in
`lem-sfb-etale-proetale-scalar-mate.lean.declarations`; their source module is
`Sheaf.Paper.EtaleProEtaleScalarMate`. They specialize the current node's recorded
ringed-pullback and site-square dependencies, and are reused directly. The present
statement does not assume or use the scalar-mate theorem. Since that downstream
node lists this cube as a proof dependency, the maintainer must OMIT adding a
proof-only import of this cube into `EtaleProEtaleScalarMate`: it would close an
import cycle, the explicit exception in stages/2-statements.md section 3 rule 7.
No DAG dependency on the downstream theorem is introduced. Future relocation of
those existing helper definitions can remove this file-level organization issue.

All already-stated proof dependencies are imported, directly or through public
statement imports; the K-flat-resolution, ordinary tensor-comparison, tensor-construction,
module-sheafification, cochain-tensor and derived-pullback modules are also direct
proof-only imports. There is no added proof dependency.

Edge cases checked before writing and again after compilation:

- Identity f: d_R is the canonical identity normalization, and the comparison
  faces have their identity normalizations; no nonidentity assumption appears.
- Identity a and the zero ring: all six canonical maps exist; a ring map into
  the zero ring and zero objects are allowed. There is no nontriviality instance.
- Empty schemes: the small-site and fixed-coefficient functors remain defined;
  no points, nonemptiness, finite covers, or chosen affine charts are required.
- Nonflat a, for example Z→Z/2: the scalar functors are derived, and the
  representative argument uses flatness of the resolution, not of B over A.
- Unbounded M and non-qcqs f: no cohomological bound or geometric finiteness
  hypothesis is inferred in this theorem. In particular it uses no invertibility
  result about the direct-image comparison.
- The order of each three-arrow composite matches the displayed equation; the
  intermediate categories switch coefficients exactly once, and all final maps
  are B-linear morphisms in the pro-etale derived module category on X.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Canonical derived scalar extension commutes with the
  etale proetale inverse image square for unbounded module complexes"`: 8 hits,
  on KaehlerDifferential/FormallyEtale and etale algebras; none states this cube.
- `msearch.py ... loogle "SheafOfModules.pullbackComp"`: 5 hits, on ordinary
  module pullback composition and its identity/associativity coherence, not this
  derived scalar/site cube.
- `msearch.py ... grep "(scalar|tensor).*(proetale|ProEtale)|(proetale|ProEtale).*(scalar|tensor)"`:
  zero Mathlib hits.
- `rg` over `lean/WeilConjectures` for the item id and scalar/cube combinations:
  no matching item or exact cube theorem.
- `rg` over `lean/Sheaf` by concept found the reused scalar-mate helpers and
  `Scheme.proEtaleConstantScalarPullback_cube`. The latter is a Cartesian square
  of four schemes on the pro-etale site, not the etale/pro-etale comparison
  square; it cannot serve as an existing binding of this node.
- Read Stacks `sites-cohomology.tex`, label `lemma-derived-pullback-composition`
  (Tag 0D6D) and its proof, and the adjacent tensor-pullback lemma. They compute
  all iterated derived pullbacks on one K-flat flat-term representative.

Validation: the statement compiled cleanly in sandbox and library-module modes
using `scompile.py` (6.2 s and 6.4 s for the first clean version). All universes
and binders are explicit, `autoImplicit` is false, and the only proof is `sorry`.
No STATEMENT-DISPUTED or mathematical node fault was found.

## Second reading by NB

A separate second pass by the same worker was performed with the original node
and the completed Lean signature open. This dispatcher brief prohibits starting
other agents; independent review is supplied by the maintainer after delivery.
The pass checked every row of the correspondence table against the actual
signature and verified the published definitions of all six faces. The first
ordinary-scalar import name was corrected to its actual owning modules before
clean compilation. No mismatch in the mathematical statement was found.
In particular the final etale face uses `Etale.scalarPullbackIso` itself, the d
faces use the unconditional inverse-image square, and neither the boundedness
nor qcqs hypotheses of the downstream scalar-mate theorem enter the signature.
The only organizational caveat is the explicitly documented proof-import cycle
exception for the module housing the already-published helper definitions.
