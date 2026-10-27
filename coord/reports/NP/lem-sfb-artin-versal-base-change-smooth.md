## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinVersalBaseChangeSmooth` states
`AlgebraicGeometry.ArtinCriterion.versal_base_change_smooth`. Its only theorem has
proof `sorry`. All four helper definitions have explicit data. The source is
Stacks artin.tex, Tag 0CXM, its parenthetical limit-preserving case, together with
Tag 0CXU's paragraph defining the section i and z_0=i(u_0). I read those two
source passages, the entire item, its nine original statement dependencies and
the recorded declarations. No source or node statement correction is needed.

Hypotheses and clauses correspond as follows.

* The base is Spec Z, in the scheme universe u: the existing `ArtinCriterion.Base`
  is `Spec (.of (ULift.{u} ℤ))`, and `integerScheme` supplies the unique structural
  map. `F : BasedCategory.{v,w} (Over Base.{u})` retains independent total-category
  object and arrow universes, and `hFibred : IsFibredInGroupoids F` means base
  arrows have cartesian lifts and every arrow is strongly cartesian. No stack
  descent hypothesis is added: “on the big fppf site” specifies the underlying
  category, not an extra sheaf condition for F.
* Representability of all Isom presheaves is `hDiagonal : HasAlgebraicSpaceDiagonal
  F`, the landed equivalent scheme-test diagonal criterion. Its witnesses are
  algebraic spaces and equivalences of the full 2-fibre products, retaining arrows.
* The square-zero equivalence for ALL base-algebra diagrams is `hGluing :
  HasSquareZeroGluing F`. It quantifies over `A B B' : CommRingCat.{u}`, both maps,
  surjectivity of `g`, and `(RingHom.ker g.hom)^2 = ⊥`. It uses any scheme-pushout
  presentation of the corresponding affine span. For a surjection this pushout
  is Spec(A times_B B'). For a fibred groupoid, asking that every lifted span
  admit a pushout over this base pushout is precisely effective gluing with
  unique compatible arrows: the base pushout determines a candidate base map,
  and the total pushout determines the unique arrow over that map. Conversely
  an equivalence with the 2-fibre product gives this pushout by cartesian
  pullback of any target. Thus this retains full faithfulness as well as object
  existence. There are NO local, Artinian, finite-type, or residue-field
  restrictions on these diagrams. In particular I did not reuse the narrower
  `ArtinCriterion.RimSchlessinger`, whose interface is only finite-type Artinian.
* Limit preservation is exactly the existing `hLimits : IsLimitPreserving F`,
  the conjunction of `ObjectsDescend`, `ArrowsDescend`, and
  `ArrowEqualitiesDescend` for nonempty directed affine inverse systems. The
  index universe is u, the scheme universe, as required by the project convention.
* U and V are arbitrary `Scheme.{u}` with `hU` and `hV` stating local finite type
  for their unique maps to Spec Z. Families x and y are `BasedFunctor` maps out
  of the representable discrete fibred groupoids. Under 2-Yoneda these are the
  stated objects in F(U), F(V), with no condition on automorphisms. `familyObject`
  evaluates the functor at the identity of its base, giving the actual object
  in `Functor.Fiber F.p (integerScheme U)`; this is real data.
* Scheme finite-type points use the recorded `FiniteTypePoint U u₀`: local
  finite type AND quasi-compactness of `U.fromSpecResidueField u₀`. The field is
  the existing `Scheme.residueField` and not a chosen isomorphic field.
* Versality is `IsVersalAt F U (familyObject x) u₀`. I read its full definition:
  it quantifies over Artinian local A and A', surjective maps to the actual
  residue field with maximal-ideal kernels, a surjective nilpotent-kernel map
  A' to A respecting those maps, a point-reducing `a : Spec A ⟶ U`, objects y,y'
  and actual cartesian arrows b,c. It returns a' and d with both the lifting
  equation and `b.val ≫ d.val = c.val`. This is the prescribed-isomorphism clause,
  not merely existence of some reduction isomorphism. Artinian and local are
  Mathlib's `IsArtinianRing` and `IsLocalRing`, including the stipulated ideal
  chain and unique-maximal-ideal meanings. No coefficient field embedding is
  assumed.
* The leading existentials supply Z, both maps p and q, and a based equivalence
  e with the actual `moduliTwoFiberProduct x y`. This category has objects
  (a,b,alpha) with alpha invertible over the identity of the test scheme; its
  arrows are the compatible pairs of arrows. The two `ModuliTwoIso` clauses
  identify BOTH projections with the specified p and q. Thus Z represents the
  triples functor and is not an unrelated algebraic space or arbitrary map.
* The first conclusion quantifies over EVERY finite-type u₀ with versality,
  then EVERY finite-type z₀ lying over it. `SpaceFiniteTypePoint` literally
  asks for an etale scheme chart e and a closed lift w with `schemePointMap e w
  = z₀`. The “lying over” equation is `mapPoint p z₀ = schemePointMap (𝟙 _) u₀`;
  `mapPoint` and `schemePointMap` are the existing maps on field-valued point
  classes, so it refers to the actual projection.
* `SpaceSmoothNear Z (integerScheme V) q z₀` supplies `O : OpenSubspace Z`,
  membership `z₀ ∈ pointImage O.val.ι`, and smoothness of the induced scheme map
  for every `AlgebraicSpace.IsEtale` chart of O. This is q restricted to an
  open neighbourhood, using the existing open subfunctor inclusion and
  Mathlib `Smooth`, not smoothness merely on a selected chart.
* The specialization quantifies over `j : U ⟶ V` with the existing
  `IsFirstOrderThickening j` (closed immersion, square-zero ideal sheaf) and a
  specified 2-isomorphism `σ : x ≅ (discreteModuliMap (yoneda.map (overMap j))).comp
  y`, namely x isomorphic to j^*y. It supplies i with `i ≫ p = 𝟙 _` and
  `i ≫ q = yoneda.map (overMap j)`. Its additional `ModuliTwoIso` identifies it
  through e with the canonical `moduliTwoFiberLift id j σ`: i is the actual
  induced triple (id,j,σ), not an unspecified section unrelated to σ.
* For EVERY finite-type u₀, including ones where x is not versal, the final
  clause asserts `SpaceFiniteTypePoint Z (schemePointMap i u₀)`. The conditional
  final clause gives `SpaceSmoothNear` when x is versal there. The assertion
  that this point lies over u₀ is already exactly the equation i p=id.

Dependency declarations reused:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
* `Mathlib.AlgebraicGeometry.Sites.Fpqc` and the slice topology interface:
  `Scheme.fppfTopology`, `GrothendieckTopology.over`, as used by AlgebraicSpace.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` and its existing representable scheme tests.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
* `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
* `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`.
* `Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion`: `Base`,
  `integerScheme`, `overMap`, `Object`, `Lift`, `IsLimitPreserving`,
  `FiniteTypePoint`, `IsVersalAt`.
* `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsFibredInGroupoids`,
  `discreteModuli`, `discreteModuliMap`, `HasAlgebraicSpaceDiagonal`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `ModuliTwoIso`.
* `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `moduliTwoFiberLift`.
* `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `moduliTwoFiberSnd`.
* `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`, `schemePointMap`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.

The existing owning definition nodes are added to stmt_deps to cite this landed
vocabulary, as explicitly allowed by brief-stage2 §5. There is no path from the
Artin criterion node back to this item (checked through both dependency kinds),
so this reuse creates no dependency cycle. No dependency is restated or repaired. The Artin criterion theorem is not a statement dependency; a new definition node attaches its already existing predicates.
The four local helpers only unpack clauses this item itself already defines;
they are recorded in `lean.declarations` with source and blueprint docstrings.
They are not independent added mathematical prerequisites.

Proof-only imports follow every currently recorded proof dependency:
FiniteType, Noetherian, ClosedImmersion, Jacobson.Ring,
SmoothFixedResidueArtinianTest, AlgebraicSpaceEtaleOpenImage,
AlgebraicSpaceFibreProductsEtaleCovers, StackChartwiseSmoothEtaleCalculus, and
SmoothEtaleLocalSource. The seven remaining proof nodes have no recorded Lean
interface in the read repository; no statements are invented for proof-only
prerequisites. The entire five-step DAG proof is in the theorem's docstring,
including its precise alpha/theta inverse directions and use of kappa(w), not
an assigned field of the algebraic-space point class.

Edge cases checked: U, V, or Z empty (point assertions are vacuous but no
nonemptiness hypothesis is imposed); zero test algebras in the unrestricted
gluing hypothesis (allowed, without Artinian-local restrictions); A'=A and
kernel zero (allowed in versality and gluing); arbitrary residue characteristic
and mixed-characteristic Artinian rings (surjective residue maps, no coefficient
field embedding); closed lifts with nontrivial residue extension (no
identification of kappa(w) with kappa(z)); non-versal finite-type points in the
section clause (the finite-type conclusion still asserted); non-quasi-compact
U,V and open neighbourhoods (only LOCAL finite type is assumed); independent
fibre universes v,w and point universe u+1 (no equality with u imposed).

Searches for existing definitions/statements, 2026-10-24:

* msearch LeanFinder: “A limit preserving fibred groupoid with representable
  diagonal and versal family has smooth base change at finite type points”.
  Eight hits, headed by `isSmooth_isStableUnderBaseChange`; none deduces
  smoothness from versality.
* msearch Loogle: `"versal", "smooth"`: zero hits.
* msearch grep of Mathlib: `\bversal\b|RimSchlessinger`: three hits, only
  cotangent-complex prose and a weak-limit versal map, not this statement.
* msearch LeanSearch: “Versality for a category fibred in groupoids implies
  smoothness of representable base changes”. Eight smooth/base-change and
  algebra-smoothness hits, no match.
* rg of WeilConjectures for `\b[Vv]ersal|RimSchlessinger`, and the item id:
  no matches. rg of Sheaf for those patterns, `IsLimitPreserving`,
  `FiniteTypePoint`, `mapPoint`, `SpaceSmoothNear`, and `HasSquareZeroGluing`:
  located the reused ArtinCriterion and point-map definitions; no exact theorem
  or unrestricted square-zero gluing predicate. The formal-deformation
  `IsRimSchlessinger` in ArtinDeformationTestCategory is about fixed-residue
  deformation categories, not F on all schemes.
* rg of DAG node files for the same notions found the existing owning nodes
  cited above. The criterion's narrower RimSchlessinger and the curve-only
  ProperCurveFamily.IsVersalAt do not express this item's unrestricted gluing
  and arbitrary fibred-groupoid families. No private copies were made.
* rg of Mathlib, WeilConjectures and Sheaf for all five proposed full declaration
  names found no collision. The unrelated deformation-to-normal-cone
  `familyObject` has a different full name and mathematical notion.

Validation: prescribed scompile.py compiled the sandbox and final library
module successfully, with no errors or warnings. `autoImplicit` is explicitly
false; every universe and variable is bound. The first compile caught a name
collision selecting deprecated scheme IsEtale instead of algebraic-space
chart IsEtale; both chart predicates were fully qualified and the clean compile
repeated. No definitions contain sorry, no theorem was proved, and no
STATEMENT-DISPUTED issue remains. The dry run and final push are recorded below
when complete.


## New nodes

`def-sfb-artin-limit-preservation-versality` attaches the ALREADY EXISTING
`ArtinCriterion.IsLimitPreserving`, `FiniteTypePoint` and `IsVersalAt`, together
with their Base/Object/Lift and descent vocabulary, using `existing: true`.
There is no new Lean module or duplicate definition. Preflight correctly advised
that the reused predicates should be carried by a definition node rather than
adding the Artin-criterion theorem node to statement dependencies. I searched
all definition-node lean records for the three full names: none carried them.
Mathlib LeanSearch, LeanFinder and grep searches are recorded in the new node;
WeilConjectures has no match, while project rg locates precisely the definitions
being reused. Blueprint search “versal” and the DAG definition-node search find
only curve-specific versality and stable-level-chart notions, not this general
definition. Source: artin.tex Tags 07XL and 07XF, both read in full with the
Artinian lifting interpretation immediately following the definition of
versality. The new node asserts neither Artin's criterion nor the present
smoothness theorem. Its existing Lean bodies are exactly the predicates
analysed hypothesis by hypothesis above.

First preflight also caught the typo `def-a1-space-point-classes`; it is repaired
to the landed `def-a1-algebraic-space-point-classes`. No mathematical statement
changed in either repair.

Final validation: deliver2.py --no-push printed `OK (dry run)` for commit
c6704b0dd46: preflight and all per-file compiles passed. The new definition
record includes the empty `import_flags` list required by the current preflight
schema (the brief's historical field list omitted it). The searches in its
`mathlib_searches` retain the raw msearch outputs. Final delivery uses the same
prescribed wrapper and reruns its checks before pushing.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
