## Worker report

The module `Sheaf.AlgebraicGeometry.LCICurveFundamentalClass` states
`AlgebraicGeometry.existsUnique_lciCurveFundamentalClass`. Its only theorem proof is
`sorry`. The three helper predicates and the explicit codimension-sign function have complete
data and express the normalization and compatibility clauses of this same node.
The returned H3/H13 faults are repaired in the same owning dependency module,
`Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`, supplied with its dependency
node record. Every theorem proof remains `sorry`; definitions contain real data.

The live Q20 delivery was a stage-1 split, reviewed PASS at 04:37 UTC on 2026-10-22.
It had no `lean` record. This delivery preserves its entire statement and proof and
supplies its stage-2 interface. The mathematical statement is retained, including its convention-dependent sign.
This is the repair of returned immutable head 754bdaac2207. The retained packet
was inspected first, and the required initial dry run passed as 0a2af565755; that
mechanical pass did not repair the two mathematical faults, so the work below
changes the dependency normalization and makes the resulting explicit sign visible.

Hypotheses, one by one:

- Schemes and morphism: `{X S : Scheme.{u}} (p : X ⟶ S)`, with every universe and
  variable explicit. No smaller universe of test schemes is imposed.
- Noetherian base: `[IsNoetherian S]`. Its actual Mathlib declaration extends both
  `IsLocallyNoetherian S` and `CompactSpace S`, exactly the two clauses of the node.
- Flatness: `[Flat p]`, the recorded class, equivalent to flat stalk maps.
- Finite presentation: `[LocallyOfFinitePresentation p] [QuasiCompact p]
  [QuasiSeparated p]`, retaining all three conditions and no separatedness assumption.
- Nonempty geometric fibres pure of dimension one:
  `hpure : HasPureFlatLCIGeometricFibres p 1`. This dependency predicate quantifies
  over every irreducible component of the pullback along the algebraic closure of
  each residue field and sets `topologicalKrullDim Z = 1`. Empty fibres are allowed;
  their absence of irreducible components makes the condition vacuous. No
  surjectivity assumption is added.
- Cover by actual regular affine polynomial presentations:
  `hcharts : ∀ x : X, ∃ A : NodalCanonicalPresentation p, x ∈ A.U.1`. Despite its
  historical name, this structure has no nodality assumption. It contains affine
  source and base opens, the actual coefficient map of p, a surjective polynomial
  map in c+1 variables, c ordered regular equations, and equality of its kernel with
  their generated ideal. Thus it is exactly the regular curve presentation in this
  node, with no choice of an arbitrary algebra structure or quotient.
- The specified adjunction line with its canonical comparisons is the argument
  `F : FlatLCIAdjunctionSystem p 1` together with `hF : F.IsNormalized`, using the
  full recorded dependency interface, not a replacement line bundle. The original
  line is `F.line (FlatLCIBaseChange.identity p)`. This is the node's instruction
  "Let K be ... with its canonical presentation comparisons", rather than an
  additional hypothesis about p. Existence is the cited adjunction theorem.

Conclusion, clause by clause:

- `∃! α : ∀ B : FlatLCIBaseChange p, B.p'.relativeDifferentials ⟶ F.line B` gives the
  sheaf-module morphism for the original family and simultaneously for every
  cartesian change of base. Identity base change is explicitly part of that type.
- `F.IsCurveFundamentalClass α` quantifies over *every* presentation C on *every*
  open U of *every* base-changed family. It is not limited to the covering charts.
  `FlatLCIPresentation` is the adjunction dependency's intrinsic conormal model.
  An affine polynomial presentation in hcharts supplies such a model; its
  conormal module is the actual pulled-back immersion ideal and its ambient
  differential module is the actual pulled-back relative differential sheaf.
- For every such chart there is a map `αU` to the restriction of `F.line B`.
  Its first equation says exactly that it is the restriction of the global map:
  on d(a), its value is `tensorPullbackSection U.ι ... (α B (d a))`. These
  equations use the specified tensor-section operation of the adjunction
  dependency. They determine the restriction by generation by differentials.
  Therefore local maps on arbitrary intersections are restrictions of the same
  morphism. The statement nowhere assumes that these intersections are affine.
- For *every* δ and β satisfying the dependency's normalized
  `IsConormalDifferential` and `IsSourceDifferentialMap`, the local map satisfies
  `IsCurveCofactorMap` and `IsCurveJacobianMap`. These maps are characterized on
  actual ideal sections and universal derivations, not arbitrary parameters.
  `hF` includes their unique existence, so the universal quantification is not
  vacuous.
- `IsCurveCofactorMap` writes the full source wedge formula: for a conormal basis
  a and its normalized dual top-wedge section ρ, the image of β(v) is
  `F.localIso` applied to `ρ ⊗ (δ(a₁) ∧ ... ∧ δ(a_c) ∧ v)`.
  `Fin.cast C.rank_eq` transports the n=c+1 rank identity explicitly.
- `IsCurveJacobianMap` also states the scalar determinant formula. Given a
  conormal basis a and an ambient basis b, it produces a linear trivialization
  e₀ whose value on the *specified* image of `ρ ⊗ wedge b` is 1, and asserts
  `e₀ (αU (β v)) = M.det` for the coefficient matrix whose first c rows are
  δ(a_i) and whose last row is v. This is a fixed orientation condition, not
  just an existential generator that can vary by an arbitrary unit.
  In the affine presentation of the node, take a_i=[f_i], b_j=dx_j and v=da.
  The dependency's conormal/source normalization makes the matrix entries
  precisely the images of ∂f_i/∂x_j and ∂a/∂x_j. Thus `M.det` is exactly the
  augmented Jacobian determinant after reduction in B. The coefficient ring
  `Γ(U.toScheme,O)` identifies canonically with B on the whole affine chart;
  these are the same sections via the open-immersion section isomorphism.
  The formula is given in coordinates of the actual conormal model, avoiding a
  second private construction of conormal or differential modules.
- The sign is explicitly `flatLCICurveFundamentalSign C.c`, defined to be the
  integer +1 under the repaired kernel-first convention. Both the cofactor value
  and the scalar Jacobian formula include this sign by integer scalar action.
  Thus `e = ε_c e₀` gives the node's signed formula (ε_c squared is one).
  This value is forced by the repaired smooth determinant comparison: the
  negative conormal cone inclusion gives (-1)^c, and the missing rank factor
  now supplied gives another (-1)^c, so they cancel. The return's f=y example
  is checked explicitly below. This is the explicit-sign option requested by
  the return, using the repaired convention, rather than the inconsistent old one.
- Uniqueness in the outer `∃!` states that the local descriptions determine the
  map. Although the formulas are also expressed for arbitrary conormal and
  ambient bases, this is the equivalent basis-independent formulation of the
  polynomial Jacobian rule, not an additional hypothesis or a different map:
  polynomial differential generators span locally and linearity determines
  the rule on all lifts; basis changes cancel in the dual-conormal tensor.
- The second conjunct is, for each base-changed family and point x,
  `IsIso ((RingedSpace.moduleStalkFunctor ... x).map (α B)) ↔
  ∃ U, x ∈ U ∧ Smooth (U.ι ≫ B.p')`. This states *exactly* the smooth locus,
  including the converse, using the neighborhood definition of smoothness at
  a point. No assumption of generic smoothness or reducedness is made.
- The last conjunct gives arbitrary base-change compatibility on universal
  differential generators. For every cartesian g,b between any two B,D, it
  equates the canonical `F.baseChange` applied to the pullback of α_B(da)
  with α_D(d(g♯a)). Pure tensors and differentials generate, so this is the
  canonical comparison square on the whole differential module. It supplies
  the identity and every iterated base-change case; F's own comparisons obey
  its identity and composition laws. No Noetherian or flat condition is
  imposed on the changed base or b. Isomorphisms of S-schemes are included
  among these cartesian squares with b the identity. Open restrictions are
  the αU equations and the wedge formula on every open O in each chart.
- No properness, nodal, marking, positivity, or reconstruction clause is added.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian`, `IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (included in IsNoetherian).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`, also
  recorded by def-weil-finite-type-morphism.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential` and its derivation,
  used by the recorded sheaf-of-differentials construction.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`.
- `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`: `FlatLCIPresentation`,
  `.conormal`, `.differentials`, `.line`, `.IsConormalDifferential`,
  `.IsSourceDifferentialMap`, `FlatLCIBaseChange`, `.identity`,
  `HasPureFlatLCIGeometricFibres`, `FlatLCIAdjunctionSystem`, `.localIso`,
  `.baseChange`, `.IsNormalized`.
- `Sheaf.AlgebraicGeometry.NodalDualizingDatum`: `NodalCanonicalPresentation`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`:
  `Scheme.Modules.exteriorSheaf` and `exteriorSheafSection`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`.
- `Scheme.Modules.tensorPullbackSection` and `tmulSection` from the actual
  tensor-section interfaces publicly reexported by the adjunction module.

The three already-landed definition nodes for affine regular presentations, exterior
sheaves, and module stalks are retained in stmt_deps. No new nodes are needed.
The adjunction dependency module is repaired under §1(B), as required by the return. Proof-only imports include the recorded determinant theorem, the
regular-sequence conormal and Koszul theorems, and standard-smooth implies smooth.
The three proof dependencies without Lean records (the cofactor naturality lemma,
adjunction normalization lemma, and cotangent presentation lemma) are not imported;
this stage only requires proof imports that have been stated. They are not missing
notions needed to type this statement.

Edge cases checked mathematically:

- c=0: the conormal wedge is empty, the augmented matrix is 1 by 1, and its
  determinant is the derivative coefficient. `Fin.snoc` includes this case.
- Empty X, empty opens and empty geometric fibres: no nonemptiness or
  surjectivity is assumed. Trivializations over the zero section ring are the
  unique equivalences of zero modules; all equations retain their meaning.
- Singular or everywhere singular curves: the cofactor can vanish; no density
  of the smooth locus or injectivity of the conormal differential is imposed.
  For example a characteristic-p equation x^p has zero corresponding derivative,
  consistent with the non-smooth locus and the failure of an isomorphism there.
- Characteristic two: +1 and -1 coincide. Over Q, the repaired transitions and
  cofactor maps also agree, so no characteristic-two vacuity remains.
- Nonseparated X: all comparisons are sheaf restrictions; no affine-intersection
  or separatedness assumption is used.
- Arbitrary, nonflat and non-Noetherian base change: B and every cartesian map
  between B,D are unrestricted. The source proof uses flatness of p, not of b.
- Identity changes and arbitrary isomorphic cartesian lifts are included by the
  all-B quantifier and the last equation, rather than only literal pullback objects.

Searches made (actual wrapper results):

- leanfinder: "canonical fundamental class from relative Kahler differentials to
  the adjunction determinant line for a flat local complete intersection curve".
  Eight hits, including `Algebra.IsStandardSmooth.of_basis_kaehlerDifferential`,
  `Algebra.Generators.toKaehler_cotangentSpaceBasis`,
  `Algebra.Generators.cotangentCompAwaySec`, `KaehlerDifferential.DLinearMap_apply`,
  `Algebra.Generators.toKaehler_tmul_D`, `Algebra.Extension.toKaehler`,
  `Algebra.IsStandardSmooth.free_kaehlerDifferential`, and
  `KaehlerDifferential.D_apply`. They give algebraic differential constructions,
  not a global fundamental class with the specified adjunction comparisons.
- loogle: "KaehlerDifferential, ExteriorAlgebra,
  Algebra.PreSubmersivePresentation.jacobian". OK, zero hits.
- Mathlib grep through msearch: "fundamentalClass|fundamental.class|adjunction.*line"
  in AlgebraicGeometry. OK, zero hits.
- rg of the project's Sheaf and WeilConjectures trees for fundamentalClass,
  fundamental class, canonicalAdjunction, and lci curve found the actual
  adjunction module and `NodalDualizingDatum`. The latter *defines* a datum
  that already includes a fundamental-class map but proves no existence and
  does not state compatibility with the specified adjunction line. Its affine
  presentation structure is reused. The other fundamental classes concern
  etale cohomology and regular-immersion cohomological classes, different objects.
- The required item-id search in WeilConjectures returned no match. Searching
  all three new helper names and the main theorem name in Mathlib, Sheaf and
  WeilConjectures returned no collisions.

Sources read: the item's complete live statement and eight-step proof; every
statement dependency's record and its used source declaration; the entire
FlatLCICanonicalAdjunction and NodalDualizingDatum modules; the actual relative
Kahler sheaf/derivation definitions; the exteriorSheaf and exteriorSheafSection
constructions; the module stalk functor; Stacks duality.tex, lemma-determinant
and lemma-fundamental-class-lci, including the displayed wedge construction and
the invertible-Jacobian converse.

No STATEMENT-DISPUTED issue or statement correction is needed: the item already
allows the sign fixed by the canonical comparison convention. The dependency's
mathematical node statement is unchanged. Its old Lean comparison did not implement
that statement and is repaired under §1(B).

## Dependency modules

`lem-trf-flat-lci-canonical-adjunction`, owned by
`Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`, is supplied in this packet.
Only its `lean` record changes; it has the required `lean.note`. The previous
`IsFlatLCIDeterminantComparison` omitted a rank sign. Hence its comparisons did
not compose, although the mathematical node explicitly requires the cocycle
condition. Since `localIso` transitions compose by cancellation, `IsNormalized`
was impossible over Q, and the existence theorem was inconsistent. The repaired
module retains every original notion and declaration and states exactly the
adjunction node, with the composition-compatible kernel-first determinant formula.
No new private definition or alternative line is used. The theorem signature and
its hypotheses, Ext and derived-duality clauses, arbitrary base changes and smooth
comparison remain the same. The full nine-step proof docstring is retained, with
the cone step explaining the rank correction. The signature in the node record
is now copied verbatim, including line breaks.

## Return repairs

1. H3/H13, composition and nonvacuity. In the original notation, A,B have ranks
   a,b and V,W ranks n,m, with a+m=b+n. The exact cone is
   `0 → A → B ⊕ V → W → 0`, maps `(f,-dA)` and `(dB,g)`.
   If M has the injection columns followed by lifted W columns, the repaired
   equation is
   `det(M) • e(A∨ ⊗ V) = (-1)^(a*(b+1)) • (B∨ ⊗ W)`.
   This follows from the source's actual kernel-first determinant functor,
   not from demanding that a naive cone orientation compose. Namely take
   T=[A⊕B → V⊕B], differential `(dA,id)`. Its projections to the source and
   target complexes are degreewise surjective quasi-isomorphisms. The source
   kernel is [B --id--> B]. Moving its bases before A and V gives determinant
   `(-1)^(b*(a+n))`. The target kernel has degree-minus-one basis `(a,-f(a))`
   and degree-zero basis `(dA(a),-f(a))`. Its quotient lifts are the columns
   of M with the rows swapped from `(B,V)` to `(V,B)`. Negating the first a
   columns and swapping those row blocks gives determinant
   `(-1)^(b*n+a)*det(M)`. The degree-minus-one kernel-plus-quotient determinant
   is one. The ratio of the two normalized surjections is therefore
   `(-1)^(b*(a+n)+b*n+a)/det(M) = (-1)^(a*(b+1))/det(M)`.
   Thus the formula is exactly a functorial determinant comparison and composes.
   For the identity, a=b and the exponent a*(a+1) is even. For an acyclic
   [E --id--> E] to zero, det(M)=(-1)^a and the correction is (-1)^a,
   giving evaluation in every rank, including zero. Appending r equations
   and variables gives det(M)=(-1)^(n*r), corrected orientation multiplier
   `(-1)^(a*(a+r+1)+n*r)=(-1)^((n-a)*r)`. Its exponent is additive in r,
   so the review's one-step/two-step contradiction disappears. In the A1/Q
   test the old transitions were -1,+1 with direct +1; they are now -1,-1
   with direct +1.

2. H3, sign and existence. Under this repaired convention the explicit forced
   sign is ε_c=+1. This is now a public, real-data sign function in the item's
   own module, and both local predicates apply it at C.c. To check it rather
   than assume it, on a smooth conormal sequence compare [C→V] to [0→Ω].
   The exact cone's first c columns are -δ(a_i), giving (-1)^c compared with
   the conormal-first wedge. The new rank factor is also (-1)^c. Hence
   `IsSmoothComparison` sends the displayed positive conormal-first orientation
   to the positive differential wedge, exactly as it says. For f=y on the
   x-line with ambient basis (dx,dy), w_C(dx)=-orientation_C. Add t, with
   equations (y,t) and ambient basis (dx,dy,dt): w_D(dx)=+orientation_D.
   The corrected transition carries orientation_C to -orientation_D, so
   it carries w_C(dx) to w_D(dx). More generally, appending r variables
   changes both transition and cofactor orientations by (-1)^r. Thus the
   all-c positive sign now glues under the *repaired* convention. It is not
   the positive sign claimed for the old uncorrected comparison.

Sources reopened for this calculation: `literature/stacks-project/more-algebra.tex`,
section on determinants of two-term complexes, especially the kernel-first
surjection construction before `lemma-canonical-element-well-defined`,
`lemma-compose-surjections`, and `lemma-determinant-two-term-complexes` (0FJM);
`literature/stacks-project/duality.tex`, `lemma-determinant` (0E9Y), displayed
conormal-first wedge, and `lemma-fundamental-class-lci` (0E9Z). These are present
locally, so no web copy was needed.

The arithmetic was checked independently by a Python exact-rational elimination
script: 80 explicit cone/mapping-cylinder matrix comparisons (a=0..4, d=0..3,
r=0..3), and 1440 two-stage stabilization compositions (a=0..7, d=0..4,
r,t=0..5). All passed. The first attempted checker imported unavailable sympy;
it was replaced by ordinary Python `fractions.Fraction` elimination, with no
installation or tool modification. The small-case checks are evidence for the
calculations above; the derivation through normalized surjections is the reason
the convention works generally, including zero divisors and noninjective δ.

## Consumer audit

The current live source was read through both the local read-only checkout and
`scompile.py --source Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`.
The latter still contained the returned uncorrected formula, so this delivery
repairs that current owning module rather than restoring a stale private copy.
The retained item's source and node record were compared with current main;
the same hypotheses and clauses are retained, including the three already-used
landed definition dependencies.

- `FlatLCIAdjunctionSystem.IsSmoothComparison` stays conormal-first and unsigned.
  The smooth-projection calculation above proves that it is now compatible with
  the rank-corrected determinant comparisons in every c,d. This includes c=0,
  d=0, the empty wedge, and empty opens. The existence theorem's smooth clause
  can therefore hold simultaneously with its repaired IsNormalized clause.
- `NodalNormalizationAdjunction.lean`: its predicate
  `IsNodalNormalizationAdjunctionComparison` and theorem
  `nodal_normalization_adjunction` use the smooth comparison on actual universal
  differential sections, followed by the canonical divisor section. They contain
  no hard-coded cone-rank sign. Since the repaired convention retains that
  positive smooth comparison, they require no edits. On xy=0 the familiar
  branch generators du/u and -dv/v differ by a unit, including characteristic 2;
  the extension and its uniquely specified generic value are preserved.
- `FormalPlaneAdjunctionLattice.lean`: `IsFormalPlaneGenericComparison` normalizes
  q by the same smooth map on universal differentials. Its theorem specifies
  the image lattice, not the value of an unnormalized formal conormal generator.
  Its proof explicitly uses ε=-f∨⊗(dx∧dy). For f=y the raw conormal-first wedge
  sends dx to -orientation, so its inverse sends -orientation to dx. In general
  that same ε maps to dx/f_y or -dy/f_x, exactly the two residue definitions.
  Thus its normalization, lattice equalities, and parameter transport are
  unchanged. No modification of this consumer is necessary.

Consumer validation uses scompile.py with the repaired dependency, the item,
`FormalPlaneAdjunctionLattice.lean`, and `NodalNormalizationAdjunction.lean` in
one private dependency-ordered packet. The two consumer files are read directly
from the read-only checkout and are not delivered or modified.

## Second reading by NE

This is an in-session second reading, not a claim of independent-agent review:
the dispatcher explicitly forbids starting other agents, and the maintainer
performs the independent review. Reopened the corrected dependency formula,
its mapping-cylinder derivation, the item predicates and the mathematical node.
The same schemes, arbitrary cartesian base changes, finite-presentation classes,
purity predicate and actual presentation cover occur. The wedge and scalar
matrix formulas now visibly apply the codimension sign. Their orientation is
fixed by e₀(orientation)=1, so no arbitrary unit is introduced. Restriction uses
tensorPullbackSection on universal differential generators; smoothness is still
an iff on every stalk, and arbitrary base change is still the full comparison
equation. c=0, empty schemes/opens/fibres, singular δ, characteristic 2, arbitrary
nonflat base changes, all cartesian lifts, and scheme universe u remain included.
The only defects found in the saved packet were the two returned sign issues;
they are repaired as detailed above. The original node statement already allows
the explicit sign forced by the repaired convention, so no node correction or
citer statement edit is appropriate.

## Validation

Initial saved-packet dry run: OK, temporary commit 0a2af565755. This was followed
by actual source changes repairing both numbered points, not an unchanged push.
Final compilation, consumer validation, and delivery checks are recorded below.

Final scompile.py packet passed with exit code 0 and no warnings or errors for
all four modules, including both sandbox and actual library module forms. The
reported library compilations were: FlatLCICanonicalAdjunction 26.2 s,
LCICurveFundamentalClass 5.9 s, FormalPlaneAdjunctionLattice 12.4 s, and
NodalNormalizationAdjunction 11.0 s. The private overlay compiled the repaired
dependency before either consumer. Only the two owning delivery modules and
the two corresponding node records are included in the delivery. JSON comparison
with the read-only base confirms that the dependency changes only `lean`; the
item changes only `lean` and the retained three landed `stmt_deps` additions.
Both stored signatures match their files verbatim; both files have lines of
at most 100 characters.

Final repaired-packet dry run: OK, temporary commit 871bfc3daac. The server
preflight and both per-file compilations passed, with the dependency node and
module included in the staged set.
