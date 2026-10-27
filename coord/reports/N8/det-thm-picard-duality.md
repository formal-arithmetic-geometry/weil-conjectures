## Worker report

This is an existing-declaration attachment, with no new Lean module. The item's
statement and ordered stmt_deps are byte-identical to those of the independently
reviewed sk-thm-picard-duality. I read its recorded source module
`lean/Sheaf/AlgebraicGeometry/Curve/PicardDuality.lean` in full, including all
signatures, definitions and proof docstrings. The ten declarations in that node's
record jointly express this same statement. The new lean record reuses all ten,
with `AlgebraicGeometry.Scheme.picard_duality_one` as its primary declaration.
The statement field is extracted verbatim from that theorem's source signature,
retaining newlines. Existing helper definitions are reused without copying them.
Only the item's lean field changes.

Source checked: the latest blueprint
`literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-rr/det-thm-picard-duality.md`
and its `.proof.md`, the current item and sk-thm-picard-duality, and the latter's
stage-2 review. The accepted node explicitly adds disconnected/empty trace
conventions to the blueprint; those are already present in the existing Lean.
No statement correction, dependency repair, new node or disputed statement is needed.

Hypothesis and clause correspondence (all module-local names below are in
`AlgebraicGeometry.Scheme`, with the helper definitions in `.Modules`):

1. The field is `{k : Type u} [Field k]`, and the scheme over it is
   `{X : Scheme.{u}} [X.Over (Spec (.of k))]`. The structure map is
   `X ↘ Spec (.of k)`. There is no perfectness, algebraic-closedness,
   geometric-connectedness or global-sections-equal-k assumption in either
   general duality theorem.
2. Smooth proper pure dimension n in {0,1} is expressed by the exhaustive two
   theorems `picard_duality_zero` and `picard_duality_one`, with respectively
   `[SmoothOfRelativeDimension 0 ...]` and `[SmoothOfRelativeDimension 1 ...]`,
   and `[IsProper ...]`. Over a field this is smoothness of the stated pure
   dimension; properness supplies separatedness and finite type. Neither theorem
   requires nonemptiness or integrality of X. There is no hidden restriction to
   connected curves. The empty scheme is admitted in either pure-dimension case.
3. F is quantified in `IsPicardTraceDuality` as `(F : X.Modules)
   [F.IsFiniteLocallyFree]`, the recorded variable-rank, finite locally free
   notion. F may be zero and its rank may differ across components.
4. The canonical module is `SheafOfModules.unit X.ringCatSheaf` for n=0 and
   `(X ↘ Spec (.of k)).relativeDifferentials` for n=1. These are exactly
   Omega^0=O_X and Omega^1; no substitute dualizing object is introduced.
5. `scalarCohomology` is the recorded module-derived cohomology with scalars
   restricted to k. `picardCohomologyZ` extends it to q:Z, using the zero module
   `ModuleCat.of k PUnit` for negative degrees. `picardCohomologyZMap` extends
   its actual coefficient maps by zero. All integer degrees are quantified.
6. For n=0, `picard_duality_zero` supplies a functional t and pins its value on
   every z to `Algebra.trace k Γ(X, ⊤)` applied through
   `scalarGlobalSectionsEquiv`. The algebra structure is explicitly
   `(globalSectionsRingHom k (X := X)).toAlgebra`. Smooth proper dimension zero
   identifies X with Spec of this finite etale global algebra, so this is the
   specified finite etale trace, without choosing an affine presentation.
7. For n=1, `picard_duality_one` supplies t and normalizes it on every finite
   disjoint integral-component presentation. `(I : Type u) [Fintype I]`,
   `(Y : I → Scheme.{u})`, integral/smooth-proper dimension-one component
   instances, open immersions `j`, commutation `h`, and
   `_hc : IsColimit (Cofan.mk X j)` encode exactly such presentations. The
   hypotheses on components occur inside the normalization conclusion, not
   as extra hypotheses on X. Smooth proper curves have a finite such
   decomposition. The compatible function-field algebra instances are just
   the structure scalars on their actual generic stalks.
8. Its formula `t z = ∑ i, residueTrace k (Y i) (...)` uses the canonical
   `picardDifferentialCohomologyPullback` and the recorded
   `moduleCohomologyExtResolutionEquiv`. The latter identifies module-derived
   cohomology with the abelian-sheaf cohomology on which residueTrace was
   constructed, using the specified common-resolution composite. Thus this
   does not replace the trace by an arbitrary equivalence or a choice.
   For integral X, the singleton presentation gives its own residue trace;
   finite decompositions give the component sum; the empty cofan forces t=0.
9. The residue sequence and cokernel are the recorded principal-parts
   constructions. I read `finiteLocallyFree_principalParts_resolution` and
   `finiteLocallyFree_principalParts_differentials`, and the definition and
   formulas of `residueTrace`. That definition is literally the quotient
   descent of `residueSum` along `differentialsPrincipalPartsMap`, composed
   with `differentialsH1Equiv`. Its well-definedness uses
   `residueSum_differentialsPrincipalPartsMap`. `residueTrace_symm_mk` is
   precisely the sum of Tate residues of principal-part representatives.
10. The regular-form vanishing, finite-potent trace construction and separable
    Laurent coefficient formula are the recorded
    `TateResidue.dvr_residue_calculus`. It uses `TateResidue.localRes`, the same
    residue as residueTrace. Only its Laurent-coordinate clause assumes
    separability of the residue field; neither localRes nor the global trace
    does. The warning about naive residues at inseparable points is explanatory,
    not an extra hypothesis; the chosen construction handles those points.
11. `picardTracePairing` takes the actual recorded `scalarCohomologyCup`, then
    `scalarCohomologyMap f (evalTensor F ω)`, then t. Its degree cast only uses
    q+(n-q)=n. If either degree is negative, it is the zero pairing. This is
    exactly the displayed cup/evaluation/trace pairing, with F-dual given by
    the existing `Modules.dual`.
12. The first conjunct of `IsPicardTraceDuality` supplies for every F and q a
    k-linear equivalence from H^(n-q)(F-dual tensor omega) to the dual of H^q(F),
    together with `∀ b a, e b a = picardTracePairing ... a b`. Its inverse
    gives the displayed direction in the node. The equation fixes the
    equivalence to the pairing; a bare unrelated equivalence would not suffice.
13. Its second conjunct quantifies finite locally free F,G, every coefficient
    morphism `φ : F ⟶ G`, q,a,b, and asserts exactly the displayed naturality
    identity. The right coefficient map is
    `picardCohomologyZMap f (dualMap φ ▷ ω) ((n : ℤ) - q)`, with the correct
    contravariant direction G-dual to F-dual.
14. `picard_duality_structureSheaf` states the n=q=1 structure-sheaf linear
    equivalence, including disconnected and empty X. Its source proof
    docstring explains the canonical O_X-dual tensor omega identification.
15. `picard_duality_genus` assumes `IsConnectedCurve`, smoothness and properness,
    and places `IsAlgClosed k` only in this specialization. Its conclusion is
    `f.genus = Module.finrank k (scalarCohomology f O_X 1)`, exactly the
    differential-form genus of sk-def-curve equaling the cohomological genus.

Dependency declarations read and reused (all ten direct dependencies):

- sk-def-curve: `Sheaf.AlgebraicGeometry.CurveGenus`,
  `Scheme.Hom.genus_baseChange_of_isAlgClosed`, and its existing definitions
  `IsCurve`, `IsConnectedCurve`, `Scheme.Hom.genus` from
  `WeilConjectures.AlgebraicGeometry.Curve`.
- def-sc-finite-locally-free-sheaf:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree`.
- def-sc-relative-differential-sheaf:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `Scheme.Hom.relativeDifferentials`.
- def-sc-function-field: `WeilConjectures.AlgebraicGeometry.FunctionField`,
  `Scheme.functionFieldOfComponents`; the integral clause uses the existing
  `Scheme.functionField`, not the product over components.
- pqf-def-cohomology: `WeilConjectures.AlgebraicGeometry.PQFCohomology`,
  `sheafCohomologyAndHigherDirectImages`, with the actual
  `RingedSpace.moduleCohomology` functors.
- def-sc-field-linear-module-cohomology-operations:
  `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`,
  `Modules.scalarCohomology`, `scalarCohomologyCup`, `scalarCohomologyMap`,
  `scalarCohomologyPullback`.
- lem-pc-vector-bundle-principal-parts:
  `Sheaf.AlgebraicGeometry.Curve.VectorBundlePrincipalParts`,
  `Modules.finiteLocallyFree_principalParts_resolution` and its cohomology,
  naturality and differential identifications.
- lem-pc-tate-dvr-residue-calculus:
  `Sheaf.RingTheory.TateResidue.DVRResidueCalculus`,
  `TateResidue.dvr_residue_calculus`.
- def-sc-scalar-global-sections-comparison:
  `WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison`,
  `Modules.externalGlobalSectionsTensor`, and the degree-zero
  `Modules.scalarGlobalSectionsEquiv` used in trace normalization.
- def-pc-module-cohomology-ext-resolution-equiv:
  `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`,
  `Modules.moduleCohomologyExtResolutionEquiv`, whose actual defined composite
  is used in the component trace formula.

Edge cases checked: Spec k; Spec L with L/k finite separable, including products
of such algebras; zero bundle; varying rank on disjoint components; a disjoint
union of two smooth proper integral curves; the empty scheme and empty component
index; q<0 and q>n; arbitrary characteristic and imperfect k with inseparable
closed points. The general clauses impose no H^0(O_X)=k. The singleton integral
component recovers the principal-parts trace. The genus clause is restricted to
the connected algebraically closed setting exactly as in the node. All universe
and variable binders already occur explicitly in the existing module.

Searches made in this task, through msearch.py N8 det-thm-picard-duality:

- leanfinder, `Serre duality finite locally free sheaves smooth proper curves
  canonical trace residue pairing naturality`: eight hits about evaluation and
  residue-field naturality, none the theorem.
- loogle, `serreDuality, residueTrace, LinearMap.IsPerfPair`: zero hits;
  unknown identifier serreDuality.
- leansearch, `Serre duality trace pairing cohomology vector bundle proper smooth
  curve`: eight results about algebra trace, trace duals and contraction, none
  the stated cohomological duality.
- grep, `serreDuality|serre_duality|residueTrace|PicardDuality` in Mathlib
  AlgebraicGeometry: zero hits.
- rg over both project roots with `serreDuality|serre_duality|residueTrace|
  genus_eq_arithmeticGenus|det-thm-picard-duality|sk-thm-picard-duality` found
  the upstream dimension-one integral residue results and the complete
  `Sheaf.AlgebraicGeometry.Curve.PicardDuality` module. The former alone do
  not cover all clauses; the latter's recorded ten declarations do.
- Read the existing sketch node's lean record and compared both natural-language
  statements and statement dependencies byte for byte: identical.

Validation: existing:true introduces no source module and requires no compilation
of a new file (brief-stage2 section 1). The delivery dry run verifies the existing
attachment against the published base. No project source or compiler artifact
was edited, and no direct git command or global build was run.

## Second reading by N8

I performed a separate second pass through the item and the complete existing
module, checking the enumerated correspondence above against the code. I am the
single dispatcher-started worker; no independent worker was started, as the
assignment expressly forbids other agents. The maintainer's independent review
remains the independent second reader.

The essential check is that the primary theorem is only the dimension-one part:
its name alone would omit dimension zero, the structure-sheaf specialization and
the genus equality. The attachment therefore explicitly lists all ten existing
helpers and theorems from the reviewed sketch-node record. I rechecked the
finite-etale trace equation in picard_duality_zero, the empty-cofan and singleton
normalizations in picard_duality_one, both conjuncts of IsPicardTraceDuality,
the actual cup/evaluation construction, and the exact hypotheses of the final
two specializations. No mismatch or change to the existing module was needed.
The item statement, proof, and all dependency lists are unchanged.
