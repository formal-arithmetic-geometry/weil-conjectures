## Worker report

Module: `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`, declaration
`AlgebraicGeometry.ProjectiveSpace.projectiveSpace_standardCharts`.
One theorem, whose proof is `sorry`; no definitions and no proofs added.

Hypothesis and clause dictionary:

- A scheme S: `(S : Scheme.{u})`; the finite nonempty homogeneous-coordinate index set:
  `(n : Type u) [Finite n] [Nonempty n]`. Universes are explicitly declared. An index set
  of cardinality r+1 gives classical projective r-space, including the singleton case.
- P and its two projections: the recorded `ℙ(n; S) = ProjectiveSpace n S`, with
  `ℙ(n; S) ↘ S` for q and `toProjInt n S` for rho. This is the base change of the integral
  model `Proj (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))`. ULift changes only the
  universe, not the coefficient ring. The grading is total degree.
- O_P(1) and T_k: the recorded `twist n S 1` and existing `twistOneSection n S k`.
  These are the twisting module and coordinate sections pulled from the integral model
  along rho; their definitions/docstrings were read in ProjectiveSpace/Twist.lean.
  No second construction of either notion is introduced. As in the already landed
  ProjectiveLinePowerAffineCharts module, the recorded twist supplies O_P(1), and each
  further pullback uses the project's tensor formula, never Mathlib's module pullback.
- D_+(T_i)_S: the existing `standardOpen n S i`, definitionally the preimage of the
  integral Proj basic open under rho. Coordinates u_{j/i} are expressed directly by
  `(toProjInt n S).app (Proj.basicOpen ... (MvPolynomial.X i))
  (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j))`.
  This is rho-sharp applied to T_j/T_i, with denominator i, including u_{i/i}=1.
- (a): `(⨆ i : n, standardOpen n S i) = ⊤`. Equality of opens states exactly the cover.
- (b), every morphism and every pair of indices: the binders
  `∀ (Y : Scheme.{u}) (g : Y ⟶ ℙ(n; S)) (i j : n)`.
  The pulled-back module is `(Scheme.Modules.tensorPullback g).obj (twist n S 1)`.
  Its invertibility is explicitly included as a conclusion. The pulled-back T_i is
  the sectionwise value of the unit of
  `Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)` at `op ⊤` on
  `twistOneSection n S i`; this is the canonical section 1 tensor T_i after sheafification.
- (b), free generator: for every `V : Y.Opens` with `V ≤ g ⁻¹ᵁ standardOpen n S i` and
  every section t over V, `∃! a : Γ(Y,V), t = a • ...` where the last term is the
  restriction of the pulled-back coordinate section to V. This states both existence
  and uniqueness over every smaller open, not merely a basis on global sections.
- (b), relation: over `g ⁻¹ᵁ standardOpen n S i`, the restriction of pulled-back T_j
  equals `g.app (standardOpen n S i) u_{j/i}` times the restriction of pulled-back T_i.
- (b), nonvanishing in P: for every i,
  `Scheme.Modules.nonvanishingLocus (twist n S 1) (twistOneSection n S i) =
  (standardOpen n S i : Set ℙ(n; S))`. The existing nonvanishing predicate is germ outside
  the maximal ideal times the stalk, equivalently nonzero residue-field value. It is
  not the support of a section (a nonzero germ is insufficient).
- (c), every affine open identified with Spec R: `(V : S.Opens) (R : CommRingCat.{u})
  (eV : V.toScheme ≅ Spec R)`. No special choice of the coordinate ring or of its
  identification is forced. Affineness is supplied by eV, so no additional hypothesis.
- (c), intersection: `standardOpen n S i ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V` is exactly the open W.
  `IsAffineOpen W` is the first conclusion.
- (c), polynomial ring and isomorphism: the second conclusion gives
  `E : MvPolynomial {j : n // j ≠ i} R ≃+* Γ(ℙ(n; S), W)`.
  The subtype excludes exactly i; it does not duplicate the redundant coordinate 1.
- (c), R-algebra map: a morphism `h : W.toScheme ⟶ V.toScheme` satisfies
  `h ≫ V.ι = W.ι ≫ q`, fixing the structural map uniquely (V.ι is an open immersion).
  For each coefficient r, `E (MvPolynomial.C r)` is r transported to Γ(Spec R),
  pulled back along `h ≫ eV.hom`, then transported from Γ(W.toScheme,top) to Γ(P,W)
  by `W.topIso.hom`. Thus E is over precisely the R-action induced by q, not an
  arbitrary ring equivalence. For each j≠i, `E (MvPolynomial.X j)` is the restriction
  of u_{j/i} to W. Polynomial maps are determined by coefficients and variables, so
  this states exactly that the specified R-algebra map is an isomorphism without
  choosing a separate typeclass instance for that R-action.

Dependencies read and used:

- def-nagata-projective-space-base-change:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, `AlgebraicGeometry.ProjectiveSpace`;
  its full definition is the pullback of the terminal maps to Spec (ULift Z).
- def-pc-projective-space-twist:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
  `AlgebraicGeometry.ProjectiveSpace.twist`; coordinate sections from its
  `twistOneSection`. Source definition uses the integral graded twisting sheaf;
  its documentation specifies the chart bases and transition units.
- def-pc-module-pullback: `Sheaf.AlgebraicGeometry.TensorPullback`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`; read the full functor definition,
  object formula, and morphism formula. Imported transitively via TensorPullbackAdjunction.
- def-nagata-affine-proj: `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`,
  `AlgebraicGeometry.Proj`, and `Proj.basicOpen`/`Proj.awayToSection` from Basic.
- def-sc-invertible-module: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, included in the conclusion.
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`;
  its signatures and docstrings were read. `Scheme.ΓSpecIso` supplies the coefficient
  dictionary. All these Mathlib and source modules are imported transitively.
- Added the already landed `def-weil-pbc-ample-invertible-module` to stmt_deps for its
  shared `nonvanishingLocus` in `Sheaf.AlgebraicGeometry.Ample`, and the already landed
  `lem-pc-module-pullback-adjunction` for its canonical unit in
  `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`. This is the allowed addition of
  existing landed dependencies under brief-stage2 §5. Neither node is rewritten.

Edge cases checked before writing:

- Singleton n: projective zero-space; the coordinate polynomial ring has no variables
  and is R. The ratio for i=j is 1. No positive-dimension condition is added.
- Empty base S, empty Y, empty V, and the zero coefficient ring: affineness/isomorphisms
  are still appropriate; on an empty open the ring/module of sections is zero and
  unique coefficients remain true. No nontriviality hypotheses are introduced.
- Nonempty n is precisely the hypothesis of the node; no Fintype enumeration or
  DecidableEq instance is demanded. All ring characteristics are covered.
- Nonvanishing is tested in the residue-field fibre, not by a nonzero germ.
- Arbitrary R and identification eV are allowed, with the coefficient map tied to eV.

Searches (all read-only, before drafting):

- msearch.py leansearch, query `projective space standard charts coordinate ratios
  twisting sheaf free generator`: service unavailable, Internal Server Error.
- msearch.py leanfinder, query `projective space standard affine charts covering and
  twisting sheaf coordinate sections free generator`: eight hits, including
  Proj.affineOpenCoverOfIrrelevantLESpan, Proj.awayToSection and basicOpenIsoAway_hom;
  none states this conjunction over a general base or concerns its coordinate sections.
- msearch.py loogle, query `AlgebraicGeometry.ProjectiveSpace.standardOpenIso,
  MvPolynomial.eval₂`: zero hits; source-only identifier unknown to the service.
- msearch.py grep, query `standardOpen|twistOneSection`, AlgebraicGeometry: zero Mathlib hits.
- rg in WeilConjectures/AlgebraicGeometry/ProjectiveSpace*: Charts.lean gives
  standardOpenIso and isAffineOpen_standardOpen for affine S; OfSections gives the cover;
  Twist gives free-generation and the ratio formula using its old pullback encoding;
  CoordinateSection gives the zero-scheme complement. No single declaration states
  (a)+(b)+(c), the explicit residue-field locus and arbitrary affine-open coordinate map.
- rg for this item's id in WeilConjectures: no hits.
- rg in lean/Sheaf for standardOpen/standard charts/nonvanishingLocus: no same statement;
  ProjectiveLinePowerAffineCharts is a different theorem and confirms the established
  twist/coordinate-section/tensor-pullback interface. Ample supplies the shared locus.
- rg in dag/lean_names_upstream.json for standardOpen/projectiveSpace_standardCharts:
  no conflicting declaration name.

Source verification: the local Stacks TeX is absent on this machine, so opened the
actual Stacks pages [01NG](https://stacks.math.columbia.edu/tag/01NG),
[01MV](https://stacks.math.columbia.edu/tag/01MV), and
[01MS](https://stacks.math.columbia.edu/tag/01MS). They provide the standard affine cover,
coordinate nonvanishing loci, and twisting-module trivializations respectively.
The theorem docstring carries all nine steps of the DAG proof with their inputs.

No statement correction, disputed statement, new node or dependency module.
Server compilation: clean, 2.4 seconds, exit code 0. Every variable and universe is
explicitly bound; no local notation, let binder, or auxiliary proof is used.

## Second reading by E1

Independent second reader: read the node and all eight delivered statement dependencies,
their recorded signatures and the relevant source definitions, with the delivered theorem
open. Verdict: the Lean states the node's three clauses with the prescribed objects and
no additional mathematical assumptions. No Lean or node correction was necessary.

Object/hypothesis/conclusion checklist (each item passes):

1. Arbitrary scheme S and finite nonempty homogeneous-coordinate set n:
   `(n : Type u) (S : Scheme.{u}) [Finite n] [Nonempty n]`. These are precisely the
   hypotheses; n is not the projective dimension. No field, separation, Noetherian,
   nontriviality, enumeration, or decidable-equality hypothesis is introduced.
2. Integral total-degree Proj, its base change P, q and rho: `ℙ(n; S)`, `ℙ(n; S) ↘ S`,
   and `toProjInt n S`. Read ProjectiveSpace.lean: the object is the pullback over the
   terminal scheme Spec (ULift Z), with first and second projections in the required order.
   The coefficient lift is a universe implementation of Z, not a changed base ring.
3. Twisting module O_P(1) and global coordinate sections: `twist n S 1` and
   `twistOneSection n S i`. Read Twist.lean, including the definitions of twist and
   twistOneSection. They are the recorded integral twist and sections pulled to P;
   the glued/graded description is the identification explicitly used in proof step 0.
   The recorded twist is reused as required, with further pullbacks using tensorPullback.
4. Standard opens and ratios: `standardOpen n S i` is definitionally rho-preimage of
   `Proj.basicOpen ... (MvPolynomial.X i)` (OfSections.lean). Read `awayXRatio` itself:
   its first index is the denominator, so `awayXRatio (ULift Z) i j` really is T_j/T_i.
   `Proj.awayToSection` followed by `toProjInt.app` gives exactly u_{j/i}.
5. Cover (a): `(⨆ i : n, standardOpen n S i) = ⊤` says union equals P.
6. Arbitrary pullback (b): `∀ (Y : Scheme.{u}) (g : Y ⟶ ℙ(n; S)) (i j : n)`.
   The module is `(tensorPullback g).obj (twist n S 1)` and its `.IsInvertible` is
   a conclusion, not an extra assumption. Read tensorPullbackObj's inverse-image,
   change-of-rings and sheafification formula and IsInvertible's local rank-one condition.
7. Pulled coordinate section (b): the unit of
   `Classical.choose (exists_tensorPullbackAdjunction g)` applied at `op ⊤`.
   Read that theorem's full signature: its second conjunct pins this unit to
   sheafification of `1 ⊗ η(m)`, so this is the canonical pulled section.
8. Free generation (b): for every `V : Y.Opens` with
   `V ≤ g ⁻¹ᵁ standardOpen n S i`, every section t has `∃! a : Γ(Y, V)` with
   `t = a • ...` the restriction of the pulled T_i. This includes uniqueness and all
   smaller opens, not just global sections on the chart.
9. Ratio identity (b): on `g ⁻¹ᵁ standardOpen n S i` the restricted pulled T_j equals
   `g.app (standardOpen n S i) u_{j/i}` times the restricted pulled T_i. Both sides
   have the right restriction open; the ratio indices have not been reversed.
10. Nonvanishing (b): `∀ i, nonvanishingLocus (twist n S 1) (twistOneSection n S i) =
    (standardOpen n S i : Set ℙ(n; S))`. Read Ample.lean: this predicate excludes the
    maximal ideal times the stalk, equivalent to nonzero residue-field value. It is
    not mere nonzero germ or support. Equality as sets expresses the same open locus.
11. Affine base open (c): `∀ (V : S.Opens) (R : CommRingCat.{u})
    (eV : V.toScheme ≅ Spec R) (i : n)`. The isomorphism supplies exactly the affine
    identification; it imposes no chosen presentation or extra affine hypothesis.
12. Intersection and affineness (c): `IsAffineOpen (standardOpen n S i ⊓ q ⁻¹ᵁ V)`.
    This is the precise W of the node.
13. Polynomial coordinate isomorphism (c): the existential ring equivalence E from
    `MvPolynomial {j : n // j ≠ i} R` to `Γ(P, W)` has all the required variables,
    with only i excluded. Its value on each X_j is u_{j/i} restricted to W.
14. R-algebra structure (c): the witness `h : W.toScheme ⟶ V.toScheme` obeys
    `h ≫ V.ι = W.ι ≫ q`, hence is the unique structural restriction (V.ι is mono).
    The formula for E(C r) transports r by `(ΓSpecIso R).inv`, then
    `(h ≫ eV.hom).appTop`, then `W.topIso.hom`. Read the signatures of ΓSpecIso
    and topIso: both directions are correct. Thus the ring equivalence is over the
    required R-action, not an arbitrary equivalence of rings. Together with the
    variable formula it is precisely the specified polynomial algebra map.

Source check: local Stacks TeX is absent, so fetched the upstream constructions.tex into
scratchpad and read `lemma-when-invertible`, `lemma-principal-open`,
`definition-projective-space`, `lemma-standard-covering-projective-space` and surrounding
text. Also opened the corresponding Stacks pages [01NG](https://stacks.math.columbia.edu/tag/01NG),
[01MS](https://stacks.math.columbia.edu/tag/01MS),
[01MV](https://stacks.math.columbia.edu/tag/01MV), and
[01ND](https://stacks.math.columbia.edu/tag/01ND).
The general graded-ring hypotheses of 01MS/01MV specialize to degree-one coordinates;
the coordinate cover makes their invertibility locus the whole integral projective space.
The source gives arbitrary base schemes, with no field or finiteness restriction on S.

Edge cases: empty n is excluded by the node itself and by exactly `[Nonempty n]`.
Singleton n gives projective dimension zero and the empty-variable polynomial ring R;
`awayXRatio_self` is 1. Empty S, Y, and V remain permitted, as does the zero ring R;
on an empty open both section ring and module have one element, so `∃!` is appropriate.
All characteristics are included. The arbitrary universe u covers schemes and rings at
any size; finite coordinate sets can be lifted to that universe. No independent smaller
universe is used for test schemes and no variable or universe is unbound.

Independent searches: LeanFinder query “Relative projective space coordinate nonvanishing
opens trivialize O(1) with polynomial section ring over each affine base open” returned
Proj.basicOpen, isAffineOpen_basicOpen, awayToSection and homogeneous-localization results,
none the conjunction here. Loogle query `AlgebraicGeometry.Proj.basicOpen, _ ≃+* _`
returned zero hits. Direct rg searches for standardCharts, standardOpenIso,
isFreeGenerator_pullbackSection, iSup_standardOpen, nonvanishing, and standard/chart
in the source, Mathlib's ProjectiveSpectrum and the project's Sheaf modules found the
already known component lemmas, not an exact statement. Opened the source's cover,
free-generator, ratio and chart-isomorphism signatures: the pullback components use the
old module pullback; the affine chart theorem alone does not state the present arbitrary
base-open coefficient/variable map or the residue-fibre locus. Checked the upstream name
index for the delivered name: no collision. These are reusable components rather than an
existing exact declaration, so the module is retained.

No new nodes or dependency modules are delivered, and no statement_change is present.
The two added stmt_deps are already landed and provide the shared nonvanishing predicate
and canonical tensor-pullback unit; their node statements and Lean signatures were read.
No hollow definitions, private copies, or proofs were added. The sole proof is `sorry`;
the declaration docstring gives all nine proof steps, sources and blueprint identifier.
All lines meet the width convention. The delivered Lean and lean.statement were compared
verbatim and match. Server scompile completed cleanly (2.4 seconds, exit 0).
Second reading changed only this report; no mathematical or Lean mismatch found.
