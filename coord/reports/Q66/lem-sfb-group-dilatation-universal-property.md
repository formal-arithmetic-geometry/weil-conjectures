## Worker report

The module `Sheaf.AlgebraicGeometry.GroupDilatationUniversalProperty` states
`AlgebraicGeometry.group_dilatation_universal_property`, with `sorry` as its entire proof.
There are three real auxiliary definitions, all belonging to clauses of this one node:
`dilatationChartIdeal`, `HasDilatationSmoothLifting`, and `HasDilatationAffineCharts`.
They are listed in `lean.declarations`; no construction is chosen from an existence theorem.
No mathematical statement correction and no dependency-interface repair were necessary.

Source checked: Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.2, construction and
Propositions 1–2, printed pp.62–64 (scan PDF pages 68–70), at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The affine calculation and the global Dedekind gluing follow the accepted eight-step DAG
proof; the source supplies the local dilatation, its flat-test lifting property, and the
group structure. The module docstring retains all eight steps, including the stronger
flat-test argument needed to construct operations before the result is restricted to
smooth tests. In particular it never applies the smooth-test property to a possibly
nonsmooth dilatation.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring D and S = Spec D: `D : CommRingCat.{u}` and `Spec D`.
- Noetherian, integrally closed domain of dimension exactly one:
  `[IsDedekindDomain D]` and `hD : ringKrullDim D = 1`.
  Mathlib's Dedekind class allows fields, so the explicit dimension binder is needed to
  retain the node's convention. It is a dimension condition, not an extra hypothesis.
- A closed point s: `s : PrimeSpectrum D` and
  `hs : IsClosed ({s} : Set (Spec D))`. Its ideal is `s.asIdeal`.
- G is an S-group scheme with the usual diagrams:
  `G : Grp (Over (Spec D))`. `G.X` is the S-scheme, `G.X.hom` its structure map;
  the `Grp` structure supplies multiplication, unit, inverse and their diagrams.
- G flat, separated, locally of finite type:
  `[Flat G.X.hom] [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom]`.
  `IsSeparated` is precisely closedness of the relative diagonal, not absolute
  separatedness over Spec Z.
- The closed subgroup F of G_s:
  `F : Grp (Over (Spec (.of ((Spec D).residueField s))))`, with a group homomorphism
  `i : F ⟶ (Over.pullback ((Spec D).fromSpecResidueField s)).mapGrp.obj G` and
  `[IsClosedImmersion i.hom.hom.left]`. The target uses the canonical group structure
  induced by the actual base-change functor. No arbitrary fibre group law is supplied.
- Existence of G' and its group homomorphism d: the existential
  `∃ (H : Grp (Over (Spec D))) (d : H ⟶ G), ...`.
  The first three conjuncts are `Flat H.X.hom`, `IsSeparated H.X.hom` and
  `LocallyOfFiniteType H.X.hom`. Affineness of d is
  `IsAffineHom d.hom.hom.left`. Its group-homomorphism property is part of the type of d.
- Isomorphism outside s: `IsIso` of `d.hom.hom` after `Over.pullback` along the
  canonical inclusion `Scheme.Opens.ι` of the open complement of `{s}`.
- Special-fibre factorization: an S_s-morphism
  `a : (Over.pullback ...).obj H.X ⟶ F.X`, with the explicit equality
  `a ≫ i.hom.hom = (Over.pullback ...).map d.hom.hom`.
- For EVERY smooth S-scheme X and EVERY S-morphism f whose fibre map factors through F:
  `HasDilatationSmoothLifting ((Spec D).fromSpecResidueField s) d.hom.hom z`, where
  `z = i.hom.hom.left ≫ pullback.fst G.X.hom ((Spec D).fromSpecResidueField s)`.
  Its definition quantifies over `X : Over S`, `Smooth X.hom`, and `f : X ⟶ G`,
  and assumes the existence of an actual morphism `a : X_s ⟶ F.left` with
  `a ≫ z = pullback.fst X.hom t ≫ f.left`. This is scheme-theoretic factorization.
  It is equivalently factorization of f_s over Spec κ(s): the closed-point map
  `t : Spec κ(s) ⟶ Spec D` is a monomorphism, so the displayed equality forces the
  morphism a to be over Spec κ(s). The conclusion is exactly
  `∃! f' : X ⟶ H, f' ≫ d = f`. Neither f nor f' is required to be a group map.
- Commutativity is retained conditionally:
  `IsCommMonObj G.X → IsCommMonObj H.X`. There is no commutativity hypothesis on G.
- Concrete affine description: `HasDilatationAffineCharts D s.asIdeal d.hom.hom z`.
  This quantifies over an affine base open `Spec B → Spec D`, with ring map `r`,
  and every generator `π` satisfying `Ideal.map r.hom s.asIdeal = Ideal.span {π}`.
  For every affine open chart `j : Spec A ⟶ G.left` above it, with a specified
  structure map `φ : B ⟶ A` satisfying `j ≫ G.hom = Spec.map φ ≫ Spec.map r`,
  it gives an isomorphism
  `pullback d.left j ≅ Spec (.of (AffineBlowup.chartRing I (φ.hom π)))`.
  Here `I = dilatationChartIdeal z A j` is the kernel of
  `A ≅ Γ(Spec A) → Γ(F ×_G Spec A)`, the full inverse-image ideal of the centre.
  Since the centre lies in the fibre, this is exactly the inverse image in A of the
  ideal in A/πA. The comparison equation requires the isomorphism to be OVER Spec A,
  with projection the spectrum of the canonical algebra map A → A[I/π]. Thus the
  chart is not merely abstractly isomorphic to an unrelated affine scheme.
  `AffineBlowup.chartRing` is the existing A-subalgebra of `Localization.Away (φ.hom π)`
  generated by the indicated fractions; it is not redeclared here.
- Charts agree with G away from s: the preceding open-complement `IsIso` applies to
  this same H and d, hence to these charts. Independence of the local generator and
  the affine cover is expressed by the quantification over ALL π, base opens and
  affine charts for this one fixed H and d. Two chart descriptions are compared over
  Spec A by composing their isomorphisms with the same actual inverse image.
- Localization to D_s: the next conjunct is `HasDilatationAffineCharts` for
  `Localization.AtPrime s.asIdeal`, the extended ideal, and the ACTUAL base change
  of d by `Over.pullback`. Its centre is the base change of z, namely
  `pullback.snd z (pullback.fst G.X.hom (Spec.map ...))`.
  The last conjunct states `HasDilatationSmoothLifting` for this same localized d
  and centre. The testing closed-fibre map is
  `pullback.snd ((Spec D).fromSpecResidueField s) (Spec.map ...)`:
  it is the base change of Spec κ(s) → S, so uses exactly the same fibre without
  imposing a new identification of residue fields. Flatness, separatedness, local
  finite type, group operations and the special-fibre factorization base change
  from the earlier clauses by the existing canonical functors. There is no separately
  chosen local dilatation or arbitrary comparison map.
- No quasi-compactness of G or F: there is no `QuasiCompact` assumption anywhere.
  Smooth tests need not be quasi-compact, locally of finite type or separated beyond
  what smoothness itself entails. Universe `u` is explicit and shared by the schemes
  and coefficient rings, including the tests; no independent smaller test universe
  makes any quantified condition vacuous.

Dependency declarations used (the recorded interfaces were opened, including docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`,
  `Scheme.Hom`, `Scheme.Hom.appTop`, `Scheme.ΓSpecIso`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `GrpObj`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `MonObj`, `IsMonHom`, `IsCommMonObj`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`: the cartesian structure on `Over`,
  the monoidal pullback functor, and its `mapGrp`. These give the relative version of
  `def-sc-group-scheme` directly. The field-only subgroup-scheme convenience class in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` is not substituted for a
  relative subgroup over Spec D.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `...Smooth`: `Smooth`; `...FiniteType`: `LocallyOfFiniteType`;
  `...ClosedImmersion`: `IsClosedImmersion`; `...Separated`: `IsSeparated`;
  `...Affine`: `IsAffineHom`. The first five are precisely the node's recorded notions.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded module of
  `def-pc-base-change`; its module-sheaf declaration is not applicable here, so scheme
  and morphism base change use the record's documented `Limits.pullback` and
  `CategoryTheory.Over.pullback` interfaces. I read the comparison theorem signatures
  and the explanation of the two projections in this module.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`:
  `AlgebraicGeometry.AffineBlowup.chartRing`, the recorded declaration of
  `def-nagata-blowup-chart-ring`. This already-landed definition node was added to
  `stmt_deps` because the theorem now states the chart formula using its declaration.
  Its `chartFraction_eq_iff` and `mem_chartRing_iff` also supply the two recorded
  normal-form/fraction-equality proof dependencies, whose upstream audits are closed.
- The named non-Mathlib proof-dependency module
  `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties` is a plain proof import.
  The remaining proof imports provide torsion-free flatness, Dedekind localization,
  scheme gluing, locally Noetherian schemes, affine morphisms, étale open immersions,
  and flat ring maps. Statement imports also expose the other Mathlib proof inputs.

Edge cases checked before finalizing:

- Dimension zero (a field) is excluded by the node's exact dimension-one convention;
  no extra nonzero-prime convention is silently substituted for that binder.
- Empty affine charts/zero rings are allowed. Their spectrum and chart-ring
  descriptions are empty as required. The predicates do not ask for nonempty charts.
- I = (π) gives the original flat chart A; I = A gives A[1/π] and an empty special
  fibre. The latter occurs when a chart misses F and must not be excluded.
- For G_a and its identity centre, the model chart is D[x/π], with d sending x to πt.
  This checks both the direction of the spectrum map in the chart equation and the
  divisibility condition in the lifting clause.
- A target ring killed by π would not have the cancellation property. The statement
  correctly restricts the unique-lifting property to smooth, hence flat, test schemes.
  It does not state lifting for all test schemes.
- A nonsmooth flat G and a nonreduced subgroup centre remain allowed; no smoothness
  of G or F is assumed. The eight-step proof uses flat tests for the group operations.
- Noncommutative G remains allowed; commutativity is only an implication.
- A nonprincipal maximal ideal of D is allowed: the chart predicate only asks for
  local generators after passing to affine base opens, not for a global uniformizer.
- Non-quasi-compact G, F and X are not removed by any finite-cover binder.

Searches made:

1. `msearch.py ... leanfinder` with “Dilatation of a flat group scheme along a closed
   subgroup of its closed fibre has a unique lifting property for smooth schemes”:
   eight hits on formally unramified morphisms, flatness and smoothness; none is this
   statement or a dilatation construction.
2. `msearch.py ... loogle` with `CategoryTheory.GrpObj, AlgebraicGeometry.Scheme`:
   seven hits, including `Scheme.GrpObjAsOverPullback`, smooth group schemes, and
   group-affine equivalences; this confirms the relative base-change interface, but
   none states the dilatation result.
3. `msearch.py ... grep` with `[Dd]ilatation|blowupChart|blowup_chart`:
   no Mathlib hits.
4. `msearch.py ... leansearch` with “Dilatation of closed subgroup of a group scheme
   over Dedekind domain”: eight topological closed-subgroup hits, no scheme dilatation.
5. `rg` of `dilatation|Dilatation|dilatate|Dilatate` in both `lean/WeilConjectures`
   and `lean/Sheaf`, and a node-ID search in `lean/WeilConjectures`: no declarations.
6. `rg` of `chartRing|ChartRing|blowupChart|BlowupChart` found the existing upstream
   `WeilConjectures.Blowup.Affine.ChartAlgebra` implementation, which is reused.
7. `rg` of the four chosen names in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`
   and `dag/lean_names_upstream.json`: no declaration-name collisions.
8. DAG and latest-blueprint searches for dilatation found the current node and its
   consumers, no duplicate defining node. `tools/blueprint_refs.py search dilatation`
   returned zero blueprint nodes; its `ancestor` command returned None, consistent
   with the node's existing blueprint provenance. The chart algebra is already the
   genuine DAG node `def-nagata-blowup-chart-ring`, not a new notion to duplicate.
9. The example `Sheaf.CategoryTheory.CompactObject` has been withdrawn. I read its
   recorded replacement `WeilConjectures.CategoryTheory.CompactObject` for the
   project module/header/docstring conventions. No repair note exists for this item.

Validation: the module compiled cleanly using `scompile.py` in both sandbox and final
module modes under the prescribed 60-second per-file limit. There are no theorem
proofs beyond the required single `sorry`; all three definitions contain actual data.
No STATEMENT-DISPUTED issue was found. The final dry run and delivery are performed
with `deliver2.py`; their result is recorded by the delivery tool.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
