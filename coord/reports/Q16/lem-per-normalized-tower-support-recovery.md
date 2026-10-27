## Worker report

Stage-2 handoff of the accepted stage-1 split. The item has no base Lean record and no
released repair note. The inherited “already split and maintainer-reviewed” rejection was
for the previous stage; coord/brief-stage2.md §0 explicitly authorizes this handoff. The
accepted statement, proof, proof dependencies, source and review fields are preserved.
Only lean and one added statement dependency change.

The delivery states seven sorry-only theorems in
Sheaf.AlgebraicGeometry.NormalizedTowerSupportRecovery. It supplies a definition-only
comparison interface in Sheaf.AlgebraicGeometry.NormalizedTowerRecoveryTests. It proves
nothing. Every variable and universe is bound explicitly; both files set autoImplicit false.

Hypotheses and clauses, with the node and both files open:

- Reduced scheme and centered normalized blowup tower: existing
  AlgebraicGeometry.Monoscheme.NormalizedTower n retains reduced levels, actual ideal
  centers, the arrows and IsNormalizedBlowup witnesses. IsNormalizedBlowup is affine finite
  generation plus an isomorphism over the base to J.normalizedBlowup. No nowhere-dense,
  normal-base, excellent-base or separated-base premise is added. Coherence is finite
  generation of the quasi-coherent ideals on Noetherian levels.
- Noetherian base and intermediate schemes: hNoeth (or hT/hS) is
  `∀ i, IsNoetherian (T.level i)`, including i=0. Mathlib IsNoetherian is locally
  Noetherian plus compact, not merely a Noetherian underlying topological space. Thus
  finite affine covers by spectra of Noetherian rings are part of the standard equivalent
  presentation (isNoetherian_iff_of_finite_affine_openCover), not a new assumption.
- Ass(B): associatedCenterImages is the union of images of associatedPoints of each
  actual closed subscheme (T.center i).subscheme. The stalk of its structure sheaf is
  O_{T_i,z}/(J_i)_z, and on the Noetherian center, `isAssociatedPrime_iff` removes Mathlib's radical from
  the annihilator condition, so association of its local maximal ideal says exactly that a nonzero
  element of this quotient has annihilator the ambient maximal ideal. This uses the
  already recorded scheme associatedPoints; no new associated-prime definition.
- j quasi-compact, flat and monomorphism: `[QuasiCompact j] [Flat j] [Mono j]`. In schemes
  Mono is equivalent to the diagonal being an isomorphism. The precise image hypothesis
  is hAss: T.associatedCenterImages ⊆ Set.range j.
- Recovery: normalizedTower_support_recovery gives existence of the scheme-theoretic
  uncontracted restriction (`Nonempty (PullbackOver T (𝟙 _) j)`) and for every original
  center the formula `((T.center i).comap p).map p = T.center i`, where p is the actual
  pullback projection of T.toFirst i.castSucc along j. Mathlib IdealSheafData.map is
  `(I.subschemeι ≫ p).ker`; for quasi-compact p its affine sections are the componentwise
  kernel of O -> pushforward O_Z. This is precisely the requested schematic closure,
  including successive stages. It is not a topological closure or radical ideal.
- Uniqueness from equal restrictions: normalizedTower_restriction_injective quantifies
  over independent lengths n,m, both Noetherian towers, their base identification e, and
  both Ass hypotheses. PT/PS retain all cartesian stage comparisons and extended centers.
  SameOver on the restrictions implies SameOver globally. SameOver explicitly contains
  n=m, a CenterIso (whose centers field is equality of actual ideal sheaves transported
  along stage isomorphisms), and the equation over the given base. As in ILO VIII 2.2.3,
  equality means the canonical centered tower comparison, not equality of unrelated Lean
  structure representations. It never permits contraction or an arbitrary reindexing.
- Rational localization: towerTestIntegerMap uses X.toSpecΓ and the unique integer ring
  map (with ULift for the ambient universe); towerTestRationalMap is pullback.fst over
  Spec Z along Spec Q -> Spec Z. normalizedTower_rational_recovery asserts flatness,
  monomorphism, quasi-compactness and the same conditional existence/closure formula.
  It assumes neither openness nor a Q-algebra structure on X.
- Fpqc test: normalizedTower_fpqc_test has `[Flat f] [QuasiCompact f] [Surjective f]` and
  the two actual uncontracted pullback data PT/PS. Its iff compares their SameOver with
  the original SameOver. No claim that normalization commutes with every flat map is
  made; the node's pullback-existence qualification is represented by those data.
- Completed strict local schemes: towerTestCompletedStrictRing s is the genuine
  AdicCompletion of the recorded strictHenselizationRing s at the kernel of its canonical
  geometric evaluation. Its commutative ring instance is the ordinary completion instance.
  towerTestCompletedStrictMap uses Spec.map of the algebraMap into that completion and
  the recorded strictHenselizationStructuralMap s. No arbitrary map or Nonempty choice
  supplies a canonical construction.
- Local faithfully flat maps: normalizedTower_completedStrict_local asserts that the
  evaluation kernel is the maximal ideal of the strict local ring, that the completion
  is local, and existence and uniqueness of a local faithfully flat ring map from
  O_{X,s(closedPoint Ω)} whose spectrum factors the specified completed map through
  X.fromSpecStalk. This factorization uniquely determines the canonical map since
  fromSpecStalk is a monomorphism. Thus the faithful-flat claim concerns exactly the
  map in the node. Universes Ω : Type u allow algebraic closures of all residue fields.
- Completed local equality test: normalizedTower_completedStrict_test quantifies over
  every Ω, Field Ω, IsAlgClosed Ω and s : Spec Ω -> X and their PT/PS. Its left side is
  `(IsEmpty X → n=m) ∧ ∀ Ω s, SameOver ...`. On nonempty X the first premise is vacuous
  and there exists a geometric point, so local SameOver supplies the length equality.
  On empty X it supplies exactly the separately required length equality. No identity,
  empty-test or unit-center case is discarded.
- Nonempty center pullback: normalizedTower_center_completedStrict_nonempty takes an
  actual point z of the actual center and hz identifying its image with s(closedPoint Ω).
  It concludes Nonempty of the scheme-theoretic pullback of that center along the specified
  completed strict local map. No existence of a normalized tower pullback is needed for
  this clause; its ordinary scheme pullback always exists.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsReduced (component_reduced).
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian,
  IsNoetherian, isNoetherian_iff_of_finite_affine_openCover.
- Sheaf.AlgebraicGeometry.NormalizedBlowup:
  Scheme.IdealSheafData.normalizedBlowup and normalizedBlowupMap; the definitions are
  the ordinary blowup's reducedNormalization and its structural composite.
- Sheaf.AlgebraicGeometry.MonoschemeToricRealization: Monoscheme.IsNormalizedBlowup,
  NormalizedTower; Sheaf.AlgebraicGeometry.NormalizedTowerDescentData: toFirst,
  CenterMap, CenterMap.IsCartesian, CenterIso. No new tower definition is introduced.
- Sheaf.AlgebraicGeometry.AssociatedPoints: AlgebraicGeometry.associatedPoints.
- WeilConjectures.AlgebraicGeometry.StrictHenselization: Scheme.strictHenselizationRing,
  strictHenselizationScheme, strictHenselization_properties (small affine colimit).
- WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap:
  Scheme.strictHenselizationStructuralMap and its characteristic existence theorem.
- Sheaf.Paper.StrictHenselizationPointEvaluation: Scheme.strictHenselizationPointEvaluation.
- Mathlib.RingTheory.AdicCompletion.Basic / Algebra: AdicCompletion, its ring structure
  and algebraMap; IsAdicComplete is not needed for the statement.
- Mathlib.AlgebraicGeometry.IdealSheaf.Functorial: IdealSheafData.comap, map; Basic:
  Scheme.Hom.ker and ker_apply; Subscheme: subscheme and subschemeι.
- Mathlib.RingTheory.RingHom.FaithfullyFlat: RingHom.FaithfullyFlat.

Proof-only imports follow the recorded modules where available:
WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes,
Mathlib.RingTheory.Flat.Localization, Mathlib.AlgebraicGeometry.Morphisms.Affine,
Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra,
Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison,
WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat, and
WeilConjectures.RingTheory.StrictHenselizationCompletionNoetherian. Their signatures and
source docstrings were read. Three proof nodes have no Lean declaration yet:
lem-per-flat-monomorphism-local-structure, lem-per-normalized-tower-regular-pullback,
lem-sfb-affine-associated-points-primes; the mathlib leaves have no bespoke module.
The three unstated lemma nodes therefore have no module to import. They are proof
prerequisites only; the maintainer can add those proof imports once stated. No statement
prerequisite is missing or awaited. All seven postponed theorem declarations match clauses
of this one DAG item, carry its source and complete proof docstrings, and are listed in lean.declarations.

Edge cases checked mathematically before writing: n=0 gives an empty union and no center
clauses, but retains the base and length; unit centers have empty closed schemes and remain
at the same index; the zero ideal and centers containing components are allowed. On the
empty scheme lengths 0 and 1 give vacuously equal completed-local test families but are
not SameOver, because its first field demands length equality. The explicit empty-base
condition fixes precisely this. On positive-characteristic X the rational localization
can be empty: Ass containment then forces all recorded centers to have no associated
points, as required, and no false openness or characteristic assumption is introduced.
Identity j and localizations Spec O_{X,x} -> X are admitted; j need not be locally of
finite presentation. Non-normal reduced bases and disconnected schemes are included.

Searches: msearch.py leanfinder for normalized blowup tower recovery by ideal-center closure
returned generic normalization maps, no recovery theorem. Loogle for NormalizedTower and
IdealSheafData, and later associatedCenterImages/PullbackOver/SameOver, gave no exact hit.
LeanSearch for uncontracted normalized towers and completed strict local tests gave generic
ideal/normalization lemmas. msearch.py grep for normalized tower and recovery interface
names gave no match beyond unrelated normalized field traces. Direct rg of Mathlib,
lean/WeilConjectures and lean/Sheaf found the reusable NormalizedTower/CenterIso/cartesian
interfaces, associatedPoints, colimit strict local ring/evaluation and Mathlib ideal map.
No recovery theorem or combined test data existed. DAG rg and blueprint_refs.py search
found no separate definition node for these comparison/test data; ancestor is
lem-per-artin-gabber-affine-curve. Raw new-node search responses are recorded in its
mathlib_searches. The current blueprint/latest ancestor was read; no unit is changed.

Source checked directly in the archived ILO PDF: VIII 2.1.18--2.1.20 (p.89),
2.2.3--2.2.12 (pp.90--91), including the explicit no-automorphism/center-retaining
convention and the scheme-theoretic cartesian meaning of pullback. The proof of 3.4.15
(p.114) supplies the rational and completed local tests. No mathematical dispute and no
statement correction. The withdrawn CompactObject example has no declarations; the
current module/public-import/exposed-section rules are followed instead.

Validation: both delivered files compile separately via scompile.py against the published
live library, including dependency-order compilation, with no errors or warnings. The
initial category inference error in the center nonemptiness clause was repaired with an
explicit `C := Scheme.{u}`. No global build, direct Git command or upstream file write.

## New nodes

`def-per-normalized-tower-recovery-tests` records only the missing recovery comparison and
canonical test data: associatedCenterImages, SameOver, PullbackOver, the genuine completed
strict local ring/map, and the integer/rational structural projections. It builds on the
existing NormalizedTower/CenterMap/CenterIso, associatedPoints, strict local colimit and
its canonical evaluation/structural map, and Mathlib completion and ideal constructions.
The source is ILO VIII 2.1.19, 2.2.3--2.2.12 and proof of 3.4.15 (p.114); the maximal-ideal
interpretation follows Stacks 04HX. Searches listed above find no existing node or exact
comparison interface. All data are explicit; its module has no postponed theorem or
hollow definition. Only this new node is added to the item's stmt_deps; its own dependencies
are exactly the definition nodes cited in its statement.

## Second reading by Q16

This dispatcher assignment forbids starting another agent. No independent second worker
was available or claimed. I performed a separate second pass with the accepted node and
both completed files open; the maintainer's independent delivery review remains required.
The clause-by-clause reading is recorded above. I checked especially that SameOver includes
length equality, CenterIso.centers compares actual ideals, PullbackOver.cartesian includes
every level, the completed map is constructed from the recorded strict local ring, the
empty-base length condition appears outside the empty geometric-point quantifier, and
rational localization is a scheme pullback. No statement mismatch was found. The only
compiler correction was the explicit scheme category for center pullback nonemptiness;
no mathematical hypothesis or conclusion changed.

Preflight format repair: the current stage2_delivery.py requires import_flags for new
nodes (2026-10-23 schema update); the new node records the empty list.
