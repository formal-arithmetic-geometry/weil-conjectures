## Worker report

The module Sheaf.Paper.GaloisContinuousSectionNaturality states
AlgebraicGeometry.ProEtale.GaloisContinuousSection.section_naturality, with sorry
as its entire proof. Its two abbreviations evaluate the existing internal-ring
section sheaf; they introduce no new ring structure or sheaf construction.
The DAG statement is unchanged. In this repair, stmt_deps also gains the required
definition-node owners; the additions are listed below.

Hypothesis and clause correspondence:

- The fields k and Ω, Algebra k Ω and IsSepClosure k Ω give the field and its
  separable closure. The Krull topological group is Ω ≃ₐ[k] Ω inside the existing
  FieldSeparableCech.power, namely Profinite.of (Fin q → (Ω ≃ₐ[k] Ω)).
- The parameter e identifies each actual (q+1)-fold site fibre product with Ω[G^q].
  The hypothesis he : FieldSeparableCech.AreCoordinates k Ω e is precisely the
  cumulative vertex convention, with the first projection the structural Ω-map
  and vertex j the ordered product of the first j increments. Neither coordinate
  existence nor a stronger compatibility assumption is imposed.
- The quantified NormedField A and hA : IsNonarchimedean (norm : A → ℝ) give the
  metric topological nonarchimedean field. NormedField B and hB do the same for
  coefficient changes. There is no completeness or algebraic-closedness binder.
- The witnesses c are ring equivalences from FieldSeparableCech.sections to
  C(power k Ω q,A). Those sections are evaluated on the actual pulled-back
  internal coefficient ring, not an arbitrary continuously modeled replacement.
- The witnesses t give profiniteSections Ω A S ≃+* C(S,A) for every Profinite S.
  profiniteSections evaluates InternalAbelianSheafModule.sectionRingSheaf at the
  dependency's profiniteToProEtOf Ω test object.
- The first conjunct normalizes c on each labelled geometric Ω-point by the
  actual ContinuousRingUniverse.comparison. The second normalizes t at every
  underlying point by profiniteTestProjection. That comparison is the recorded
  adjunction transpose of f ↦ f ∘ π_S, so these are the specified adjoint equations,
  not a choice of an unrelated section isomorphism.
- The witnesses a identify pointSections Ω A with A. The third conjunct fixes
  this equivalence by comparison evaluated at IsLocalRing.closedPoint Ω and the
  final site object Scheme.ProEt.mk (𝟙 (Spec Ω)).
- The fourth conjunct quantifies over every SimplexCategory map α, hence every
  face and degeneracy, and identifies its actual nerve restriction with
  FieldSeparableCech.reindex. The reindex formula is the quotient of successive
  selected cumulative products; it drops the first increment at d₀, multiplies
  adjacent increments at an interior face, drops the last at the final face,
  and inserts 1 for repetitions. Its right hand side applies no automorphism to
  A, including at d₀, retaining trivial coefficient action at the moved base.
- The fifth conjunct states coefficient postcomposition on c for every q,
  including q=0. The sixth states it on t for every S. The seventh states it on
  point sections a. All use FieldSeparableCech.coefficientMap, which is exactly
  (upperStarFromPoint X).map (continuousMapRingObjMapOfUniverse φ hφ).
  Combining the fourth and fifth equations gives the specified commutation
  with all reindexings: both composites evaluate to φ(c A hA n f (reindex α g)).
  Since power 0 is a singleton, the q=0 equation induces exactly φ on A.
- The last conjunct asserts IsIso and IsMonHom of the actual condensedPullbackHom
  along Spec.map (algebraMap k Ω). This is the component of upperStarFromPointComp,
  so it is exactly v*R_A,k ≅ R_A,Ω with the transported multiplication and unit.

Dependency declarations read and used:

- WeilConjectures.Mathlib.FieldTheory.IsSepClosed:
  IsSepClosure.exists_intermediateField_mem, and the imported IsSepClosure class.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback,
  pullback.fst, pullback.snd, used by the existing test and nerve constructions.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  profiniteToProEtOf, condensedRingObj, coefficientRing, upperStarFromPoint,
  upperStarFromPointComp, isMonoidal_upperStarFromPointComp and
  condensedPullbackHom (all in AlgebraicGeometry.ProEtale).
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt, Scheme.ProEt.topology.
- Sheaf.Topology.ContinuousMapCondensedRing:
  Profinite.continuousMapRingObjOfUniverse and its actual ring-object construction.
- Sheaf.Topology.ContinuousMapCondensedRingMap:
  Profinite.continuousMapRingObjMapOfUniverse, the postcomposition coefficient map.
- Sheaf.Paper.ContinuousRingUniverseRealization:
  AlgebraicGeometry.ProEtale.ContinuousRingUniverse.comparisonAdjoint, comparison,
  comparison_isMonHom and comparison_isIso. The first three are the definition
  dependency; comparison_isIso is the already-stated proof dependency.
- Sheaf.Paper.FieldSeparableCechCoordinates: FieldSeparableCech.object, power,
  testPoint, cumulative, AreCoordinates, sections, coefficientMap and reindex.
  These already exist; the parent section_coordinates theorem alone is not the
  full present node (it lacks general Ω[S] sections and the point/pullback clauses).
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence:
  InternalAbelianSheafModule.sectionRingSheaf, used for both abbreviations.
  Profinite.continuousCoefficientRingObj in the recorded parent's sections is
  definitionally the same underlying C(-,A) construction at the common universe;
  no alternative coefficients are introduced.

All dependencies are available transitively through the public parent import;
plain proof imports additionally retain the finite-affine coproduct, Spec-limit,
locally-constant spectrum and weakly-etale stability inputs. The genuine unstated
proof dependency lem-sfb-separable-cover-finite-coordinates is not imported; the
existing closureObject already uses the parent's named weaklyEtale theorem.
No theorem about the canonical map is assumed as a new hypothesis.

Import-cycle note for maintenance: the coordinate definitions are already owned
by Sheaf.Paper.FieldSeparableCechCoordinates, which is the parent item's module.
Consequently its future proof-only import of this module must be omitted under
stages/2-statements.md §3(7), since it would close a module import cycle. This
module does not cite the parent's section_coordinates theorem in a proof; only
its existing concrete definitions are used. No DAG dependency cycle is added.

Edge cases checked: q=0 uses Fin 0 powers and one geometric vertex; the q=0
coefficient formula is exactly φ. In degree one both faces pull a value to its
constant function. In degree two an interior face gives g₁g₂ in the established
composition order. A degeneracy repeats a cumulative vertex, so inserts 1.
For trivial G every power is a singleton. Empty S yields the zero section ring
and the singleton ring of functions from the empty space, with a vacuous
normalization. Trivially normed fields satisfy the same clopen-ball argument.
Ω need not be perfect. All universes and variables are explicitly bound in
module mode with autoImplicit false. A common ambient u allows arbitrary fields
and profinite sets after enlarging the ambient universe; it forces no field
completeness or geometric hypothesis.

Searches (all actually run with msearch.py unless labeled rg):

- leanfinder, “Canonical proetale continuous coefficient sections on the Galois
  Cech nerve naturally in coefficient homomorphisms”: eight unrelated hits,
  including BDeRhamPlus and etale presentation maps; no exact match.
- loogle, “continuousMapPresheaf, ContinuousMap.comp”: no hits, unknown unqualified
  identifier continuousMapPresheaf. This query is not evidence of absence by itself.
- grep, “galois.*continuous.*section|continuous.*section.*galois”: zero Mathlib hits.
- leansearch, “Galois Cech nerve cumulative coordinates on separable closure
  profinite powers”: cechNerveTerminalFrom and InfiniteGalois profinite-limit
  declarations, but no normalized coefficient comparison.
- leanfinder, “A definition of cumulative Galois Cech coordinates on powers of a
  separable closure”: galBasis and InfiniteGalois limit maps; no exact match.
- grep, “AreCoordinates|FieldSeparableCech|cumulative.*[Gg]alois”: zero Mathlib hits.
- rg of the shared WeilConjectures and Sheaf trees for Galois nerve/continuous
  sections, profiniteTestProjection, AreCoordinates and FieldSeparableCech found
  the exact reusable parent helpers and continuous-ring comparison. They were
  reused. grep of WeilConjectures for this node id gave no match.
- blueprint_refs.py search “Galois Cech coordinates” and “cumulative” gave zero
  blueprint matches; ancestor on this item retained the inherited null ancestor.

Source read: HRS Example 3.1 on PDF page 6, including the functoriality in
coefficient rings and Λ_Y=f⁻¹Λ_X paragraph; the current blueprint test-object
file in literature/blueprint/latest. The inherited expanded proof specifies the
extra cumulative conventions. No statement fault or STATEMENT-DISPUTED remains.

Validation: scompile.py compiled the delivered module twice (sandbox and library
module names) cleanly, in 12.8 and 10.0 seconds respectively. The only postponed
proof in this delivery is section_naturality; both abbreviations have real data.

## Repair of returned head 1b3e1a0a531f

H2 repaired: added the landed def-sfb-field-separable-cech-nerve to the item
stmt_deps for closureArrow/object/power/testPoint/AreCoordinates (and cumulative).
Added and cited def-sfb-field-separable-cech-section-data, existing:true on the
three existing plain definitions sections/coefficientMap/reindex. The new node
depends only on definition nodes; it neither cites nor assumes the parent
lem-sfb-field-separable-cech-coordinates theorem. This removes the unrecorded
statement dependency on the downstream theorem node. No definition or theorem
was copied. The node-level dependencies are acyclic. The shared module's future
proof-import cycle is still to be handled as noted above.

Advisories addressed: stmt_deps now also cites the landed
def-zl-profinite-test-projection for profiniteTestProjection and
def-weil-pbc-internal-abelian-sheaf-module-equivalence for sectionRingSheaf.
The Lean file is intentionally byte-identical to the reviewed returned head, as
explicitly permitted in the return. The spelling continuousCoefficientRingObj
therefore remains in uses of the parent's existing section/coefficient helpers;
it is definitionally the recorded continuousMapRingObjOfUniverse at these
universes, with no mathematical difference.

Compared the retained sandbox with current main: outside lean the original item
was identical before this repair. Rebuilt its copy from current main, restoring
only this delivery's lean and the four added stmt_deps. All original statement,
proof, proof_deps and other fields are preserved; no statement_change is needed.
The delivery wrapper rebases this packet onto current server main.

The maintainer already independently checked every mathematical clause and all
edge cases of the unchanged Lean file. No independent second worker is started
under the dispatcher instructions; maintainer review remains the independent
reading. New compile, preflight and delivery checks are rerun below.

## New nodes

def-sfb-field-separable-cech-section-data owns the existing definitions
FieldSeparableCech.sections, coefficientMap and reindex in
Sheaf.Paper.FieldSeparableCechCoordinates. Its self-contained statement defines
the actual ring of sections on W_q, the actual inverse-image coefficient map on
any scheme, and the quotient of selected cumulative products for every simplex
map. Source: HRS Example 3.1, p. 6, and the cumulative Cech convention in the
existing parent expansion. All three definitions contain real data. There is
no comparison theorem, coordinate-existence assertion, or nonarchimedean
hypothesis in this node. Edge cases include q=0, n=0, constant simplex maps,
identity coefficient maps, and trivially normed fields.

The new node records actual fresh searches: LeanSearch for section rings,
coefficient maps and simplex reindexing returned abstract Cech nerves and
condensed modules; LeanFinder for cumulative Galois Cech increment reindexing
returned LightProfinite transition maps and unrelated inverse systems; Mathlib
grep for FieldSeparableCech|coefficientMap|def reindex returned unrelated matrix,
basis and affine-space reindexings. Project/DAG rg found these exact plain defs
only in the existing parent's module and its theorem node's lean record; no
definition node already owned them. Whole-blueprint search for
Galois.*section|Cech.*increment gave zero matches, and the ancestor command
confirms the inherited null ancestor. Search log records are copied verbatim
into mathlib_searches. This new existing:true binding supplies ownership without
a new module or an import of the parent theorem as a DAG prerequisite.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
