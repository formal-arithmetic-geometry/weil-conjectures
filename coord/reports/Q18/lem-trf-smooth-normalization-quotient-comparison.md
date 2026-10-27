## Worker report

The delivery states `AlgebraicGeometry.SmoothNormalizationQuotient.smooth_normalization_quotient_comparison`
in `Sheaf.TraceFormula.SmoothNormalizationQuotientComparison`. Its only postponed proof is
this named theorem. The definitions contain actual constructions or predicates on the
recorded objects. The accepted stage-1 statement, split, sources and dependencies are
unchanged. The previous worker's stage-1 unchanged-item refusal is superseded by the
stage-2 handoff in coord/brief-stage2.md §0: the live node has no Lean record and is in
the stage-2 queue. No repair note for this item was present.

Hypothesis and conclusion correspondence:

- `S : Scheme.{u}` and `[IsReduced S]` express the given reduced scheme.
- `q : S ⟶ Spec (.of (ULift.{u} ℚ))`, `[LocallyOfFiniteType q]` and `[QuasiCompact q]`
  express finite type over Q. ULift is the usual size convention and preserves Q.
- `T : Scheme.{u}`, `h : T ⟶ S`, `[Smooth h]` and `[QuasiCompact h]` express exactly
  the quasi-compact smooth map. No separatedness, nonemptiness or normality is assumed.
- `IsReduced T ∧ LocallyOfFiniteType (h ≫ q) ∧ QuasiCompact (h ≫ q)` gives reducedness
  and finite type of T over Q. Finiteness of both normalization maps is included because
  the statement uses the finite normalization algebra and its short exact sequence.
- `Comparison.theta : T.reducedNormalization ≅ pullback S.fromReducedNormalization h`
  is theta_h. `Comparison.over` identifies the map to T with the second projection.
  `Comparison.normalizationMap` is theta followed by the first projection.
- `algebra X` is literally the pushforward of the structure-sheaf module by
  `X.fromReducedNormalization`; `Comparison.alpha` is the required h-star algebra
  isomorphism. This helper names that expression, not a new normalization construction.
- `Comparison.beta` has source `(tensorPullback h).obj (conductorCokernel S)` and
  target `conductorCokernel T`, using the recorded cokernel without redefining it.
- `inclusion X` is the actual `unitToPushforwardObjUnit`; `quotient X` is its actual
  `cokernel.π`; `sequence X` is the short complex made from those maps. `Canonical`
  includes the two short-exactness assertions and both commuting squares. The first
  square uses the published `tensorPullbackObjUnitToUnit h`, so its first term is the
  canonical structure-sheaf pullback identification. The second square specifies beta
  on the quotient map. These two squares are exactly the isomorphism of sequences;
  they also imply that the pulled-back sequence is short exact.
- The first clause of `Canonical` identifies alpha with the published, adjoint-defined
  `moduleBaseChangeMap` for the square specified by theta, followed by pushforward
  of `tensorPullbackObjUnitToUnit` on the normalization map. Its commutativity witness
  is existential, so the clause cannot be vacuous. Arbitrary module or algebra
  automorphisms cannot replace the canonical comparison.
- `AffineFormula` quantifies over every pair `U : S.affineOpens`, `V : T.affineOpens`
  and `hVU : V.1 ≤ h ⁻¹ᵁ U.1`, including pairs which are not full inverse images.
  `(h.appLE U.1 V.1 hVU).hom.Flat` is flatness of A to B.
- On U, `Γ(algebra S,U)` is definitionally the underlying additive group of
  `Γ(S.reducedNormalization, S.fromReducedNormalization ⁻¹ᵁ U)`, hence the stated N.
  The exact, injective, surjective section maps in `AffineFormula` present
  `Γ(conductorCokernel S,U)` as N/A and similarly present the target quotient on V.
  Surjectivity is asserted only on affine opens, not arbitrary opens.
- `ModuleCat.extendScalars φ` uses the order B tensor_A N; the node writes
  N tensor_A B. The canonical tensor symmetry identifies these orders. `eN`
  and `eQ` are B-module isomorphisms. Their equations on `b tensor n` and
  `b tensor c` identify them with alpha and beta on chart sections. `chartSection`
  uses the recorded section-normalized pullback unit, followed by restriction.
- The equations for `eN` at `1 tensor (n*m)` and `1 tensor 1`, together with its
  B-linearity, make eN the finite B-algebra comparison, not merely an unnormalized
  module isomorphism. Multiplication is the actual multiplication on sections of
  the normalization scheme, not an independently assumed algebra structure.
- Exactness, injectivity and surjectivity of the scalar-extended inclusion and
  quotient maps give the presentation of `(N tensor_A B)/B`. The final square
  `(extendScalars φ).map quotient ≫ eQ.hom = eN.hom ≫ quotient` specifies
  `[n] tensor b ↦ [n tensor b]`. The embedded submodule is the image of the
  extended inclusion `A tensor_A B → N tensor_A B`; the canonical identification
  `A tensor_A B = B` sends b to `1 tensor b`. Its injectivity is stated explicitly.
- The comparisons are global module-sheaf maps, so restriction compatibility is
  built into their naturality. All affine formulas apply to every smaller affine
  pair as well. No separate or freely chosen restriction comparison is used.
- `∃! d : Comparison h, Canonical d` records canonicity. Identity clauses identify
  the induced normalization map with the identity and alpha/beta with the published
  `tensorPullbackSectionId`. The composition clauses quantify over any further
  quasi-compact smooth `g` and canonical comparison data for h, g and g≫h. They
  give the normalization-map cocycle and both module-map cocycles, using precisely
  `tensorPullbackSectionComp g h`. Existence of those further comparisons follows
  by reapplying this same theorem after its first finite-type/reducedness clause.
  These map cocycles determine the corresponding theta cocycle by pullback uniqueness.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsReduced`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Sheaf.AlgebraicGeometry.ReducedNormalization: `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization`, and the underlying component construction.
- Sheaf.TraceFormula.ConductorSmoothBaseChange: `AlgebraicGeometry.conductorCokernel`.
  Only its definition is used; the conductor theorem is not used as a proof input.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.fst`,
  `pullback.snd` (scheme limits supplied through ReducedNormalization's imports).
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`,
  `tensorPullbackSectionId`, `tensorPullbackSectionComp` and their normalized adjunction.
- Mathlib.RingTheory.RingHom.Flat: `RingHom.Flat`; its module meaning is Mathlib's
  `Module.Flat` via the specified ring map.
- Published proof interfaces imported include
  WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
  (`Scheme.Modules.affinePushforward_baseChange` and its algebra and composition clauses),
  TensorPullbackStructureSheaf (`tensorPullbackObjUnitToUnit`),
  FlatModulePullbackExact, ModulePullbackAffineSections,
  CoherentFiniteTypeLocallyNoetherian, and
  Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus,
  ReducedAlgebraicNormalizationFieldChange and CoherentFiniteType.
  Mathlib proof imports cover Noetherian permanence, finite presentation, tensor
  exactness and the sheaf basis criterion. The proof dependencies
  lem-trf-finite-normalization-quotient-local-criterion and
  lem-trf-smooth-reduced-dense-pullback have no recorded module, so no import is
  fabricated for them. Their roles remain in the full natural-language proof docstring.

Sources and edge checks:

Read the full node and every statement-dependency record and declaration, including
its source docstring. Read Stacks more-morphisms.tex, lemma-normalization-and-smooth
(07TD): its unique normalization comparison applies because finite-type Q-schemes
are Noetherian. The quotient calculation is the accepted split's deduction from
02KG, 02N4, 01I9, 00HD and 00DF. The normalized-blowup route is preserved in the
proof docstring; no blueprint unit or mathematical route is changed.

The empty S or T is allowed (no nonempty component or domain assumption is added).
Normal S gives zero cokernel; the zero module satisfies the quotient formulas and
uniqueness. Identity and open immersion cases are explicitly covered. On a nodal
or cuspidal affine curve, tensoring the normalization inclusion and quotient is the
usual flat tensor sequence. Universes are explicit and shared with the scheme and
section categories. No implicit variable or additional size equality is introduced.

Searches (2026-10-23):

- msearch.py leanfinder: "Smooth pullback commutes with the componentwise normalization
  and its structure sheaf cokernel": 8 hits, all relative normalization interfaces
  such as Scheme.Hom.normalizationDiagramMap and normalizationDesc; no full comparison.
- msearch.py loogle: `"normalizationPullback"`: 7 hits for relative normalization,
  its smooth isomorphism instance and projection equations. This concerns normalization
  of a qcqs morphism, not the componentwise absolute normalization quotient sequence.
- msearch.py grep: `normalizationPullback|normalization.*baseChange|baseChange.*normalization`:
  7 Mathlib hits in Normalization and ZariskisMainTheorem; none states this node.
- msearch.py leansearch: "The normalization algebra and its quotient by the structure
  sheaf commute with smooth pullback": 8 relative-normalization hits; no exact match.
- rg of lean/Sheaf and lean/WeilConjectures for conductorCokernel and normalization
  quotient names found the recorded conductor definition/theorem and existing
  normalization helpers, not this full comparison. The upstream blueprint-id search
  had no hits. Searches for the new namespace/theorem in Mathlib, both project
  roots and dag/lean_names_upstream.json had no hits.
- tools/blueprint_refs.py ancestor returns lem-trf-local-term-locality. No new
  independent notion or dependency repair is needed: the helpers only name the
  maps, complex, comparison data and clauses of this item, as authorized by §1.

Validation: scompile.py compiled both sandbox and proper module path successfully,
with no error or warning. The node's lean.statement is copied verbatim from the
main theorem signature. No declaration is proved in this stage-2 delivery.

## Second reading by Q18

Final worker audit against the node and the file: every hypothesis and clause is
matched above. During compiler checking the affine expressions were corrected to
use module-valued `.val.obj` and `.val.app`, while multiplication uses the actual
ring of sections on the normalization. The existential square witness avoids a
vacuous canonicity condition. The tensor-factor order is explicitly explained,
and the short exact quotient presentation retains injectivity of the embedded B.
No statement correction was made. This is a final self-audit, not a claim that a
second agent read the delivery: this dispatcher expressly forbids starting other
agents and delegates independent review to the maintainer after delivery.
