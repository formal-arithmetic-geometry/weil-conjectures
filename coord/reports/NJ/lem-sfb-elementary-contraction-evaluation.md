## Worker report

The delivery states `AlgebraicGeometry.ElementaryContraction.Diagram.elementary_contraction_evaluation`
in `Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation`. Its single theorem has proof
`sorry`. Every definition has real data. All auxiliary declarations expand this same
node's input, canonical comparisons, quotient geometry or compatibility equations; they
introduce no independent mathematical notion requiring a new DAG node. The item JSON
changes only `lean`; the statement and dependency lists are unchanged.

The earlier worker's blocker confused the completed stage-1 split with stage 2. The live
node's `reviewed` is the Q62 stage-1 review, and there was no `lean` record. No re-splitting
or change to the reviewed mathematical statement is made.

The source is Knudsen II, Section 2, Lemma 2.5, pp.178--179, and Corollary 1.5/Lemma 1.6.
I read the node's eleven-step proof and all statement dependencies. The Brown
primary-author URL timed out, but I obtained the original paper from its journal:
https://journals.msp.org/mscand/article/download/1622/1621/1653 . I read the scans of
printed pp.167--168 and 178--179 directly (the PDF has no text layer). Page 178 gives
the multiplication comparison and the diagonal/difference exact row; p.167 gives
base change and evaluation. In the paper the cokernel in the twisted exact row is
denoted K; our node denotes the untwisted cokernel by K, so the fourth comparison
correctly retains O(-D). The formalization follows the unchanged reviewed node,
including its identity/tail/bridge cases. No statement correction was needed.

Hypothesis and clause correspondence (names below are in the namespace
`AlgebraicGeometry.ElementaryContraction.Diagram` unless qualified):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Any common scheme T | `Diagram.X.base.left`; every T is represented by taking `S = T` and the identity base object. No nonemptiness, reducedness, Noetherianity or characteristic condition is imposed on T. |
| Stable ordered X/T with r markings and Y/T with r+1 markings, genus g >= 2 | `Diagram.X : StablePointedModuli S g r`, `Diagram.Y : StablePointedModuli S g (r+1)`, `base_eq`. These use the recorded `IsStablePointedCurve` and the recorded geometric H1 genus, with `genus_at_least_two`. |
| Last marking t; old markings ti | `last = marking (Fin.last r)` and `marking i.castSucc`. `marking` only transports the common-base equality; it does not alter the sections. |
| q is over T, and q ti = si | `Diagram.q`, `over_base`, `markings`. |
| Delta = q t | `delta = last ≫ q`. |
| Each geometric fibre is an isomorphism or has just one smooth rational exceptional component | `IsElementary`, quantified over every `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]` and `a : Spec Ω ⟶ T`. `fiberMap` is the actual pullback map. Its alternatives are `IsIso` or `Exceptional`. |
| Exceptional component smooth, rational, containing t, exactly three special points including t | `Exceptional` uses an irreducible component's canonical reduced induced scheme, smoothness of its structural map, `normalizedComponentGenus = 0`, containment of the base-changed last section, and `encard = 3` of the inverse image of nonsmooth points or all markings under `normalizedComponentMap`. The nonsmooth set is written as absence of any smooth open neighbourhood, equivalent to the smooth locus, to avoid introducing an LFP instance as a new hypothesis. |
| q is an isomorphism elsewhere and contracts only this component | `fiberMap a ⁻¹' {x} = Z.1`, and `IsIso` of the restriction over the open complement of the closed point x. Smooth genus-zero proper components over an algebraically closed field are rational; no coordinate or chosen parametrization is assumed. |
| D = sum si(T), E = sum ti(T) | `oldIdealX`, `oldIdealY` are finite products of the actual section-kernel ideal sheaves. Their module sheaves are O(-D), O(-E); duals are the recorded divisor modules O(D), O(E). `Result` asserts their Cartier invertibility and that of t, rather than adding assumptions. |
| J = ker(OX -> Delta_* OT), and J dual = Hom(J,OX) | `ideal` is exactly `kernel (SheafOfModules.unitToPushforwardObjUnit delta.toRingCatSheafHom)`; `idealι` is its kernel inclusion. `Scheme.Modules.dual` is the dependency's actual internal Hom. |
| K = coker(OX -> J dual plus O(D)) with components multiplication and divisor inclusion | `multiplication` is tensor-Hom currying of the ideal inclusion; `diagonal = biprod.lift` of the two specified maps, and `expansionModule = cokernel diagonal`. In particular K is constructed, not selected from an unspecified existence theorem. |
| q_* OY = OX | `Comparisons.iso 0`, with `functions` identifying its inverse-direction map with the actual pullback-of-functions structure map. |
| q_* OY(-E) = OX(-D) | `Comparisons.iso 1`, normalized by `old` and the ideal inclusions. |
| q_* OY(t-E) = J dual tensor OX(-D) | `Comparisons.iso 2`. `minus` is the kernel identification q_*O(-t) = J, fixed by `kernel`; `multiplier` characterizes the required comparison by multiplication on all open sections, using the existing `dualTensorHom`. This auxiliary kernel presentation is forced by left exactness and the first comparison; it is not an extra input assumption. |
| q_* OY(t) = K tensor OX(-D) | `Comparisons.iso 3`. `cokernel_left` and `cokernel_right` fix the two maps through the cokernel; the latter has the minus sign from `(b,c) ↦ b-c`. The two negative-D twists are explicit in `image`. |
| Evaluation is a surjection q^*(K tensor O(-D)) -> O(t) | `evaluation` is pullback of `(iso 3).hom` followed by the canonical section-normalized adjunction counit; `Result.evaluation_surjective : Epi ...`. For module sheaves this is surjectivity on stalks/local sections, not surjectivity on all open-section maps. |
| Equivalent invertible quotient q^* K -> O(t) tensor q^*O(D) | `quotient` explicitly cancels the invertible old divisor via tensor associators, the normalized tensor comparison, and the pulled-back evaluation pairing. `Result.quotient_invertible` and `quotient_surjective` assert the two required properties. |
| Corresponding map into Proj_X(Sym K), using quotient convention | `Geometry.tautological`, `map`, `over_X`, `classifies` use the recorded `SymmetricAlgebraSheaf.gradedAlgebraData` and `ProjectiveBundleQuotientGeometry.Classifies`, including quotient-compatible pullback of O(1). `Result.quasicoherent` supplies the canonical symmetric algebra's required property as a conclusion. |
| Ordered sections map to lifts from the two summands | `Geometry.old_lifts` says the pulled-back quotient kills the J-dual summand at each old label; `last_lift` kills the O(D) summand at the last label. Together with the invertible surjective quotient and `Classifies`, these identify precisely the quotient classes of the two summand cokernels. No label is forgotten or permuted. |
| Identity off the exceptional component | `exceptional_fibers` makes the target's projection to X an isomorphism off x. The constructed map is over X and q is already an isomorphism there, so it is the identity under these canonical identifications. No literal equality between differently presented schemes is required. |
| Exceptional component identified with its exceptional projective line by its complete degree-one system | `exceptional_fibers` gives an isomorphism from the reduced exceptional component to the actual target fibre over the rational point x, and identifies its map with the restriction of `projectiveFiberMap`. It also gives an Omega-isomorphism from the standard projective line and identifies the pulled-back quotient line with the existing `ProjectiveSpace.twist ... 1`. Since the morphism is induced by the stated surjective quotient and is an isomorphism of projective lines with this O(1), the resulting linear system is the complete degree-one system (any generating subsystem of H0(P1,O(1)) is the full two-dimensional space). |
| Isomorphism on entire fibre when q is an isomorphism | `Geometry.identity_fibers : IsIso (fiberMap a) -> IsIso (projectiveFiberMap ...)`. |
| Identifications commute with arbitrary base change | `Change` presents every labelled cartesian change; it has no flatness or finite-type restriction on its base map. `Change.Modules` gives the actual ideal/dual/cokernel identifications fixed by inclusion, evaluation-pairing and cokernel equations. `Change.Compatible` requires the four existing adjunction-defined `moduleBaseChangeMap`s to be isomorphisms and to commute with `Comparisons.iso`. No compatibility is merely asserted by freely choosing an unidentified module map. |
| Evaluation and quotient commute with base change | The last two equations of `Change.Compatible`, using the existing section-normalized composition comparisons in `Change.interchange`. |
| Compatibility with every isomorphism, including automorphisms over identity X | All labelled isomorphisms give `Change` squares; `Change.x` may be the identity while `Change.y` is any compatible automorphism. The same four comparison squares and both quotient squares apply. Naturality of the Proj map follows from `Classifies` and uniqueness in the imported quotient-geometry theorem, using these exact quotient squares. |

The main theorem quantifies over every cartesian `Change` without assuming that the
changed diagram is elementary: this follows from the original hypothesis, and its full
`Result` is supplied in the conclusion. In particular there is no extra geometric input
condition on a base change. Existential comparison records are normalized by their
specified maps; no definition chooses data from this postponed existence theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedCurve`: `IsStablePointedCurve`,
  `Scheme.normalizedComponentMap`, `Scheme.normalizedComponentGenus`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `StablePointedModuli`
  (all family fields, stable predicate, and the actual geometric H1 genus).
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `Scheme.IdealSheafData.IsInvertible.isInvertible_toModules` and
  `isInvertible_dual_toModules`; divisor modules remain the actual ideal module/dual.
- `WeilConjectures.AlgebraicGeometry.Modules.Dual`: `Scheme.Modules.dual`,
  `dualEvaluation`, internal Hom and its monoidal closed structure.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`:
  `TautologicalQuotient`, `Classifies`, and the uniqueness content of
  `projective_bundle_quotient_geometry`; the canonical symmetric algebra and relative
  Proj are its imported existing constructions.
- Existing helper APIs: `Scheme.Modules.dualTensorHom`, `tmulSection`,
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`,
  `module_pullback_tensor`, `tensorPullbackObjUnitToUnit`, and `moduleBaseChangeMap`.
  `pullTensor` selects the unique comparison specified by the existing pure-tensor
  formula (pure tensors locally generate); it does not select an arbitrary iso.

Every available proof-dependency module is imported privately, except those already
publicly needed by the statement. Unstated proof nodes
`lem-sfb-rational-contraction-line-cohomology`, `lem-sfb-nodal-section-dual-flat`,
`lem-trf-closed-union-pushout`, and `lem-sfb-section-ideal-proj-expansion` are not
imports and are not needed to type the statement. Their roles are retained in the
complete eleven-step theorem docstring. The proper-to-separated, Nakayama and tensor
exactness Mathlib leaves are supplied by their existing imports.

Edge cases checked before and after writing:

- r = 0: `Fin r` is empty, both old ideal products are the unit ideal; the last
  marking remains present, old-lift equations are vacuous, and the minus-D twist
  becomes the unit twist. A rational exceptional bridge is still permitted.
- Empty T: the geometric hypotheses are vacuous; flat proper nonempty-fibre family
  data over the empty base forces the curves to be empty, so the module and Proj
  conclusions hold in the empty setting. No `Nonempty T` was imposed.
- Identity q: the extra marking is smooth and disjoint from all old markings;
  the defining diagonal/difference row identifies K(-D) with O(t). The independent
  `identity_fibers` clause is retained, rather than requiring an exceptional component.
- Tail with one old marking: O(t-E) is degree zero on the tail, J(-D)-dual is locally
  O; K(-D) has the extra one-dimensional skyscraper contribution to q_*O(t).
- Bridge with no old marking: two branches are counted separately on the
  normalization; J dual is the normalization multiplier module and O(t) has degree one.
- Arbitrary characteristic, nonreduced or disconnected base, and mixed identity/
  exceptional fibres: no excluded cases or base regularity assumptions.
- Universes: all schemes and test algebraically closed fields use the same explicit
  `u`, with `ULift.{u} (Fin 2)` for the projective-line coordinate set. No equality
  between distinct site universes or vacuous smaller test-field universe is imposed.
- Automorphisms over identity X: allowed by the full cartesian change record; no
  coordinate, choice of basis on the exceptional component, or rigidity assumption.

Searches performed (2026-10-22):

- msearch LeanFinder, query `stable pointed curves elementary rational component
  contraction direct images divisor evaluation Knudsen`: eight hits on Weierstrass
  base-extension/minimality results; none states this node.
- msearch LeanSearch, query `contraction of rational component stable pointed curve
  evaluation direct image`: eight hits on tensor contraction, residue-field
  evaluation and smooth-sheaf evaluation; none states this node.
- msearch Loogle, query `AlgebraicGeometry.Scheme.Modules.pushforward,
  AlgebraicGeometry.Scheme.Modules.tensorPullback`: zero hits, unknown identifier
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` in the Mathlib-only search index.
- msearch grep in Mathlib/AlgebraicGeometry, queries
  `contraction|Contraction|knudsen|Knudsen` and
  `StablePointed|ElementaryContraction|Exceptional.*(Curve|Component)`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, contraction/Contraction and
  sectionIdeal: no elementary stable-curve contraction theorem; unrelated algebraic
  contraction/cochain homotopy results and the reusable nodal-branch theorem.
- `rg` for the item's exact DAG id in `lean/WeilConjectures`: no declaration.
- `rg` for `elementaryContraction|elementary_contraction|ElementaryContraction`
  in `lean/Sheaf` and `dag/lean_names_upstream.json`: no existing statement.

The delivery dry run passed preflight and compilation before the final documentation
expansion; it is repeated on the final packet. Validation uses only the prescribed
scompile.py wrapper, in module mode, against the
live published build. Import probes and every iteration of the delivered module were
compiled through it; no global build or direct Lean/Lake invocation was used.

## Second reading by NJ

This is a second self-reading with the node and file open, not a claim that another
agent reviewed it: the dispatcher explicitly prohibits starting other agents and the
maintainer supplies the independent review. I checked each row above against both the
node and declaration records. During drafting I corrected the base-changed marking
maps to start at Spec Omega, counted special points on the normalization, retained
the identity-fibre disjunct, normalized both signs in the cokernel row, and required
O(1) compatibility on the exceptional projective line. The final change statement
has no extra elementarity hypothesis on the base-changed family. The four source
modules, their two negative-D twists, actual evaluation counit, both summand lift
conditions, and all comparison/quotient naturality squares remain explicit. No
mathematical statement change, new node, or dependency-record repair is required.
