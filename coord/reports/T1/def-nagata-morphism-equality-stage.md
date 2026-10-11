## Worker report

The module defines `NagataMorphismEqualityStageData`, a finite-data record for the
stage of equality of two descended morphisms.  It binds the directed inverse system
and limit cone, the base stage, schemes and morphisms over the base, finite affine-chart
and generator indices, the compact-open equality stages and coefficient stages, and the
selected finite upper bound.  Its `stage_eq` field renders the final clause by applying
`directedFiniteUpperBound` to `lambda0`, every `lambdaJK j k`, and every `mu j k a`.
The record fields `affineTransitions`, `finitePresentationX/Y`, `finiteAffineCovers`,
`generatorsGenerate`, `equalLimitBaseChange`, `openEqualityStages`, and
`generatorStages` render the corresponding hypotheses and construction clauses.
The module also defines `nagataMorphismEqualityStage`, which returns the record's
selected stage.

Dependencies used: `Sheaf.Order.DirectedFiniteUpperBound`,
`Sheaf.AlgebraicGeometry.NagataQCOpenEqualityStage`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`; the declarations
used are `directedFiniteUpperBound`, `nagataQCOpenEqualityStage` (for the recorded
open-equality stage notion), and `baseChangeDiagram`/`baseChangeCone` (for the
base-changed system notion).

Edge cases checked: the finite index types may be empty; the finite stage set still
contains `lambda0`, so the selected upper bound is defined.  The directed index type
is explicitly nonempty, and all scheme and index universes are the same `u`.
No statement was believed false; no `STATEMENT-DISPUTED` flag applies.

Searches made: the node's recorded LeanFinder, Loogle, and grep searches found only
broader inverse-limit morphism results and no exact declaration.  I additionally used
`rg` over `lean/Sheaf` and the slopmaster2 source for Nagata equality-stage names;
no existing exact declaration was found.

## Earlier second reading (a previous round; superseded)

Read the node and module independently.  The directed system, affine transitions,
base stage, finite-presentation morphisms, equal limit base change, finite target-chart
and generator data, per-chart open-equality stages, per-generator coefficient stages,
and finite upper-bound stage are each represented by explicit parameters or fields.
The finite stage set in `stage_eq` contains exactly the base, all chart stages, and all
coefficient stages.  No proof is attempted; only data and the selected stage are
recorded.

## Second reading by T1

I independently read the node's full current statement, the module, the three
recorded definition dependencies, and both Mathlib statement dependencies. I also
read the blueprint source paragraph (node order 355) and Stacks `limits.tex`,
`lemma-descend-finite-presentation`, Tag 01ZM, hypotheses and proof of (3), lines
2370–2446. The blueprint describes the selected upper bound, not a theorem asserting
that the maps agree there. The detailed DAG statement supplies the construction
that the blueprint summarizes. The node needs no statement correction.

Object/hypothesis/clause checklist, with its Lean rendering and verdict:

1. Directed nonempty index set and inverse system: `{I : Type u}`, `Preorder I`,
   `IsDirected I (· ≤ ·)`, `Nonempty I`, and `D : Iᵒᵖ ⥤ Scheme.{u}`. All transitions
   are affine by the explicit instance quantified over every arrow. Matches; a
   preorder also covers the node's directed posets.
2. Identified limit and fixed base stage: `c : Cone D`, `hc : IsLimit c`, `i₀ : I`.
   `CompactSpace (D.obj (op i₀))` and `QuasiSeparatedSpace` render qcqs. The tail
   above i₀ suffices; the Stacks hypothesis that every base is qcqs follows on this
   tail by affineness. Matches, without requiring qcqs at earlier indices.
3. Schemes X₀,Y₀ and structure morphisms: `p`, `q` with
   `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` for each.
   These are finite presentation in the Stacks convention used by the node.
   X₀'s `CompactSpace` and `QuasiSeparatedSpace` explicitly render the node's
   stated qcqs consequence, needed to elaborate `nagataQCOpenEqualityStage`;
   they are consequences of the preceding assumptions, not extra restrictions.
   Matches. The draft only supplied local finite presentation and omitted the
   base's qcqs assumptions; repaired.
4. The two base-linear morphisms: `phi psi`, `hphi : phi ≫ q = p`, and `hpsi`.
   `equalLimitBaseChange` asserts equality after composing the projection
   `pullback.fst p (c.π.app (op i₀))` with each morphism. This is equivalent to
   equality of the two base-changed maps to the pullback Y, since their second
   projections coincide automatically and pullback projections jointly determine
   maps. Matches. Replaced the draft's arbitrary `Prop` field with this equality.
5. Finite affine base cover T_j = Spec R_j: fields `J`, `finiteJ`, `T`, `affineT`,
   `coverT`. T consists of opens of the actual base, not unrelated schemes.
   R_j is Γ((T j).toScheme, ⊤), the canonical coordinate ring. Matches.
6. Finite affine target cover V_jk = Spec B_jk over T_j: dependent finite index
   family `K`, `finiteK`, actual opens `V`, `affineV`, `coverV`, and `chartMap`
   with `chartOver`. B_jk is Γ((V j k).toScheme, ⊤).
   `finitePresentationChart` states finite presentation of the induced ring map.
   Matches. Replaced the draft's unrelated scheme families and arbitrary cover
   predicate; the dependent K family does not impose a common chart count.
7. Finite algebra generators: `G j k` is a finset of actual elements of B_jk.
   `generatorsGenerate` says that the subring generated by the image of R_j and
   G_jk is the whole B_jk. For commutative rings this is exactly generation as
   R_j-algebra, without choosing a separate algebra instance. Matches. The draft
   had finsets of natural numbers with no coordinate-ring elements attached.
8. W₁,W₂ and their compactness/equality on X: `phi ⁻¹ᵁ V j k` and
   `psi ⁻¹ᵁ V j k`, `compactPhi`, `compactPsi`, and `equalOpens`. All are concrete
   opens or propositions about these opens. Matches. These facts are explicitly
   justified by the node and do not assert eventual morphism equality.
9. Selected λ_jk: `lambdaJK`, `selectedLambda` equating it to the actual
   dependency declaration `nagataQCOpenEqualityStage D c hc i₀ p ... d r`, and
   `lambdaGE`. Uses the prescribed stage, not an arbitrary successful witness.
   Matches. The draft's `openEqualityStages : Prop` imposed no such condition.
10. Finite affine cover of the intersection at λ_jk: `L`, `finiteL`, `U`,
    `affineU`, and `coverU`. U consists of opens of the actual X_λ produced by
    `baseChangeDiagram`; `coverU` is equality with the intersection, as the
    current node requires (not an assumed equality of the two opens). Matches.
    The draft omitted the cover index l and its opens entirely.
11. Pullbacks x,y of each b: `phiU`, `psiU` are the restricted composites into V;
    `overPhi`, `overPsi` identify them with the two prescribed composites through
    X₀. Thus `(phiU j k l).appTop b.val` and its psi counterpart are exactly x,y.
    The chart maps to T and base-linearity ensure equality on R_j; no field,
    Noetherianity or characteristic condition is introduced. Matches.
12. U_mu and coefficient stages μ_jklb: `mu j k l b` is an object of
    `Over (op (lambdaJK j k))`, hence its underlying index is ≥ λ_jk. In
    `coefficientEquality`, the pullback of U over S_λ along `D.map mu.hom` is
    canonically U_mu (by associativity of fibre products); its first projection
    induces the section map on x,y. Their images are required to be equal.
    Matches every l and every b, including both indices that the draft collapsed.
    The affine-limit/filtered-colimit assertions explain existence of these
    choices; they are not extra data hypotheses and are not proved in this module.
13. F and λ_{phi=psi}: `nagataMorphismEqualityStage` computes
    `directedFiniteUpperBound i₀ d r` of the insertion of i₀, all `lambdaJK j k`,
    and all `(mu j k l b).left.unop`. The finite unions range over exactly J,K,L,G.
    `boundData` records the selected binary bounds; r is separate from the
    directed preorder. Matches. Removed the arbitrary supplied `stage`/`stage_eq`
    fields: the output is now the specified calculation itself.

Dependency signatures were opened and checked. `baseChangeDiagram D p` has objects
`pullback p (D.map j.hom)` and maps induced by identities and D's transitions;
`baseChangeCone` has point `pullback p (c.π.app i₀)`. The module uses these actual
pullbacks (including the diagram for X_λ); no private inverse-system notion is
introduced. `nagataQCOpenEqualityStage` requires the same affine transitions,
limit cone, qcqs X₀, compact opens and equality on the limit, and selects the
upper bound of the base and a witness of compact-open equality descent.
`directedFiniteUpperBound` folds d over the r-sorted finite set; it does not
assert its upper-bound property inside its definition. Both dependency modules
are usable without change. Mathlib's `Spec.reflective` expresses the right-adjoint
Spec limit property; `Concrete.isColimit_rep_eq_iff_exists` is exactly equality
of representatives at a later object, under `PreservesColimit F (forget C)` and
`IsFiltered J`, supplied for CommRingCat by its filtered-colimit instance.
These two theorem dependencies justify the coefficient choices in the node;
this definition takes those chosen witnesses, and does not re-prove the theorems.
No dependency module or new node is needed.

Edge cases: J, each K_j and L_jk, and each generator finset can be empty.
Every family is genuinely dependent and finite, without positive cardinality
assumptions. The finite set F always includes i₀. Empty schemes and zero coordinate
rings remain allowed; subring generation and equality of their sections remain
well typed. There is no n, prime, characteristic, field, or Noetherian parameter.
All schemes and index types live in the single arbitrary universe u required by
the recorded inverse-system constructions; any finite indexing type may be
represented there. No test-scheme universe makes any hypothesis vacuous.

Independent searches: LeanFinder query "chosen equality index for finite coordinate
functions of two finitely presented scheme maps" found local-finite-presentation
and affine-section finite-presentation results, none defining this finite-data
stage. Loogle `RingHom.FinitePresentation` confirmed the existing ring-map predicate
used for the coordinate algebras. The tracked Mathlib grep
`morphism.*equality.*stage|equality.*stage.*morphism` in AlgebraicGeometry had no
hits. Direct rg of the project's Sheaf modules and upstream WeilConjectures for
`morphism.*equality.*stage|stage.*morphism.*equal|NagataMorphismEquality` had no hits.
LeanSearch query "define the finite upper bound of open equality stages and
generator equality witnesses for scheme morphisms" was actually attempted but
returned Internal Server Error; this is an unavailable service, not evidence
of absence. The broader eventual-equality theorem does not define this selected
stage. No duplicate notion was found.

Every mismatch above was repaired in the sandbox. The node's mathematical
statement is unchanged. Its main Lean record now names the actual selected-stage
definition and copies its signature verbatim, with both declarations listed.
There are no theorems or sorries and no arbitrary Prop-valued data fields.
The definition's local instances merely install the finite enumerations supplied
in the record; none occur in its statement or create a file-local convention.
All declarations have source/blueprint docstrings; the module has no hidden
notation, unbound variables or universes. Local compilation completed cleanly,
with no warnings.
