## Worker report

The module `Sheaf.Paper.TorsionCdTopologicalSerreTransfer` states
`AlgebraicGeometry.ProEtale.torsionCd_topological_serreHeart_cohomology_vanishes`
with proof `sorry`. No definitions or subsidiary theorems are introduced.

The stage-1 split is preserved. The inherited failure concerned an unchanged
stage-1 item, whereas this is a stage-2 statement assignment: the current item
has no Lean record, is in `coord/queue.tsv` at stage 2, and has no repair note.
The stage-handoff paragraph in `coord/brief-stage2.md` explicitly resolves this
case. This delivery adds its Lean attachment and adds the already landed
`def-sfb-condensed-module-sections` to `stmt_deps` so the sections functor has its
own statement-dependency citation. No statement correction is needed.

### Hypotheses and clauses

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure is the
  existing `PadicAlgCl ℓ`; finite subextensions inside it are
  `PadicAlgCl.FiniteIntermediateField ℓ`. Changing the chosen algebraic closure
  by an isomorphism changes none of the quantified coefficient possibilities.
- The commutative condensed ring is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`
  with `[MonObj Λ] [IsCommMonObj Λ]`. `hΛ` lists exactly six possibilities up to
  ring-object isomorphism. These express the node's coefficient choices without
  identifying a ring with a particular carrier type.
- The first branch of `hΛ` quantifies `A : Type` with a commutative ring,
  discrete topology and topological-ring structure, and requires `Finite A` and
  `∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0`. Its ring object is
  `Profinite.continuousMapRingObj A`. Every finite ring has such a representative
  in `Type 0`; thus the carrier size does not restrict its isomorphism class.
- The next five branches are respectively the continuous-map ring on `ℤ_[ℓ]`,
  `Profinite.padicIntegersRingObj ℓ E` for a finite intermediate field,
  the continuous-map ring on `ℚ_[ℓ]`, the continuous-map ring on such an `E`,
  and `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`.
  The existing instances give the induced norm topologies on `E` and its
  valuation ring. The final branch uses all continuous functions on profinite
  sets, including functions whose images lie in no single finite subextension.
  It is deliberately not `Profinite.padicAlgClRingObj ℓ`.
- The node's affine scheme is `(X : Scheme.{u}) [IsAffine X]`; its small sites
  are the recorded `Scheme.smallEtaleTopology` within the torsion predicate and
  `Scheme.ProEt.topology X` in the module category. The scheme universe is `u`,
  site objects have universe `u + 1`, site morphisms have universe `u`, and
  abelian coefficients and small coproduct indices use `u + 1`. There is no
  equality imposed between the site object and morphism universes.
- The nonnegative integer is `d : ℕ`. Its use as an integer is `(d : ℤ)`.
- `hcd` quantifies every `(V : Scheme.{u}) (v : V ⟶ X)` with `[IsAffine V]`
  and `[Etale v]`, and asserts the recorded
  `V.HasTorsionEtaleCohomologicalDimensionLE d`. Its definition quantifies
  all locally torsion abelian sheaves on the small étale site and all natural
  degrees above `d`, with ordinary cohomology zero. This is equivalent to the
  node's integer-degree quantification because `d ≥ 0` makes every `q > d`
  positive. No single annihilator of the sheaf is required.
- `M` is an internal module over `condensedRingObj Λ X`, the existing pulled-back
  ring `p_X^*Λ`, in abelian sheaves on the small pro-étale site.
- `hM` is `ObjectProperty.weakSerreCoproductClosure.{u + 1}` of
  `IsConstantModelConstructible Λ X`. Reading the existing definition shows
  that it is the intersection of all replete properties containing these
  constructible modules and closed under kernels, cokernels, extensions and
  all `Type (u + 1)`-indexed ambient coproducts. Its kernel/cokernel clauses
  involve maps whose source and target are members, exactly as in the node.
  Its extension clause uses arbitrary short exact sequences. Its empty
  coproduct clause forces inclusion of zero, so the node's explicit requirement
  to contain zero changes nothing. The upstream `ContainsZero` instance was
  also read. No stronger Serre requirement of closure under arbitrary
  subobjects or quotients is used.
- `(q : ℤ) (hq : (d : ℤ) + 2 < q)` renders every integer degree strictly above
  `d + 2`. The conclusion is `IsZero` of the degree-`q` homology of
  `(condensedModuleSections Λ X).rightDerivedFunctor.obj`
  `((DerivedCategory.singleFunctor _ 0).obj M)`.
  `singleFunctor _ 0` is `M[0]`. The existing `condensedModuleSections` first
  forgets the internal module action and then evaluates the abelian sheaf at
  the final pro-étale object. Its `rightDerivedFunctor` derives this whole
  composite in the internal module category, so this is the actual ordinary
  abelian-group-valued `RΓ`, not a functor separately derived on abelian sheaves.
  The target is a bundled abelian group, so `IsZero` is the required vanishing.
- There are no completeness, Noetherianity, finite-type-over-a-field,
  characteristic, invertibility-of-ℓ, nonempty-scheme, or nonzero-ring
  hypotheses. No completion occurs in the construction used in the conclusion.

### Dependencies and source reading

The node and every statement dependency were opened, including their statement
and recorded attachment. The recorded declarations and full source signatures
used are:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme
  morphisms; the local-affine structure definition was read.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, the induced small étale topology.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt`, weakly étale objects over `X`, and its topology.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  defined by affine-local étale ring maps.
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`:
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`, including
  its local torsion predicate and ordinary étale derived cohomology.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`; its finite
  stratification and finite constant model definitions were read. No copy of
  the older arbitrary-local-matrix constructibility predicate is used.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: the recorded total-derived
  interface and its public upstream import, including
  `CategoryTheory.Functor.rightDerivedFunctor`. Its pushforward specialization
  is the general derived functor of the full underived composite.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`: the recorded
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient` was read. Its
  repaired interface has an additional finite-subextension-valued algebraic
  closure case, so using that whole predicate here would strengthen the
  coefficient generality beyond the node. Instead `hΛ` expands exactly the six
  stated cases using the same existing coefficient constructions. This module
  imports their shared definitions and instances; there is no second definition
  of an admissibility predicate.
- `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure`:
  `CategoryTheory.ObjectProperty.weakSerreCoproductClosure`, read in full,
  including the empty-coproduct argument for zero membership.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`:
  `AlgebraicGeometry.ProEtale.condensedModuleSections`, recorded by the already
  landed definition node `def-sfb-condensed-module-sections`. Its transparent
  body and docstring at lines 123–135 were read. This same module also states
  the global-sections continuity theorem used by proof step 3.
- `def-weil-size-convention` has no Lean object; its recorded metatheoretic
  convention is rendered by the explicit universes above.

The newest blueprint refinement proof (2) was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md`.
It invokes direct-sum preservation on the ambient localizing hull. The present
node is its agent-formulated coefficient transfer obligation; its own source
record explicitly says an exact reference in this full generality is WANTED.
The docstrings retain this qualification, rather than presenting HRS Lemma 8.6
as a proof of the all-continuous Ω weak-Serre assertion.

The theorem docstring copies the three-step accepted proof plan: finite-complex
heart local bound, filtered-heart approximation and minimality, then bounded-below
filtered continuity. The first two proof nodes currently have no Lean records,
so they cannot yet be imported. The third proof node's recorded module is already
publicly imported because it contains the underived sections definition needed
by the statement. No unstated proof theorem is used to manufacture any data.

### Edge cases

Checked before writing: the empty affine scheme is not excluded, and its module
sections vanish; `d = 0` leaves the strict bound `q > 2` intact; the zero ring is
allowed by the finite discrete branch (there is no `Nontrivial A`), including
exponent zero; empty coproducts ensure that the zero module belongs to the hull.
The identity affine étale test morphism is among the tests of `hcd`. No restriction
on residue characteristics is imposed. The finite scalar models use the same
existing predicate as the node. The all-continuous algebraic-closure branch
retains functions with images in infinitely many finite subextensions. The
integer-degree conclusion neither loses the zero-degree boundary nor imposes
any spurious negative-degree condition. No counterexample was established and
no statement correction or `STATEMENT-DISPUTED` flag is introduced.

### Searches actually run

- `msearch.py` LeanFinder: "Torsion etale cohomological dimension implies
  vanishing of ordinary pro etale derived sections for the weak Serre coproduct
  closure of constructible topological coefficient modules". Eight hits,
  including `Rep.isZero_Tor_succ_of_projective`, étale locus/cotangent results
  and derived-category single-object vanishing; none states this theorem.
- `msearch.py` Loogle: `ObjectProperty, IsSerreClass`. Zero hits, with unknown
  identifier `ObjectProperty`; no usable exact match.
- `msearch.py` grep: `weakSerre|WeakSerre|torsion.*[Cc]ohomological`. Zero Mathlib
  hits. The upstream project search found the exact generic weak-Serre closure,
  which is reused, and related proper-image theorems, which are different.
- `msearch.py` LeanSearch: "Torsion etale cohomological dimension bound gives
  pro etale cohomology vanishing for topological coefficient constructible weak
  Serre hull". Eight hits on small étale sites, étale morphisms and étale loci;
  no coefficient-transfer statement.
- `rg` of `lean/WeilConjectures` for this item id: no match. `rg` of project
  sources for weak Serre closure, torsion dimension and derived/module global
  sections found the reused definitions, related proper bounds, and the
  consumer `AffineProfiniteFamilySerreCd`. That consumer only states a geometric
  specialization with additional geometric hypotheses, not this local-torsion
  transfer. No exact existing declaration was found.
- `rg` of `dag/nodes` for `weakSerreCoproductClosure|condensedModuleSections`
  found `def-sfb-condensed-module-sections`, reused through the added existing
  statement dependency. No new node or duplicated notion is needed.

### Validation

`scompile.py NP lem-sfb-torsion-cd-topological-serre-transfer` compiled the single
module in both sandbox and library-module modes on the server, in 5.8 and 5.6
seconds respectively, with no errors or unexpected warnings. All variables
and universe levels are explicit, with `autoImplicit false`.
The Lean record contains the theorem signature verbatim through the conclusion,
excluding `:= by`. Only `lean` and the permitted addition of the already landed
sections definition to `stmt_deps` differ from the original node.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
