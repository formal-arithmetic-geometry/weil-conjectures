## Worker report

The module `Sheaf.Paper.UniversalTranslationMultiplier` states
`AlgebraicGeometry.Etale.purUniversalTranslationMultiplier`, with `sorry` as its
whole proof. The supporting declarations are an explicit local-generator
specification of multiplication by a unit section and a general structure, specialized by an abbreviation, packaging the
specified trace, multiplication map, action and conjugation equality. Neither
helper constructs data from a postponed existence theorem. No proof is supplied.

The statement was read against the current blueprint
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/sk-prop-sp-orientation-vector-bundle.proof.md`,
Step 1, and against the complete seven-step DAG proof. The node statement is
unchanged. Its auxiliary definitions use the already published coordinate-tower
model and normalized comparisons.

Hypotheses and objects, clause by clause:

- `N : ℕ`, `hN : 0 < N` express the positive integer annihilator.
- `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`, `hA : (N : A) = 0`
  express the finite commutative coefficient ring and its annihilator. There is
  no nonzero-ring or prime-power assumption.
- `S : Scheme.{u}`, `[IsNoetherian S]` express precisely the Noetherian base.
  Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with the
  finite affine-cover convention of the node. The local rings are Noetherian
  in the recorded `IsNoetherianRing` sense.
- `hS : IsUnit (N : Γ(S, ⊤))` expresses invertibility on S. For every subsequent
  affine tower and every arbitrary pullback, the existing `affineTraceInvertible`
  and `affineTracePullbackInvertible` supply the corresponding proofs.
- `d : ℕ` includes zero. `affineTraceTower S d` is P, and its rank-d tower is W.
  `affineTraceAffineSpaceIso S d` is the existing coordinate isomorphism to
  Mathlib affine space with coordinates `ULift.{u} (Fin d)`.
- The universal vector is `affineTraceCoordinate S d`. The actual map tau is
  `ambientAffineTranslation P d (affineTraceCoordinate S d)`, whose recursive
  last-coordinate map is translation by the negative parameter. Its inverse is
  given by the existing isomorphism. Thus the order is `(z,a) -> (z-a,a)`.
- The source of each witness trace is `(affineTraceLeft A B d).obj
  ((affineTraceRight A N hA B d).obj (ordinaryFiniteUnit A B))`. This is the
  published coordinate presentation of `Rq_! A(d)[2d]`; the right normal form,
  compact-support comparison, and unbounded comparison declarations give exactly
  the identifications stipulated by the node. This is the ordinary small-etale
  category `DerivedCategoryModule A B`, not a pro-etale replacement.
- `trace_hom` fixes the witness trace to the actual `affineTraceCounit` with
  `ambientAffineTraceTransport` and `ambientAffineTraceDatum`. The existential
  trace isomorphism only supplies the inverse of this specified forward map.
- `action_eq` fixes the witness action to `ambientAffineTranslationExchange`
  followed by `affineTraceLeft.map ambientAffineTranslationTate.hom`. These are
  the actual pasted exchange and normalized Tate maps; no free action is assumed.
- `b : LocallyConstant P Aˣ` represents the unit global section under the canonical
  section/function identification explicitly requested by the node. This uses
  the pointwise units even for the zero ring. `scalar_spec` specifies the actual
  multiplication map: for every etale U over B on which b has constant value a,
  and every c in A, the map carries the sheafification generator c to a*c.
  These U cover B by open fibres of b, and sheafification is locally surjective,
  so this specifies m_b uniquely, not just its action on global cohomology.
- `conjugate` reads `trace.inv ≫ action ≫ trace.hom = singleFunctor.map scalar`.
  Lean composition runs left to right; this is exactly `t rho t^{-1} = m_b[0]`.
- The outer existential supplies b and its witness. The first conjunct quantifies
  over every b' with a witness of the conjugation equation and gives b'=b.
  Uniqueness is therefore for the multiplier equation itself, not merely among
  multipliers satisfying the subsequent base-change clauses.
- The next conjunct quantifies over every scheme T, every proof it is Noetherian,
  and every `v : T ⟶ P`. It imposes no flatness, finite-type or separatedness
  condition on v. The coefficient function is precisely `b.comap ⟨v,v.continuous⟩`;
  the translated vector is `fun i ↦ v.appTop (affineTraceCoordinate S d i)`.
- The isomorphism C has its forward map fixed by the displayed equality to the
  existing `affineTraceExchange`, followed by the right-Tate base-change and
  constant-unit comparisons. It is the requested canonical exchange, rather
  than an arbitrary naturality witness.
- The next equality is `pullback.map w.action ≫ C.hom = C.hom ≫ wT.action`,
  exactly `C u*rho_P = rho_T C` in Lean's order of composition.
- `C.hom ≫ wT.trace.hom = pullback.map w.trace.hom ≫
  (ordinaryFiniteUnitPullback A v).hom` is the trace equation. The final factor
  explicitly identifies `u*A_P[0]` with `A_T[0]`, suppressed in the TeX.
- The base-change witness's own `conjugate` field is precisely the third requested
  equation, multiplication by `u*b` in degree zero.
- The zero section is `AffineSpace.zeroSection (ULift.{u} (Fin d)) S` followed by
  the inverse of the published coordinate isomorphism. The next conjunct says
  its pointwise pullback of b is the unit function, equivalently `e*b=1`.
- The final equality says the actual action at the vector obtained by zero-section
  pullback is the identity, including the canonical identity Tate comparison.

Recorded dependency declarations read and used:

- Mathlib `AlgebraicGeometry.Scheme` / `Scheme.Hom`,
  `IsNoetherianRing`, and `AlgebraicGeometry.AffineSpace` with `AffineSpace.over`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`; `DerivedCategory.singleFunctor`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback` and its normalized transport interface,
  reused through the ordinary finite transport.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, used in the existing tower.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`:
  `exists_affineSpaceTopTrace`, providing the specified trace transport and datum.
- `Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange`:
  `compactSupportActionBaseChange` and `compactSupportAction_id`, proof imports.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  actual unbounded exchanges and the bounded-below normalizations, available
  through the public import of the existing ambient constructions.
- Mathlib `CategoryTheory.constantSheaf` and `toSheafify`:
  the existing coefficient sheaf and its local generators.
- `Sheaf.Paper.ConstantSheafSectionsLocallyConstant`:
  `constantSheaf_sections_locallyConstant`, proof import. Its literal signature
  uses `AddCommGrpCat.{u}`; the published upstream continuous-function comparison
  in `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf` supplies the
  coefficient-sized `u+1` version as well. The statement itself uses the canonical
  locally constant function representation and requires no choice of equivalence.
- `Sheaf.AlgebraicGeometry.AffineTraceTower`: `affineTraceTower`,
  `affineTraceCoordinate`, `affineTraceAffineSpaceIso`, `affineTraceNoetherian`,
  `affineTraceInvertible` and `affineTracePullbackInvertible`.
- `Sheaf.AlgebraicGeometry.AffineTraceConstruction`: `affineTraceLeft`,
  `affineTraceRight`, `affineTraceCounit`, `affineTraceExchange`, and
  `affineTraceRightBaseChange`.
- Definition-only node `def-trf-ambient-affine-translation-trace`, whose recorded
  existing declarations are in `Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace`:
  `ambientAffineTranslation`, `ambientAffineTranslationExchange`,
  `ambientAffineTranslationTate`, `ambientAffineTraceTransport`,
  `ambientAffineTraceDatum`. The invariance theorem in that same source is NOT
  used: it is downstream of this node. A future proof-import back into that
  module must be omitted to avoid an import cycle, as stage 2 rule 7 prescribes.
- Mathlib `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace`,
  `AlgebraicGeometry.IsNoetherian.noetherianSpace`, the well-founded order on
  `TopologicalSpace.Closeds`, and `WellFounded.has_min`, proof leaves.
- `WeilConjectures.Compactification.NagataCompactification`:
  `AlgebraicGeometry.NagataCompactification`, proof import.
- Mathlib `DerivedCategory.singleFunctor` full/faithful instances in
  `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`, proof import.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`:
  `CategoryTheory.constant_left_module_inverse_image`, proof import.

The item's stmt_deps gains only three already landed definition nodes:
`def-trf-ambient-affine-translation-trace`, `def-amb-affine-trace-tower`, and
`def-amb-affine-trace-construction`. These identify the exact reused definitions.
There is no new definition node or dependency-interface repair.

Edge cases checked before writing: d=0 gives identity towers and empty coordinate
vectors, without a positive-rank assumption. Empty S and empty T give empty
locally constant functions and valid sheaf equalities. The zero coefficient ring
has its one-element unit group and is permitted. N=1 forces that zero coefficient
case and is included. Disconnected schemes allow distinct locally constant values
and no connectedness or constancy conclusion is added. Arbitrary Noetherian T
has the same scheme universe as P; the coefficient universe remains u+1, as in
the supplied ordinary etale framework. No dimension, field or finite-type
restriction on the base is imposed.

Searches:

- `msearch.py ... leanfinder`: "Universal affine translation acts on normalized
  compact support etale trace by a unique locally constant unit compatible with
  base change" returned eight unrelated normalization and normalized field-trace
  declarations; no exact theorem.
- `msearch.py ... leansearch`: "Automorphisms of a constant module sheaf are
  multiplication by locally constant invertible sections" returned eight results
  about continuous linear automorphisms, tilde sections, condensed constants and
  sheafification scalar operations; none states this theorem.
- `msearch.py ... loogle 'LocallyConstant, ModuleCat'` returned condensed constant
  module formulas and unrelated Profinite declarations, no etale multiplier.
- `msearch.py ... grep 'constantSheaf.*[Mm]ul|[Mm]ul.*constantSheaf|locallyConstant.*[Mm]odule'`
  returned condensed locally constant modules and unrelated free-locus lemmas.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for translation, multiplier and
  constant-section multiplication located the ambient coordinate constructions
  and the stronger translation-invariance statements, not the present unique
  multiplier with all three exchange equations. The present theorem reuses those
  existing coordinate definitions without assuming either invariance theorem.
- The required literal node-id search of `lean/WeilConjectures` found no match.

No STATEMENT-DISPUTED issue or source correction was found.

## Second reading by Q104

Self-contained second pass with the DAG statement and final module open; no other
agent was started, in accordance with the dispatcher's explicit instruction. The
maintainer performs the independent review after delivery. The pass checked the
maps, not only their object types: trace_hom and action_eq prevent unnormalized
choices; scalar_spec acts on every local constant generator; conjugation is in
DerivedCategoryModule; C.hom is the exact published composite; the constant-unit
comparison is present in trace naturality; and the pulled-back witness supplies
the scalar conjugation equation, not merely an action on global sections.
The initial explicit repeated action expressions were replaced by a stored action
with action_eq, preserving the canonical map and reducing elaboration cost.
The Noetherian proof for P is supplied explicitly, so no additional instance or
hollow automatic hypothesis is introduced. All variables and universes are bound.
Uniqueness is quantified over the conjugation witnesses alone. The zero-section
identity action is stated in addition to the function equality.

The final performance repair factors the witness through the generic
`CoefficientLineMultiplierWitness` structure. Its category, functor, objects, trace,
action and scalar predicate are explicit parameters; `TranslationMultiplierWitness`
is their exact specialization to the published derived constructions. This avoids
regenerating a heavy derived-category recursor without changing a field or clause.

Validation: the final complete module passed `scompile.py Q104
lem-pur-universal-translation-multiplier` in both sandbox (9.5 s) and library
module (6.2 s), within the unchanged 60-second limit. No error or unexpected
warning was emitted. Diagnostic `#check` commands and profiler options have been
removed. The four owned declarations are all recorded in lean.declarations;
there is one postponed theorem, with the full seven-step proof docstring.
