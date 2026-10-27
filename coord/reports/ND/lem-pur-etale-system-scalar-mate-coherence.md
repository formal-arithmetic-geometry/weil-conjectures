## Worker report

The module `Sheaf.Paper.EtaleSystemScalarMateCoherence` states
`AlgebraicGeometry.Etale.SystemScalarMate.etaleSystemScalarMateCoherence`.
Its sole theorem has proof `sorry`; every helper definition has real data. The
node statement, proof and dependency lists are unchanged. No dependency repairs
or new independent notions are needed.

Hypotheses and objects, matched against the node:

- The global field and characteristic are `k : WeilConjectures.FiniteFieldDatum.{u}`;
  `_hl : l.Prime` and `_hlp : l ≠ k.p` give exactly the coefficient prime conditions.
- `X Y : Over (Spec (CommRingCat.of k.k))` and their `LocallyOfFiniteType` and
  `QuasiCompact` instances say finite-type k-schemes. `f : X ⟶ Y` is over k;
  `IsSeparated f.left`, `LocallyOfFiniteType f.left`, `QuasiCompact f.left` say
  separated finite type. Nothing asserts Y separated. `c : Compactification f.left`
  is the fixed open/proper factorization.
- `Coefficients l` is the existing inverse sequence of finite commutative rings
  killed by powers of l, without flat or surjective transitions. The existing
  `SystemProjection.Modules`, `Derived`, `level` and `Evaluation.E` are strict
  semilinear module systems and their ordinary unbounded derived categories.
  Index n represents the positive level n+1, including the first level.
- `t : Theory c l` is precisely the already recorded simultaneous proper/open,
  scalar and evaluation presentation. Its `support.F` is derived proper image
  after exact termwise open extension. Its scalar models retain the ordinary
  sheafified change of rings, K-flat universal counit and normalized adjunction.
- `q : Projections t` only packages the invertible actual projections supplied
  by the projection dependency: `system_hom` fixes its arrow to `t.q a`;
  `single_hom` fixes every finite-level arrow to `compactScalarMap`. These are
  determined isomorphisms, not arbitrary projection comparisons.
- `d : Adjoints t q` packages arbitrary fixed `G B`, `g B n`, `adj B`, `adjN B n`.
  `theta`, `counit` and `unit` express the stipulated evaluation identifications.
  `LX`, `LY`, `leftX`, `leftY` give the actual left adjoints to exact evaluations;
  left-adjoint uniqueness identifies these with the recorded left extensions.
  `leftComparison` is fixed by `left_normalized`, its mate being the inverse
  actual support-evaluation comparison. `hom_chain` is the six natural Hom
  bijections in precisely their order, as in the evaluation-bound dependency.
- `Transitions.ordinary` is not a free family of derived level arrows: `sections`
  fixes its map on every section to the horizontal restriction of the module
  sheaf on the sequence site. `Transitions.derived` localizes that map termwise;
  `Transitions.reduction` is its canonical scalar-adjunction transpose.
  `d.transition_normalized` is exactly the stipulated finite-mate-followed-by-
  g_n-of-input-transition equation for each sequence and every m ≥ n. In
  particular the DVR theorem is not applied to arbitrary finite coefficient
  sequences. Its transition formula is what the item explicitly assumes.

Conclusions, in their Lean order:

1. `IsIso (mate q d a)` says the actual natural transformation is invertible.
   `mate` itself is the Mathlib `mateEquiv` applied to `(q.system a).inv`, on
   entire system categories, so its construction never lifts a level family.
2. The next conjunct is the exact transposition equation
   `F_D.map b ≫ epsilon_D = q.inv ≫ T_Y.map epsilon_C`, at every system object.
3. The next conjunct identifies evaluation of b with the finite
   `etaleCoefficientQuotientMate`, using `theta` and the specified scalar
   evaluation isomorphisms on both ends. The finite q is fixed to the actual
   compact-support projection by `q.single_hom`.
4. The transition equation is the naturality square for the actual reduction
   maps of the two entire target-coefficient systems. Together with the
   evaluation identity and `d.transition_normalized`, it is exactly the
   finite-mate transition square specified in the node's proof step 3.
5. `CoefficientAdjunctionEvaluation` spells out the evaluated scalar unit
   and scalar counit equations, using both specified scalar/restriction
   comparisons and the existing finite scalar adjunction. It is asserted
   for X and Y, all coefficient maps, and all levels.
6. The next conjunct spells out compatibility of the actual support-adjunction
   Hom transpose with evaluation. Applied to `q.inv ≫ T(epsilon)` it gives
   precisely evaluation of the displayed transposition formula. All its
   arguments range over the whole unbounded categories.
7. The composition conjunct is an equality of natural transformations
   `whiskerLeft G_B tau_X.hom ≫ b_ab = whiskerRight b_a T_bX ≫
   whiskerLeft T_aY b_b ≫ whiskerRight tau_Y.hom G_D`.
   Lean functor composition reads left to right; thus this is exactly the
   node's displayed b_ba/tau equation. Associators are the existing canonical
   balanced ones, not new freely chosen identifications.
8. The unit conjunct is `b_id ≫ G(unit_Y) = unit_X` at every object.
9. The mixed-square conjunct compares `path` for any two equal coefficient
   composites. `path` is the actual two-mate word transported by the same
   canonical associators. `HEq` accommodates the equal but not definitionally
   identical composite ring-map indices; transporting along the supplied
   equality makes this ordinary equality of natural transformations. It
   includes every mixed quotient/extension diagram without adding flatness.
10. Finite free at every level is expressed by a finite basis of the actual
    restricted module D_n over C_n, with no fixed rank or compatible basis.
    The conclusion gives preservation of finite limits and finite colimits
    by each actual ordinary system-extension functor, and invertibility of
    its universal left-derived counit on EVERY complex, for both X and Y.
    This says exactly that T is already exact termwise extension.

Dependencies read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- The morphism-properties convention has no declaration: the actual Mathlib
  `Over`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` are used.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`,
  `Compactification.Refinement`, its category; the item uses its object c.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`:
  `SheafOfModules.systemLevelLeftExtensionTheory`, its exact evaluations,
  normalized left adjoints and joint conservativity (proof dependency).
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`,
  `AdjunctionEvaluation`, `evaluation_mate`; actual `Systems`, `DS`, and
  representative calculus through the existing projection presentation.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`;
  the item fixes arbitrary finite adjunctions, rather than choosing its right adjoint.
- `Sheaf.Paper.EtaleSystemEvaluationBound`: `StrictEtaleEvaluationBound`,
  `strictEtaleEvaluationHomChain`, `strictEtaleBrownQuotientMate`, and
  `etaleSystemEvaluationBound`. Its general transition normalization and
  six-Hom-chain pattern are spelled out for the arbitrary sequences assumed here.
- `Sheaf.Paper.EtaleSystemCoefficientProjection`:
  `AlgebraicGeometry.Etale.SystemProjection.etaleSystemCoefficientProjection`;
  its public `EtaleSystemProjectionData` provides `Theory`, `Coefficients`,
  actual `Modules`, `Derived`, scalar/evaluation models, `associator`, `unit`, q.
- `Sheaf.Paper.EtaleSystemQuotientNormalization`:
  `AlgebraicGeometry.Etale.etaleCoefficientQuotientMate` and
  `etaleCoefficientQuotientNormalization`; the general finite-ring clause is
  used, without specializing the item to a DVR tower.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  the retained public `SheafOfModules.DerivedChangeOfRingsCochainModel`;
  the ordinary-module specialization is not substituted for the system model.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; scalar models carry
  its normalized adjunction and insertion-of-1 unit.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`
  (proof import), supplying canonical iterated associator normalization.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`,
  `mateEquiv_counit`, `mateEquiv_vcomp`, `conjugateEquiv_id`. This is also the
  recorded Mathlib match of `lem-weil-pbc-mate-pasting`.

Edge cases checked before and during writing: the zero ring is allowed by
`Coefficients.torsion` (exponent zero); nonflat quotients need no extra
instance; identities and m=n occur in the same formulas; variable finite free
ranks and rank zero are included; no normalization or boundedness on inputs
is imposed; empty schemes and zero complexes are included; the positive first
level is n=0. Site objects have universe u+1 and morphisms u, coefficients
u+1, and derived categories use the existing u+2 localization. No extra
universe equality is introduced. No evaluation faithfulness is assumed.

Searches for an existing statement:

- `msearch.py ... leanfinder "Scalar extension mates of exceptional right
  adjoints on derived etale coefficient systems satisfy identity composition
  and evaluation coherence"` and a second phrasing "On derived strict etale
  coefficient systems scalar extension commutes with exceptional right
  adjoints and mates satisfy composition": hits are generic
  `CategoryTheory.Adjunction.derivedε`, `derivedη`, their factorization and
  counit lemmas. No entire-system étale theorem.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.mateEquiv_vcomp"`:
  one result `CategoryTheory.mateEquiv_vcomp`, reused as the generic pasting law.
- `msearch.py ... grep "mateEquiv_vcomp|conjugateEquiv_id" CategoryTheory/Adjunction/`:
  five lines in Mathlib's Mates.lean, no specialized system theorem.
- `rg` searches of both live `lean/WeilConjectures` and `lean/Sheaf` for scalar
  mate names and the exact node id: related scalar/finite-tower statements;
  the only exact-id occurrence is a proof-plan citation in
  `ClopenExceptionalScalarDescent.lean`, not a declaration of this node.
  All newly introduced full names are absent from those trees.

Sources opened: the full node and every statement dependency with its Lean
record; the recorded signatures and docstrings, including transitive model
interfaces; current blueprint `latest/.../def-weil-exceptional-inverse-image.md`;
Zheng PDF printed pp. 15–16, 35–36 (Constructions 2.26, 5.15, Proposition
2.29(2), Lemmas 5.16, 5.22). The blueprint has since changed its adic definition;
this extracted node's independent ordinary-system assertion and explicit
assumptions remain the ones delivered. No target or unit statement is changed.

Validation: scompile.py compiled both the sandbox signature check and the
actual library module cleanly (18.0 s and 20.0 s). One initial parser error at
a line break before `.mapDerivedCategory` was repaired. `autoImplicit false`
is set, all universes and variables are explicitly bound, and the delivered
module has no diagnostic commands, private helpers, local instances or local
notation. Only the expected theorem `sorry` remains. No statement dispute.

## Second reading by ND

A separate rereading pass compared the complete node and the generated module,
hypothesis by hypothesis and conjunct by conjunct. This is a single dispatcher
worker, as instructed; no additional agent was started and no independent
worker review is claimed. The maintainer's independent review remains required.
The rereading found that a bare finite-evaluation mate equation would not spell
out the requested coefficient-adjunction compatibility. The final file therefore
includes `CoefficientAdjunctionEvaluation` for both schemes and the explicit
support Hom-transpose evaluation equation. It also checked the direction of
`tau_X` and `tau_Y`, identity comparisons, the HEq endpoint transport for mixed
squares, and that the finite-free clause uses the actual D_n as C_n-module.
Every clause is matched above; no new node or dependency repair was introduced.
