## Worker report

The module `Sheaf.Paper.CoefficientFiniteDescentHom` states all three clauses of
`det-lem-coefficient-finite-descent-hom`, without changing its natural-language
statement. The theorem `AlgebraicGeometry.ProEtale.coefficient_finite_descent_hom`
has the only `sorry`. Every helper has actual data. No definition node or dependency
repair is introduced. The existing repair note is a resolved stage-1 proof-splitting
instruction; its ten-step route and unchanged statement are retained.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The standing base is
  `{k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)`.
  The scheme is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, with
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`,
  `[QuasiCompact (X ↘ Spec (.of k))]`, and
  `[IsSeparated (X ↘ Spec (.of k))]`: exactly separated finite type over k.
* A finite coefficient extension inside the fixed algebraic closure is
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. The objects are
  `(C D : BoundedConstructible (padicSubfieldRingObj X ℓ E))`, the recorded
  full subcategory with bounded constructible cohomology and ambient derived Hom.
  The degree is arbitrary `(r : ℤ)`, with no positivity condition.
* Clause (1), finite F: the first conjunct is bijectivity of the existing
  `finiteCoefficientDerivedHomEquiv X ℓ h C.obj ((T_h D.obj)⟦r⟧)` for every
  finite F and h : E ≤ F. Its source is Hom(C_F,D_F[r]); its target is
  Hom(C,Res(D_F[r])). The second conjunct is the identical assertion using
  `finiteCoefficientDerivedAlgClHomEquiv` for the algebraic closure.
  These are the actual recorded derived adjunction equivalences, not arbitrary
  bijections between these sets. Exact restriction identifies Res(D_F[r]) with
  (Res D_F)[r], as in the node's proof.
* Natural in F: the third conjunct states the finite-to-finite naturality
  identity, using `coefficientDescentHomTransition` on the left and
  `coefficientDescentRestrictionTransition` on the right. The fourth is the
  corresponding identity into the algebraic closure. The Hom maps apply
  scalar extension, its exact shift comparison, and canonical tensor
  transitivity. The restriction maps are their adjunction mates at the old
  counit, so they are the coefficient-inclusion maps b tensor m -> i(b) tensor m.
  No unconstrained comparison map or nonempty-choice construction is used.
* Clause (2): the fifth conjunct quantifies over every complex K, an isomorphism
  `DerivedCategory.Q.obj K ≅ D.obj`, integers a,b, and the actual termwise
  vanishing `∀ n, n < a ∨ b < n → IsZero (K.X n)`. It asserts filteredness of
  `AsSmall.{u+1} (Under E)`, `Nonempty (IsColimit (coefficientComplexCocone ...))`,
  and vanishing at every stage below this same a. `coefficientDescentFields`
  is just `(AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E`.
  At i, both inclusion proofs are `leOfHom (ULift.down i).hom`.
  The recorded diagram has value Res(F_X tensor_(E_X) K); its maps are
  actual coefficient inclusions tensor the identity. The recorded cocone has
  vertex Res(Qbar_X tensor_(E_X) K) with these same inclusion legs.
  IsColimit is in the category of E-module complexes, hence termwise colimit.
  The symmetric sheaf tensor identifies the displayed left scalar tensor
  with the node's right scalar tensor; no different object is selected.
* Clause (3): the sixth conjunct says every algebraic-closure shifted Hom has a
  finite-field representative under `coefficientDescentHomToAlgCl`. The last
  conjunct says two representatives (possibly over different F,G ≥ E) with
  equal images have equal images over some common finite H ≥ F,G under
  `coefficientDescentHomTransition`. The tail is a nonempty directed poset;
  these are precisely surjectivity and injectivity of its canonical Hom-colimit
  map. The shifts in both maps use `commShiftIso`; they are not omitted or
  silently replaced by extension of an unshifted target. No chosen categorical
  colimit or extra coherence assumption is needed for this representatives form.

Dependency declarations read and used:

* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`:
  `derivedExtendScalarsSubfield`, `derivedExtendScalarsToPadicAlgCl`,
  `derivedExtendScalarsCompIso`, with full source and target internal-module
  derived categories. Current server source uses the shared reducible derived
  extension aliases; the recorded functors are used throughout.
* `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`, re-exporting
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`:
  `BoundedConstructible`, `boundedConstructible`, `mem_boundedConstructible_iff`.
  Its conditional triangulatedness theorem is not imposed as a hypothesis here.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj`, and its
  commutativity instance. These are the actual p_X^* coefficient rings.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `ModObj`, `Mod`, `Mod.forget`,
  `Mod.regular`, `Mod.comap`; and
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars`, `Mod.extendRestrictAdjunction`. The closed upstream
  audits supply these for dependency nodes whose lean record is absent.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`. All derived categories are
  ordinary, uncompleted derived categories, as in the node.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` records the standing setting;
  this item needs no morphism or compactification choice.
* Added existing definition dependency `def-weil-pbc-finite-derived-tensor-comparison`:
  `Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison`, especially
  `finiteCoefficientDerivedAdjunction`, `finiteCoefficientDerivedAlgClAdjunction`,
  their Hom equivalences and restriction functors. Read with scompile --source.
* Added existing definition dependency `def-weil-pbc-condensed-coefficient-comparisons`:
  `Sheaf.Paper.CondensedCoefficientComparisons`, especially
  `condensedCoefficientCompIso`, `condensedCoefficientCommShift`, and
  `condensedAlgClCoefficientCommShift`. The transitivity maps are derived from
  tensor multiplication, and the shifts are transported from termwise extension.
* Added existing definition dependency `def-weil-pbc-condensed-coefficient-complex-diagram`:
  `Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram`, especially
  `coefficientComplexDiagram`, `coefficientComplexCocone`,
  `coefficientComplexStage`, `coefficientComplexVertex`, and their actual
  coefficient-inclusion maps. Read the complete current source with scompile --source.

All stated proof dependencies are imported, with proof-only imports non-public.
`sk-lem-constructible-ext-continuity` currently has no recorded Lean declaration
or closed upstream audit; its place remains explicit in proof step 10. It is not
needed to type this stage-2 theorem. Other proof inputs are imported through their
recorded modules or their exact Mathlib matches, including localization,
termwise adjunction, exact derived factorization, bounded representatives,
ring-to-module colimits, and tensor preservation of colimits.

Edge cases checked before writing: zero C or D; zero representative complex;
empty scheme; r = 0, positive r, and negative r; F = E and identity transitions;
two different finite fields with a common finite compositum; a singleton or
non-singleton tail; arbitrary lower bound a of a bounded representative; no
upper bound imposed on coefficient fields. The tail always contains E, so it
is never empty. The index is lifted into the coefficient universe u+1, with
site object universe u+1 and site morphism universe u unchanged. No equality
between object and morphism universes is added. Characteristic p is positive
and distinct from ell, exactly the standing hypotheses. No disputed statement
or source correction was found.

Searches for an existing complete statement and names:

* msearch leanfinder: "finite extension of coefficients derived Hom filtered
  colimit bounded constructible pro-etale sheaves". Eight generic commutative
  algebra descent hits, including RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit;
  none states the three-clause pro-etale derived assertion.
* msearch loogle: "CategoryTheory.Adjunction.homEquiv". Twelve adjunction
  declarations; the existing Hom equivalence API is reused, not restated.
* msearch leansearch: "morphisms in bounded constructible derived category
  descend to finite coefficient extension". Eight hits including
  DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, DerivedCategory.Q,
  HasDerivedCategory.standard; none is this statement.
* msearch grep: "constructible.*[Hh]om|[Hh]om.*constructible". Ten hits about
  constructible sets and Chevalley, not derived sheaf coefficients.
* msearch grep: "coefficientDescentDerivedHomMap|coefficientDescentHomTransition|
  coefficient_finite_descent_hom". Zero Mathlib hits.
* rg in upstream WeilConjectures and project lean/Sheaf for derived Hom descent,
  continuity, the item id and the proposed declaration names. Related upstream
  two-colimit HomSurj/HomInj statements do not give clauses (1) or (2); the
  lisse finite coefficient descent module concerns degree-zero modules, not
  derived complexes. The existing comparison and coefficient-complex modules
  were located and reused. No duplicate helper name was found.

Validation: compilation and delivery preflight results are recorded below after
completion. This is a statement delivery; no mathematical proof is claimed.

`scompile.py Q47 det-lem-coefficient-finite-descent-hom` passed for the delivered
module, both sandbox and library-name checks, with exit 0 and no warnings.
Static self-check: 251 lines, no line longer than 100 characters, eight public
recorded declarations, exactly one sorry, and the recorded main signature is
verbatim in the module. No shared source or launcher script was edited.

Delivery dry run passed: `deliver2.py Q47 det-lem-coefficient-finite-descent-hom
--no-push` printed `OK (dry run)` for commit e494e1df8a, with server preflight
and compilation accepted. The actual delivery repeats these required checks.

## Second reading by Q47

Independent maintainer second reading, 2026-10-18, of immutable delivery
50a0e72317d6071a8ce61023c47e39ec0c91d939. The reader did not write the delivery.
This section replaces the delivered placeholder; no Lean or node record is changed.

Sources read: the item's blueprint statement and proof at
`sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.{md,proof.md}`,
the standing-setting source `sk-def-sfb-dc-setting/_section.md`, all eleven
statement-dependency snapshot nodes and their recorded interfaces. The small-site
framework was read in the Q47 clone, including `ModuleObject.Basic`,
`Colimit.Compatibility`, `Colimit.TwoColimit`, module-object scalar extension, and
`ConstructibleSheaf.ProEtaleModule.DerivedCategory`. Current sources of
`CondensedDerivedTensorComparison`, `CondensedCoefficientComplexDiagram`,
`ProEtaleBoundedConstructible`, and `Colimit.TwoColimit` were also obtained with
`scompile.py --source` to resolve missing/stale local files.

Hypothesis and conclusion audit:

1. The explicit field k, positive prime characteristic p, distinct prime ell,
   scheme over k, locally finite type, quasi-compact and separated structure map
   say exactly the standing setting. No extra Noetherian, perfection, properness,
   triangulatedness or weak Serre assumption is imposed. The base field and
   scheme share the standing ambient universe; the site object/morphism
   universes remain u+1/u. The coefficient tail is lifted to u+1, not restricted
   to a smaller universe. `autoImplicit false` prevents unbound binders.
2. E is the recorded finite intermediate field. C and D are the recorded full
   bounded-constructible subcategory, with ambient ordinary derived Hom and
   constructible cohomology; no derived-completeness or lisse-only restriction
   has been inserted. r ranges over all integers.
3. The first two conjuncts use the exact recorded adjunction Hom equivalences
   at target `(T D)[r]`, with derived restriction of that shifted target.
   Bijectivity of these equivalences renders clause (1). Exact restriction
   supplies the conventional identification with `(Res T D)[r]`.
4. The next two conjuncts state the coefficient naturality identities for finite
   inclusions and inclusion into the closure. `coefficientDescentDerivedHomMap`
   conjugates scalar extension by the recorded tensor comparison and inserts
   its shift comparison. `coefficientDescentDerivedRestrictionMap` takes the
   adjunction mate of that comparison applied to the old counit. These are
   actual constructions: on tensor representatives the latter is precisely
   b tensor m mapped to i(b) tensor m. There is no arbitrary chosen map.
5. The fifth conjunct quantifies over every termwise bounded representative K
   of D, every pair of bounds a,b and the asserted termwise vanishing. The
   recorded diagram has stage Res(F_X tensor_E K), actual inclusion maps, and
   cocone vertex Res(Qbar_X tensor_E K). `Nonempty (IsColimit ...)` asserts its
   universal property in complexes of E-module objects; it does not choose
   data from an unproved existence assertion. The same a bounds every stage.
   The commutative tensor symmetry reconciles the source's right tensor
   notation with the existing left-extension convention.
6. The last two conjuncts render clause (3): every closure morphism has a finite
   representative; two finite representatives with equal images become equal
   over a common finite field. The nonempty filtered tail and the canonical
   comparisons give exactly the surjectivity and injectivity description of
   the canonical filtered Hom-colimit map, including shifts.

All three source clauses are present, with no substantive mismatch. The exact
`lean.statement` string equals the theorem signature in the immutable module.
All eight declarations are listed in `lean.declarations`. The seven helpers
have concrete bodies; the sole theorem has exactly `by sorry`. Each declaration
has source/blueprint documentation, and the theorem docstring follows the ten
DAG proof steps: exact scalar adjunction, termwise/localized adjunction,
identification with the chosen derived functors, tensor transitivity,
transition identity, directed coefficient tail, module-colimit transport,
termwise tensor colimit, bounded representative, and Ext continuity. The
continuity node's statement explicitly covers bounded constructible C over E;
its missing Lean declaration is proof-only and does not obstruct this stage-2
signature. No unstated prerequisite is needed to type the delivery.

Independent searches used `rg` for the exact new names across Mathlib,
WeilConjectures and project Sheaf sources (no existing declarations), and for
coefficient Hom/descent/colimit terminology. The existing upstream
`constructibleCocone_homSurj` and `constructibleCocone_homInj` concern the
ordinary-category two-colimit Hom clauses, not the combined three-clause
statement. Existing tensor, module, adjunction, comparison and complex-diagram
notions are reused. The worker report records LeanSearch, LeanFinder/Loogle,
and grep searches; no new definition node or dependency module was delivered.

Edge cases read against the binders: empty X, zero C/D/K, r=0 and either sign,
F=E, identity inclusions, distinct F and G and a common compositum, and every
lower bound of a bounded representative. The tail contains E and cannot be
empty. If a>b, the representative is zero and the assertion still makes sense.
No equality of site universes or restriction on the coefficient degree is used.

Route-pivot check: the current dropped-id list has empty intersection with all
item statement/proof dependencies. The current repair note is resolved stage 1,
by `L (human decision)`, dated 2026-10-17; it requests splitting long steps and
is not a route-pivot note. The delivered ten-step ordinary derived argument
contains no enhanced localization, Quillen, coherent-section, straightening,
operadic or infinity-category step. This item states its actual pro-etale
coefficient-source lemma; it does not substitute pro-etale operations for the
pivoted tower six-operation construction.

Compiler reproduction: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q47 det-lem-coefficient-finite-descent-hom snapshot/lean/Sheaf/Paper/CoefficientFiniteDescentHom.lean`.
Exit 0, no Lean diagnostics: sandbox `Sheaf/Stage2/Sandbox0.lean` 11.2 s;
library `Sheaf/Paper/CoefficientFiniteDescentHom.lean` 53.3 s. The installed
wrapper currently delegates to the server side overlay (rather than running a
local Lean process); its output records a private `/dev/shm/nt-tmp/.../.lbuild`.
The initial multiplexing refusal recovered and did not affect the result.
The delivered report's successful per-file compile is therefore reproducible.
No global/lake build, direct SSH invocation, live Lean edit, claim, delivery,
merge or project-clone mutation was performed. No line exceeds 100 characters.

Finding and repair: H11 (and the substantive section requirement of H1): the
original second-reading section explicitly said no second reading had occurred.
The heading alone was insufficient. This complete report replacement retains
`## Worker report` and supplies the actual independent reading above. The Lean
module, statement, dependency records and mathematical proof route need no fix.
