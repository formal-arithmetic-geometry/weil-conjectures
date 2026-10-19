## Worker report

The module `Sheaf.Paper.IntegralStratumExtBound` states the entire node as the single
sorry theorem `AlgebraicGeometry.ProEtale.CondensedRing.integral_stratum_ext_bound`.
It introduces no definition and proves nothing. The node changes only in `lean`.
The stage-1 repair note is resolved: its twelve-step proof is retained and rendered in
the theorem docstring. There is no stage-2 archived interface defect to repair.

Hypothesis-by-hypothesis correspondence:

- The global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`. Its
  fields specify p, q, the finite base and its algebraic closure `D.k`. The prime is
  `(l : ℕ) [Fact l.Prime]`, with `(_hl : l ≠ D.p)` expressing distinct characteristic.
- The finite extension E/Q_l is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. `integralCoefficientRing l E` is the recorded
  condensed valuation ring, pulled back to each scheme; it uses the canonical
  valuation ring and uniformizer, and is the completed integral coefficient sheaf.
  The statement does not depend on a choice of uniformizer. It does not replace
  the coefficient by its constant discrete sheaf or a finite quotient.
- X is `(X : Scheme.{u}) [X.Over (Spec (.of D.k))]`, with `LocallyOfFiniteType` and
  `QuasiCompact` on the structure map encoding finite type and `IsSeparated`
  encoding separatedness.
- The open-closed factorization is `(v : S ⟶ Z) (i : Z ⟶ X)`, with
  `[IsOpenImmersion v] [IsClosedImmersion i]`. Its composite is a = i after v.
  There is no separate arbitrary a or assumed comparison map.
- The complement is `(j : V ⟶ X) [IsOpenImmersion j]` with
  `Set.range j = (Set.range i)ᶜ`. Open immersions with this image are precisely
  open-complement inclusions, up to the unique isomorphism over X.
- `[CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j]` supply the domains of
  the recorded cohomological-dimension definitions. These are automatic here,
  rather than additional mathematical restrictions: X is Noetherian by finite
  type over the field; closed Z, open S in Z, and the complement V are Noetherian;
  every open subset of a Noetherian space is quasi-compact, and locally Noetherian
  schemes are quasi-separated. The open immersion j is separated, hence
  quasi-separated, by its existing instance.
- `L : pulledBackModuleObjects (integralCoefficientRing l E) S` with
  `IsConstantModelConstructible ... S L` expresses membership in Cons(S,O_E).
  `HasFiniteConstantLocalModel ... S L` is exactly the recorded local completed
  scalar-module model of the dependency det-lem-int-ext-formula(1). Over the DVR,
  finite presentation and finite generation agree. No flatness, freeness or
  torsion-free condition is imposed on L; a finite torsion module is allowed.

Clause-by-clause correspondence:

- The first conjunct quantifies over every such factorization and local model.
  `∃ d : ℕ, (d : WithTop ℕ) = relativeCohomologicalDimension l ... j +
  cohomologicalDimension l ... S + 3 ∧ ...` names the finite bound asserted in
  the node and its proof. These are the exact recorded dimensions (classical
  locally l-power torsion abelian sheaves), with no alternative dimension.
  They are finite in this setting, as the node's proof explicitly establishes.
- For every N in `pulledBackModuleObjects ... X`, the predicate
  `IsConstantModelConstructible ... X N` is membership in Cons(X,O_E).
  `∀ r : ℤ, (d : ℤ) < r → Subsingleton (...)` states vanishing in every integer
  degree above the displayed bound, uniformly in N. A Hom group is a Type, so
  `Subsingleton` is its zero-group condition, not `IsZero` on a bare Type.
- The source object is `(DerivedCategory.singleFunctor _ 0).obj
  ((lowerStar ... i).obj ((openImmersionLowerShriek ... v).obj L))`, exactly
  `(i_* v_! L)[0] = (a_! L)[0]`. The target is
  `((DerivedCategory.singleFunctor _ 0).obj N)⟦r⟧`. These morphisms are in the
  ordinary ambient unbounded category `integralDerived l E X`, as stipulated
  by the node's definition of Ext.
- The second conjunct quantifies over every C in Cons(X,O_E). Its
  `∃ d : ℕ, ∀ N, ... ∀ r : ℤ, (d : ℤ) < r → Subsingleton (...)` is precisely
  the nonnegative integer d_C, independent of N, with the same ambient Ext.
  Using a natural number for a nonnegative integer is an equivalent encoding;
  Ext degrees remain integers. This clause does not require any stratum choice.

Dependency declarations read and used:

- `sk-def-sf-setting`: `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
  `AlgebraicGeometry.Etale.constantComplex` and its documented coefficient vocabulary.
  Its node explicitly refers to the global datum in `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum`; that existing construction is used directly.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and
  `HasFiniteConstantLocalModel`. Read the full definitions and docstrings.
- `det-lem-int-ext-formula`: `Sheaf.Paper.IntegralStratumHomFormula`,
  `AlgebraicGeometry.ProEtale.CondensedRing.integral_stratum_filtration` and
  `integral_stratum_hom_formula`; its coefficient aliases are the public import
  `Sheaf.Paper.IntegralDerivedCoefficientData`, `integralCoefficientRing` and
  `integralDerived`. Its open-closed source object is reproduced by applying the
  recorded functors, not by a second definition of extension by zero.
- `sk-def-cd`: `Sheaf.AlgebraicGeometry.CohomologicalDimension`,
  `AlgebraicGeometry.ProEtale.cohomologicalDimension` and
  `relativeCohomologicalDimension`. Read both complete signatures and docstrings.

Every recorded proof-dependency module is imported without `public` unless already
publicly imported as a statement dependency. Mathlib proof matches are imported by
the recorded source files. The theorem docstring follows all twelve proof steps,
including the derived dual, [-1,0] reductions, the support fibre, finite-coefficient
comparison, Tor amplitude [0,1], the c+s+2 reduction bound, the Roos triangle's extra
degree, and the final degree-zero filtration argument.

Edge cases checked before writing:

- Empty S: a_!L is zero and its Hom groups vanish; no Nonempty binder excludes it.
- Z = X and empty complementary V: j is the empty open immersion; the recorded
  supremum of an empty set is zero. The displayed bound still has its +3.
- X empty: both clauses allow it, and the zero sheaf is covered.
- L = O_E/pi on a geometric point: allowed by the finite local model predicate.
  Its derived dual has cohomology in degree 1; the ordinary dual would be wrong.
- Torsion N: its derived quotient can have degree -1 cohomology; the statement
  never replaces it by an ordinary quotient or assumes N is flat.
- C = 0 and an empty filtration: d_C can be zero.
- Arbitrary integer r: the cutoff uses the integer coercion of a natural bound,
  and is strict. Negative r cannot exceed this nonnegative bound.
- All schemes and E use the same arbitrary explicit universe u required by the
  recorded module-object/condensed coefficient framework; no accidental
  site-object/morphism universe equality or smaller coefficient category is imposed.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Ext vanishing between constructible integral l-adic
  sheaves bounded by cohomological dimension"`: eight generic injective/projective
  dimension and derived t-structure results; none is this geometric integral bound.
- `msearch.py ... loogle "Ext, Subsingleton, cohomologicalDimension"`: no hits;
  the search service does not know the project's cohomologicalDimension identifier.
- `msearch.py ... grep "integral_stratum_ext|constructible_ext|Ext.*cohomologicalDimension"`:
  no Mathlib hits.
- `msearch.py ... leansearch "Ext vanishing for constructible integral l-adic sheaves"`:
  eight generic Ext/dimension/sheaf-cohomology hits, no exact statement.
- `rg` of `integral_stratum_ext_bound|integral_constructible_ext|det-lem-int-ext-bound`
  in upstream WeilConjectures and side lean/Sheaf finds only the downstream
  `IntegralConstructibleExt.lean` docstring citing this node. That downstream
  theorem combines continuity with the existential consequence and does not state
  this node's explicit stratum bound. It is not imported (that would reverse the
  dependency direction).
- Broader source and side searches for integral Ext and cohomologicalDimension
  found `UniformConstructibleExt` (rational coefficients, cutoff +2) and the
  torsion/integral/rational lisse-lattice bounds; these use different coefficients
  or hypotheses and do not match the present torsion-allowing local model theorem.
  Direct Mathlib CategoryTheory and upstream ProEtale searches for the new name
  and cohomologicalDimension found no declaration to reuse.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag
is needed. No shared source, DAG, launcher script, or Git state is directly edited.

## Second reading by NK

Author's second pass, with the node, the dependency modules and the finished Lean
module open; the independent maintainer review remains separate. Checked the finite
field/prime and coefficient hypotheses, all finite-type and separation binders, the
open-closed order, equality of the complement image, both local-model predicates,
the precise +3 cutoff, the universal target N, the single-in-degree-zero source and
target, the integer shift r, and the independently uniform existential bound for C.
Both clauses are present. The technical qcqs instance binders do not exclude a
locally closed stratum of the standing Noetherian scheme. The source is actual
`i_* v_! L`, not a freely chosen derived object; the coefficient is the same completed
valuation-ring object as the filtration dependency. No theorem on continuity is
substituted for the explicit bound, and torsion L and N remain allowed. No mismatch
was found in this pass. All universe variables are explicit and both auto-implicit
options are disabled.

## Saved-packet repair and validation (2026-10-18)

Retained the earlier packet and first ran `deliver2.py NK det-lem-int-ext-bound
--no-push`. It found a Lean parser error at the adjacent tokens `)⟦` in the shifted
target. Inserted whitespace in both target shifts (`) ⟦r⟧`) and regenerated the
node's verbatim `lean.statement`; no mathematical statement or other node field
changed.

Re-read the current item, its four statement-dependency node records, the coefficient
aliases, finite-field datum, constant-model constructibility definitions, stratum
filtration/formula signatures, and both cohomological-dimension definitions. Checked
the explicit +3 bound and the uniform consequence against the current blueprint and
DAG statement. Both clauses, the completed coefficient, torsion local models, ambient
unbounded derived Hom, and all integer degrees are retained. The node copy differs
from the current shared node only in `lean`. This is the author's self-check; the
maintainer's independent review is still required.

`python3 /home/ubuntu/weil-launcher-nt/scompile.py NK det-lem-int-ext-bound
<module>` passed both sandbox and library checks (31.8 s and 5.1 s), with no errors
or warnings. The prescribed delivery preflight is rerun on the repaired packet.
