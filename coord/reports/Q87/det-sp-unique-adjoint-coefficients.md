## Worker report

This repairs returned head `6a2d7d38f056` for H3, H8, and H11. The saved packet's
initial prescribed dry run passed (`8c7cd01ded`), but that mechanical result did
not resolve the mathematical review. The module has therefore been repaired.

`Sheaf.SmoothPurity.UniqueAdjointCoefficients` now uses the recorded coefficient
categories of `def-sf-categories`, including every one of the four admissible
stages. `WeilConjectures.AdjointCoefficientStage` is just a selector for those
existing constructions, with a positive level in the finite case. Its `category`
selector unfolds to the following existing declarations; it does not construct a
new derived category or replace a recorded definition.

| Stage | Existing declaration selected |
| --- | --- |
| Finite A(E,n), n >= 1 | `WeilConjectures.sfFiniteConstructibleFiniteTorCategory` |
| Integral O(E) | `WeilConjectures.finiteTorConstructibleIntegralCategory` |
| Rational E | `WeilConjectures.sfRationalConstructibleFiniteTorCategory` |
| Algebraically closed coefficient field | `WeilConjectures.sfCommonStageConstructibleFiniteTorCategory` |

Thus the integral case includes derived completeness, uniform boundedness and a
single Tor interval across all reductions. Rational objects live in the recorded
scalar localization, and algebraically closed objects in the common-stage
category. Neither field case is replaced by constant-coefficient sheaves on an
ordinary site. All finite coefficient fields lie inside the specified closure.

The first theorem states the conjugation, conditional isomorphism, and the two
naturality clauses. The second theorem states exactly the coefficient-chain
implication. Their only postponed proofs are `sorry`. The complete seven-step
natural-language proof from the node is in the first theorem's docstring, and the
second theorem gives the cancellation and associator argument for its own clause.
`coefficientRightMate` has real data: the target adjunction's `homEquiv` applied
to `b.inv.app (J.obj K) ≫ TY.map (adjJ.counit.app K)`.

The input correspondence, including each standing hypothesis, is as follows.

| Source hypothesis or clause | Lean rendering |
| --- | --- |
| Global finite field datum, ell different from p, fixed coefficient closure | `P : PurityFiniteSetting.{u}`; its `field` and `coefficients` are the recorded data, including primality and distinctness |
| X and Y finite type over k | `f : Arrow Scheme.{u}` packages `f.left = X`, `f.right = Y`, `f.hom = f`; the two `Over`, `LocallyOfFiniteType`, and `QuasiCompact` structure-map instances |
| f a k-morphism | `[f.hom.IsOver (Spec (.of P.field.k))]` |
| f separated of finite type | `[IsSeparated f.hom] [LocallyOfFiniteType f.hom] [QuasiCompact f.hom]` |
| Admissible source and target coefficient stages | `Λ Λ' : AdjointCoefficientStage P`, with all four cases as above |
| Given compact-support functors F and F' | `F : Λ.category f.left ⥤ Λ.category f.right` and the primed counterpart |
| The coefficient extension supplies functors on Dctf | `TX : Λ.category f.left ⥤ Λ'.category f.left` and `TY : Λ.category f.right ⥤ Λ'.category f.right` |
| Fixed right adjoints f! and the alternative J, J' | `G J`, `G' J'` between exactly those concrete categories; `adjG`, `adjJ`, `adjG'`, `adjJ'` |
| Natural isomorphism b(M) | `b : F ⋙ TY ≅ TX ⋙ F'` |
| Definition of c_J | `coefficientRightMate F F' TX TY b J' J adjJ' adjJ K` |
| Definition of c_f | The same expression with `G' G adjG' adjG` |
| Counit-compatible gamma, gamma' | `adjG.rightAdjointUniq adjJ` and its primed counterpart |
| Conjugation formula | First conjunct: `TX.map gamma.inv ≫ c_f ≫ gamma'.hom`; Lean composition is diagrammatic |
| c_f invertible implies c_J invertible | Second conjunct, with precisely an `IsIso c_f → IsIso c_J` implication |
| Naturality of c_J and c_f | Third and fourth conjuncts, for every `k : K ⟶ L` |
| Three coefficient stages | `Λ₀ Λ₁ Λ₂ : AdjointCoefficientStage P` in the chain theorem |
| Same middle adjoints in both comparisons | One `G1`, one `J1`, with their single adjunctions, shared by `b01` and `b12` |
| Successive extension identifications | `aX : TX01 ⋙ TX12 ≅ TX02`, `aY : TY01 ⋙ TY12 ≅ TY02` |
| Conditional composition identity | The displayed G equation implies the identically oriented J equation, for every K; the final factors are `G2.map (aY.hom.app K)` and `aX.hom.app (G0.obj K)`, respectively |

The node explicitly calls F and F' **given** compact-support functors and assumes
that scalar extension **supplies** TX and TY on Dctf. This statement concerns
those supplied functors and adjunctions, rather than construction/existence of
compact support or scalar extension. Accordingly the Lean binds precisely those
functor data on the actual coefficient categories. There is no extra arbitrary
unbounded pro-etale right adjoint assumption. There is no unrelated phantom ring
homomorphism: the coefficient extension enters this categorical assertion by its
supplied TX and TY, exactly as in the expanded node. The scheme arrow's endpoints
occur in every functor type, and its actual hom occurs in the geometric hypotheses.

Dependencies and exact declarations read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`. `Arrow Scheme` is just the existing packaging
  of a scheme morphism and its endpoints, from `Mathlib.CategoryTheory.Comma.Arrow`.
- `def-sf-categories`: `Sheaf.SixFunctors.SfCategories`, its finite, rational and
  common-stage finite-Tor aliases listed above. The integral category is the exact
  imported `finiteTorConstructibleIntegralCategory` from
  `Sheaf.Paper.FiniteTorAmplitude`, already used by `def-sf-categories`.
- `def-pur-conventions` (added landed dependency):
  `WeilConjectures.PurityFiniteSetting`, `Ring`, and the underlying coefficient
  datum, from `Sheaf.Paper.PurityFiniteSetting`.
- `det-sp-unique-right-adjoint` is a Mathlib leaf, not a missing Lean record:
  `CategoryTheory.Adjunction.rightAdjointUniq`,
  `homEquiv_symm_rightAdjointUniq_hom_app`, `rightAdjointUniq_hom_app_counit`,
  `rightAdjointUniq_inv_app`, from `Mathlib.CategoryTheory.Adjunction.Unique`.
- `lem-weil-pbc-adjunct-counit-identity` is the Mathlib leaf
  `CategoryTheory.Adjunction.eq_unit_comp_map_iff`, from
  `Mathlib.CategoryTheory.Adjunction.Basic`; `Adjunction.homEquiv` gives its
  forward transpose construction.
- `def-weil-pbc-adjunction-mate` is the Mathlib leaf `CategoryTheory.mateEquiv`,
  from `Mathlib.CategoryTheory.Adjunction.Mates`; `mateEquiv_counit` gives the
  exact counit equation. The pointwise helper is its source-specified transpose
  expression, not a second adjunction or mate equivalence.

Edge cases checked before finalizing: empty schemes are not excluded; identity
coefficient extensions and identity scheme maps remain allowed; finite n=0 is
excluded exactly by `hn : 1 ≤ n`; integral and both field stages are retained;
nontrivial ramification is not restricted; X and Y need not be absolutely
separated; the chain allows identity associators and genuinely nontrivial
associators; the middle adjoints agree by construction; no invertibility of b's
mate is assumed or inferred without `IsIso c_f`. No faithfulness or conservativity
of scalar extension is used. The generic transpose helper binds four independent
object universes and four independent hom universes. The theorem categories use
their recorded universe conventions, with no equality imposed between coefficient
ring size and arbitrary category hom size.

Searches (fresh repair checks as well as retained searches):

- `msearch.py ... leanfinder "Changing both chosen right adjoints conjugates a
  coefficient extension mate by the unique counit compatible isomorphisms and
  preserves its composition identity." returned eight related declarations,
  including `conjugateEquiv_mateEquiv_vcomp`, `mateEquiv_counit`,
  `mateEquiv_conjugateEquiv_vcomp`, and `iterated_mateEquiv_conjugateEquiv`.
  They supply the generic calculations but not this full four-stage/chain statement.
- `msearch.py ... loogle "CategoryTheory.Adjunction.rightAdjointUniq,
  CategoryTheory.mateEquiv"` returned zero hits for that combined query.
- `msearch.py ... grep "rightAdjointUniq|mateEquiv.*conjugate|conjugateEquiv.*mateEquiv"
  CategoryTheory/Adjunction` returned eleven hits, including Unique.lean:102,
  :105 and Mates.lean:464, :472. The full uniqueness, transpose, and mate signatures
  and docstrings were read in the pinned source, including Basic.lean:301 and
  Mates.lean:84--138. They do not replace the complete target assertion.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared
  `lean/Sheaf` for the item id, `coefficientRightMate`, and
  `AdjointCoefficientStage` found no existing declaration of this statement or
  helper selector. The retained packet also records the prior semantic searches.
- Category searches found the exact recorded aliases in SfCategories.lean and
  FiniteTorAmplitude.lean; those declarations are imported and selected unchanged.

No `STATEMENT-DISPUTED` mathematical counterexample was found. The statement-context
fault and its complete citer audit are recorded below. Per-file `scompile.py`
completed cleanly for both the sandbox and final module (9.9 s and 17.5 s in the
last run), with no errors or warnings. All compilation used the prescribed wrapper.

## Second reading by Q87

This is a fresh self-check with the corrected node, the source conventions, the
source coefficient lemma, the seven proof steps, and both Lean signatures open.
The dispatcher explicitly prohibits starting another agent; this section does not
claim that a second person or agent performed the reading.

H3, category objects: the old arbitrary C,D,C',D' binders have been removed from
both target theorems. I unfolded each of the four selector branches against its
recorded declaration, including the uniform integral Tor condition, raw rational
localization, and the common-stage category. No branch introduces an etale-origin
predicate or replaces the intrinsic pro-etale constructibility predicate. The
source's schemes appear as the actual endpoints of `f : Arrow Scheme`, so the
coefficient categories and functor types depend on those endpoints. The geometric
instance binders match the source's finite-type k-schemes and separated finite-type
k-map, without absolute separatedness. The old unused coefficient-ring hom was
removed: the node's assumed extension functors themselves are explicit data on
these categories. The coefficient stage is no longer an unrelated phantom type.

H3, universes: I checked `coefficientRightMate`'s complete binder list, not just its
inferred type. Its C,D,C',D' have independent uC,uD,uC',uD' and independent
vC,vD,vC',vD'. The original shared `Category.{u}` binders are gone. I also checked
that selector branches compile with the recorded site/coefficient size convention.
The final compile requires no added universe equality or extra instance assumption.

Conjugation clause: c_J's source is TX(JK), target J'(TYK). TX(gamma inverse)
has source TX(JK), target TX(GK); c_f ends in G'(TYK), and gamma' hom ends in
J'(TYK). `rightAdjointUniq` has direction G -> J, not J -> G. The helper uses
b inverse at JK followed by TY of the J counit, and the target J' adjunction.
These checks fix the orientation without relying on informal composition notation.

The isomorphism clause has only the one conditional antecedent specified by the
node. Each naturality equation is checked from TX(JK) to J'(TYL), respectively
TX(GK) to G'(TYL). The two equations use their own counits/adjunctions through the
helper; they are not only the naturality of gamma. No naturality clause is missing.

Chain clause: the first factor is TX12(c01), the second is c12 evaluated at TY01(K),
and the last is the action of the final right adjoint on aY(K). Both sides end at
G2(TY02 K), or J2(TY02 K), and start at TX12(TX01(G0 K)), or its J counterpart.
The right side is aX at the initial right-adjoint object followed by c02. There
are exactly three b's, six right adjoints, six adjunctions and two associators;
the same stage-1 right adjoints are used twice. The assumed G equation is the
antecedent, and the J equation is the consequent. No b-composition premise was added.

H8: I compared all seven node proof steps with the full first-theorem docstring,
including the inverse counit equation, b-naturality, equality of transposes,
explicit inverse, middle-gamma cancellation, and aX naturality. The chain theorem
also has its own complete cancellation proof in prose. Each definition/instance
has source and blueprint documentation, real data, and no sorry. Exactly the two
theorems have postponed proofs; both are clauses of this same DAG node.

H11: the hypothesis/clause table above was checked against the final signatures,
not reused from the generic returned packet. Both final signatures were also
checked for explicit variables, no stale `f`/`coeff` phantoms, and 100-column style.
The recorded `lean.statement` is extracted verbatim from the main signature.

## Statement corrected

The old statement began: "Let f:X->Y be a scheme morphism [def-pc-scheme] and
Lambda->Lambda' a coefficient extension." It did not state the source's standing
field, admissible stages, or geometric hypotheses. This was the H3 context fault.
The correction makes those conventions explicit, following the current blueprint
`sec-six-functors-basics/sk-def-purity-conv/def-pur-conventions.md`, its unit's
separated finite-type domain, and `sec-smooth-purity/sk-prop-sp-unique-adjoint/`.
The old statement is preserved verbatim in `statement_change.old_statement`.
The transpose, conjugation, conditional isomorphism, naturality and chain clauses
are unchanged. `def-pur-conventions` is the only new statement dependency.

I searched every DAG node containing the item id, then retained exactly the nodes
whose `stmt_deps` or `proof_deps` contain it. There are three actual citers:

- `lem-coef-cartesian-section-adjoint-mates`: holds. Its fixed global k and separated
  finite-type schemes/map satisfy the context, and its use is at finite stages.
- `lem-sf-constructible-exceptional-adjunction-coefficients`: holds. Its fixed global
  k, finite-type schemes and separated finite-type map match; all coefficient stages
  and the counit-normalized comparison transport remain covered.
- `lem-pur-condensed-exceptional-reconstruction`: does not hold as an application of
  this specialized source statement alone. It explicitly allows arbitrary positive
  characteristic k and also applies the calculation to Brown tower adjoints. The
  generic mate calculation remains valid, but that citer needs its own specialization.
  It is named with `holds: false` in the node and is not edited in this delivery.

The grep hit `lem-sfb-dc-proper-pushforward-left-adjoint-qlbar` mentions the id in
metadata but does not contain it in either dependency list, so it is not an actual
citer for the required audit. No target/unit statement is changed.
