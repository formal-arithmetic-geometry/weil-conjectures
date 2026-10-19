## Worker report

The module `Sheaf.Paper.ProjectionFormulaTotalization` states
`SheafOfModules.ringedProjectionFormula_totalization`, with its sole proof `sorry`.
It asserts both inverse equations for the actual pair constructed by
`SheafOfModules.ringedProjectionFormulaArrows`. There are no new definitions,
no statement correction, and no dependency repair.

Source read: the full blueprint lemma 1267 at
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lemma-weil-pbc-projection-formula-totalization.md`,
its expanded five-step DAG proof, and the full declaration and docstring of
`ringedProjectionFormulaArrows` in `Sheaf.Paper.ProjectionFormulaArrows`.

Hypothesis and clause matching:

- The implicit context h,E,F is exactly that of the statement dependency
  `def-weil-pbc-projection-formula-arrows`. Its declaration's binders are retained
  verbatim, rather than replacing the canonical arrows with abstract morphisms.
- Small sites and ring sheaves are `C D : Type u`, `Category.{u}`, topologies
  `JC JD`, and `R S RI : Sheaf ... CommRingCat.{u}`. This is the same universe
  convention as the recorded dependency; no new size condition is introduced.
- The ringed-topos morphism is `uInv`, `uPush`, `adj`, finite-limit preservation,
  algebraic inverse-image lift `I`, and coefficient ring map `c`.
- Ordinary module pullback is `uStar`, fixed on objects and maps by `hobj hmap`.
  Its module direct image and adjunction are `V am`; additivity is retained.
- Unbounded derived categories are the two `HasDerivedCategory.{w}` instances.
  `LF epsilon hLF` present left-derived pullback; `PR PS hPR hPS` specify K-flat
  complexes with flat terms. `TR TS rR rS` present derived tensor through its
  K-flat representative comparisons. `k` is the canonical ordinary tensor
  comparison, not an arbitrary comparison isomorphism.
- `RF eta hRF computeR` present the K-injective total right derived direct image.
  `computeL` presents computation of pullback on K-flat flat-term representatives.
  `adjD canonicalAdj` fix the canonical derived adjunction and its counit.
  These are the infrastructure already required by the arrow definition.
- The arbitrary derived object E is `E`; `K hK repE` give its K-injective
  representative, with no boundedness condition on K or E.
- The bounded finite-projective complex is `F` together with strict-perfect
  degreewise splitting package `P` and the exact finite support condition
  `hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)`.
  This is the specified localized package in the node's proof, not an extra
  compatibility condition on splittings and differentials.
- Pi and rho are respectively `.1` and `.2` of `ringedProjectionFormulaArrows`
  applied to all the preceding parameters. In Lean composition order,
  `pi ≫ rho = 𝟙 (TR.obj (RF.obj E, Q.obj F))` is rho pi = 1.
  `rho ≫ pi = 𝟙 (RF.obj (TS.obj (E, LF.obj (Q.obj F))))` is pi rho = 1.
  These two equations express that these specified arrows are inverse
  isomorphisms; neither is replaced by a bare existence or IsIso assertion.

Dependency declarations used: `Sheaf.Paper.ProjectionFormulaArrows`,
`SheafOfModules.ringedProjectionFormulaArrows` (the sole statement dependency).
All recorded proof-dependency modules are also imported without `public`.
The projective-summand proof dependency has no Lean record yet, so has no import;
its future import is for the maintainer after it lands. No import is needed
from an unstated node to express this statement.

Edge cases checked: F=0 and empty finite-free summands (N=0) are allowed by P;
the support interval may be empty; E=0 is allowed; K and E may be unbounded;
negative total degrees and nontrivial differential signs are retained by the
canonical arrow definition; splittings need not be compatible with dF.
No nonempty-site, nonzero-ring, positive-rank or nonempty-support hypothesis.

Searches actually run:

- msearch leanfinder, "Derived projection formula arrows for bounded finite
  projective complexes are mutually inverse": eight hits, all generic
  projective-resolution comparison facts or left-derived degree-zero facts,
  none the ringed-topos statement or specified total arrows.
- msearch loogle, `CategoryTheory.IsIso, "total"`: zero hits.
- msearch grep, `projectionFormula|projection_formula`: zero Mathlib hits.
- msearch leansearch, "Derived projection formula for bounded finite projective
  coefficients inverse totalization": service unavailable (Internal Server
  Error), recorded as unavailable, not no match.
- rg `projectionFormula|projection_formula|ringedProjectionFormula` in upstream
  WeilConjectures and lean/Sheaf: upstream abstract trace-formula packages and
  etale finite-pushforward results; project scheme/open-locality results; and
  the canonical arrow dependency used here. None is this inverse assertion.
- grep of the exact item id in upstream WeilConjectures: no occurrence.

Validation uses the prescribed unmodified `scompile.py` and
`deliver2.py --no-push` wrappers, including the authorized local side-project
overlay and library confirmation. The earlier server-only workaround is obsolete
and is not used in this resumed attempt. No library build or proof is performed.

## Earlier second reading (a previous round; superseded)

I independently read the sandbox node and complete statement module, the blueprint
source of lemma 1267, the expanded five-step DAG proof, the full signature and body
of `SheafOfModules.ringedProjectionFormulaArrows`, and the coefficient-package
structure. The node's source is the blueprint markdown, not a Stacks tag; its
ambient hypotheses are supplied explicitly by definition 1264. No statement
correction, new definition node, or dependency module is needed.

Object, hypothesis, and conclusion inventory, matched independently:

1. The small sites underlying the source and target topoi are `C D : Type u`
   with `Category.{u}` and topologies `JC JD`. The commutative coefficient sheaves
   are `R`, `S`, and the inverse-image ring `RI`, all in `CommRingCat.{u}`.
   Verdict: precisely the chosen-universe small-site convention of definition 1264;
   no Noetherian, scheme, field, characteristic, or finiteness assumption.
2. The ringed-topos morphism h is rendered by `uInv`, `uPush`, `adj`,
   `[PreservesFiniteLimits uInv]`, `I : AlgebraicInverseImage uInv R RI`, and
   `c : RI ⟶ S`. Verdict: the same inverse-image adjunction and coefficient map
   as the dependency, rather than a morphism of schemes or a special site map.
3. Its ordinary module pullback is `uStar` with `hobj` and `hmap`, which specify
   extension of scalars after `I.modules` on both objects and morphisms. `V am`
   specify its module right adjoint; both additive instances are retained.
   Verdict: exactly the ordinary module adjunction used to construct the arrows.
4. The unbounded derived categories use `[HasDerivedCategory.{w} ...]` on both
   sides. `LF epsilon hLF` specify left-derived pullback. `PR PS hPR hPS`
   select exactly K-flat complexes with flat terms. `TR TS rR rS` specify the
   two derived tensor functors through their representative comparisons.
   Verdict: the dependency's derived operations, with no boundedness on E or K.
5. `k : CanonicalRingedTensorComparison ...` is the specified ordinary tensor
   comparison. The dependency body uses its `mu` and `naturality`, the ordinary
   unit normalization, and `ringedTopoiCanonicalDerivedTensorComparison` for the
   derived comparison. Verdict: no arbitrary tensor isomorphism is substituted.
6. `RF eta hRF computeR` specify total right-derived direct image and its
   K-injective computation. `computeL` gives the K-flat computation of LF.
   `adjD canonicalAdj` require the counit induced by the ordinary adjunction
   on K-injective representatives. Verdict: these parameters present the
   canonical infrastructure already used by definition 1264, rather than
   assuming the desired projection formula or an unrelated adjunction.
7. E is the arbitrary source derived object `E`. `K hK repE` give its chosen
   K-injective representative. Verdict: all E are covered; the representative
   is part of the construction in definition 1264, not a perfection assumption.
8. The bounded finite-projective coefficient complex is `F` with
   `P : StrictPerfectCoefficientPackage ... F` and `hbounded`. I opened the
   structure: `N : ℤ → ℕ`, degreewise `i` and `p` to/from the finite product
   of copies of the coefficient unit, and `i r ≫ p r = 𝟙`. There is no
   chain-map condition on those splittings. `hbounded` is exactly vanishing
   outside some integer interval. Verdict: the stipulated localized strict
   package, with no additional compatibility or positive-rank hypothesis.
9. Pi is component `.1` of the dependency's actual `ringedProjectionFormulaArrows`.
   Its body is `derivedProjectionFormulaMate` using the canonical comparison;
   I also opened upstream `Adjunction.rightAdjointProjectionMap` and checked
   its counit-mate formula. Rho is component `.2`: `eB.hom ≫ Q.map s ≫ eC.inv`,
   where s is `tensorAdjunctionTotalInverse` and the dependency's summand theorem
   characterizes it by the prescribed finite-free inverse and retract formula.
   Verdict: the two specified arrows, not independently quantified morphisms.
10. The first conclusion is `.1 ≫ .2 = 𝟙 (TR.obj (RF.obj E, Q.obj F))`, which
    is rho pi = 1 in mathematical composition order. The second is
    `.2 ≫ .1 = 𝟙 (RF.obj (TS.obj (E, LF.obj (Q.obj F))))`, which is pi rho = 1.
    Verdict: both clauses of the source, with the correct identity objects and
    every parameter passed identically in all four arrow applications. Together
    these equations express exactly inverse isomorphisms, not mere existence.

Edge cases: `N r = 0` is allowed (`Fin 0` gives the empty finite product).
F and E can be zero; bounds can give an empty support interval; F can be
concentrated in degree zero or in negative degrees. K and E remain unbounded.
No object of either site, nonempty site, nonzero ring, or fixed characteristic
is required; an empty scheme is therefore not excluded by an ambient hypothesis.
The ordinary signed tensor total used by the dependency preserves (a,r), so its
vertical sign remains (-1)^a, including negative total degrees. No extra universe
equality is introduced: `u` and `w` are explicitly bound and exactly those of the
recorded arrow interface. Smallness is the source's chosen size convention.

Independent H4 searches (different wording from the first reader):

- `msearch leanfinder`: "projection formula bounded perfect complex tensor
  derived direct image inverse" returned eight generic Tor, left-derived, and
  complex-unitor hits; none states these canonical inverse equations.
- `msearch loogle`: `"projection", "tensor"` returned zero hits.
- `msearch leansearch`: "A bounded complex of finite projective sheaves satisfies
  the derived projection formula for a morphism of ringed topoi" was unavailable
  (Internal Server Error); this is not evidence of absence.
- `msearch grep`: `rightAdjointProjectionMap|tensorAdjunctionTotal` returned no
  Mathlib matches. Direct rg across Mathlib, upstream WeilConjectures, and
  project lean/Sheaf for `projectionFormula`, `projection_formula`,
  `ringedProjectionFormula`, and projection/total combinations found upstream
  abstract trace-formula packages and finite-etale results, scheme/open-locality
  results, and definition 1264's arrow helpers. None is this statement. The
  upstream right-adjoint projection-map definition was opened and checked: it
  constructs the forward mate, not the inverse theorem for bounded coefficients.
  Definition 1264's ordinary `tensorAdjunctionTotal_isIso` concerns chain maps,
  not the identification with the canonical derived counit mate asserted here.

H5/H6/H8/H9 checks: this delivery adds no definitions and has exactly one named
statement with whole proof `sorry`. Its module and theorem docstrings cite
lemma 1267 and the correct blueprint id. The theorem docstring follows the five
DAG steps: representative computations, bidegree inverses, differential
naturality, signed finite totalization, and identification with the canonical
mate and specified inverse. All recorded proof-dependency modules are imported;
`lemma-weil-pbc-projection-formula-projective-summand` still has no Lean record,
so there is no module to import for it. All source lines are at most 100
characters. There are no hidden `let`/`show` binders or file-local notations.
The node's `lean.statement` equals the complete theorem signature verbatim,
including whitespace, and all variables and universes are visibly bound.

Mismatches found and changes: none in the Lean, node, or source correspondence;
these are retained unchanged. I added this independent reading and fresh
validation. The worker report's server-only workaround reflects an earlier
brief: this reading uses the prescribed unmodified scompile.py and deliver2.py
wrappers directly under the current parallel-landing authorization.

Fresh second-reader validation: direct scompile.py completed successfully with
no errors or warnings (local overlay and library confirmation). The first
unmodified delivery dry run reached clone refresh but its SSH git fetch connection
was closed by the server; this was a transport failure, and the wrapper is retried.

The retry failed identically at `git fetch -q origin`: SSH connection closed,
followed by "fatal: Could not read from remote repository." The mathematical
second reading and clean compilation are complete. No delivery dry run has
passed and nothing has been pushed by this reader; delivery is blocked by the
wrapper's server Git connection, not by a missing mathematical dependency.

## Resumed validation (2026-10-15)

Reopened the current node, blueprint lemma 1267, and the full recorded arrow
declaration and its docstring. The theorem retains the dependency signature
and asserts precisely the two inverse equations. The earlier searches and
independent second reading above remain applicable. Direct unmodified
`scompile.py NI lemma-weil-pbc-projection-formula-totalization` passed both
the sandbox and library confirmation without errors or warnings. The dry run
is retried through the unmodified delivery wrapper; the earlier SSH failures
above are historical outcomes, not a mathematical dependency wait.

The unmodified dry run printed OK: commit c2520b73f1 passes preflight and
compiles; nothing was pushed. A final dry run includes this refreshed report.

## Second reading by NI

I independently read the sandbox node and theorem, blueprint lemma 1267 and
its definition 1264, the recorded arrow dependency's full signature and body,
and the degreewise splitting structure. The source is blueprint markdown,
not a Stacks lemma with additional ambient hypotheses. No statement correction,
new node, or dependency module is needed in this delivery.

Object/hypothesis/conclusion inventory and correspondence:

1. Ringed topoi and their morphism h: `C D`, `JC JD`, coefficient sheaves
   `R S RI`, `uInv uPush adj`, finite-limit preservation, `I c`.
   `uStar hobj hmap` fix pullback as inverse image followed by scalar extension;
   `V am` fix its right adjoint. Verdict: the same ringed-topos data as definition
   1264, with no scheme, Noetherian, field, or characteristic restriction.
2. Derived operations: `LF epsilon hLF`, `RF eta hRF computeR computeL`,
   `adjD canonicalAdj`, and `TR TS rR rS` with `PR PS hPR hPS` specify derived
   pullback, direct image, their canonical adjunction, and derived tensors.
   `k` is the canonical ordinary tensor comparison. Verdict: these are exactly
   the infrastructure parameters of the recorded arrows, not arbitrary pi/rho
   or a hypothesis asserting the projection formula. I checked the dependency
   body: pi uses the canonical derived comparison and counit mate; rho uses
   `tensorAdjunctionTotalInverse` conjugated by representative comparisons.
3. Arbitrary E: `E K hK repE`. Verdict: K is a chosen K-injective representative
   of E; neither E nor K is required to be bounded or perfect.
4. Bounded finite-projective coefficient complex: `F P hbounded`.
   `StrictPerfectCoefficientPackage` has ranks `N : ℤ → ℕ`, inclusions `i r`,
   retractions `p r`, and `i r ≫ p r = 𝟙`; no compatibility with the differential
   is imposed. `hbounded` is vanishing outside an integer interval. Verdict:
   exactly the strict package on the localization stipulated in definition 1264
   and the expanded node proof, including boundedness.
5. Specified total arrows: `.1` and `.2` of `ringedProjectionFormulaArrows`
   with identical parameters at every occurrence. Verdict: uses the dependency's
   actual constructions and does not replace them with existential morphisms.
6. First inverse equation: `.1 ≫ .2 = 𝟙 (TR.obj (RF.obj E, Q.obj F))`.
   Verdict: rho composed with pi is the identity on the source, in Lean's
   diagrammatic composition order.
7. Second inverse equation: `.2 ≫ .1 = 𝟙 (RF.obj (TS.obj (E, LF.obj (Q.obj F))))`.
   Verdict: pi composed with rho is the identity on the target. Together the two
   clauses say precisely that the specified arrows are inverse isomorphisms.

Edge cases: rank zero uses `Fin 0`, and F=0, E=0, empty support, degree zero,
negative degrees, and unbounded K are allowed. There is no nonempty-site,
nonzero-ring, positive-rank, or characteristic hypothesis. Empty schemes are
not excluded. The explicitly bound universes `u w` are exactly those of the
recorded arrow interface; no additional equality or instance has been imposed.
The finite tensor total retains both bidegrees and hence the sign (-1)^a.

Fresh independent H4 searches with different wording:

- LeanFinder: "Signed tensor totalization of the counit projection map for
  strictly perfect coefficients has a canonical inverse" returned eight
  complex-unitor, graded-tensor and Dold-Kan facts; none is this statement.
- Loogle: `"projection", "inverse"` returned two linear-map projection/retract
  facts, not ringed-topos derived tensor statements.
- LeanSearch: "The projection formula morphism and the finite totalized retract
  inverse are mutually inverse for bounded finite projective sheaf complexes"
  was unavailable (Internal Server Error), not evidence of absence.
- Direct rg on Mathlib, upstream WeilConjectures, and project lean/Sheaf used
  projection/perfect, projection/totalization, and rightAdjointProjectionMap.
  The abstract projection-map infrastructure and the arrow dependency do not
  assert the two derived inverse equations here. The dependency's ordinary
  chain-map inverse theorem does not identify that chain map with the canonical
  derived counit mate, which is the remaining content of this statement.

H5/H6/H8/H9: no new definition, exactly one named theorem with proof `sorry`;
source and blueprint docstrings are present and the theorem docstring follows
all five expanded proof steps. All currently recorded proof-dependency modules
are imported. The projective-summand proof node has no recorded module yet.
All lines satisfy 100 columns. No file-local notation, hidden let/show binder,
unbound variable, or extra conclusion occurs. A mechanical extraction confirmed
that `lean.statement` equals the complete source signature verbatim.

Mismatches found: none. The Lean and node are retained unchanged; this reading
adds the required current review section and fresh search/validation evidence.
The prescribed scompile.py compiled the sandbox and library confirmation cleanly
on 2026-10-15, with no errors or warnings. Delivery uses only the authorized
unmodified wrappers; earlier transport failures in this report are historical.
