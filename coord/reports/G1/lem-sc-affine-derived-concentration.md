## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AffineDerivedConcentration.lean` states
`AlgebraicGeometry.affine_derived_concentration`, with one `sorry` and no definitions.
The node is unchanged except for its `lean` record. No new nodes or dependency modules
are required.

Hypothesis and clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`; scheme morphism f: `(f : X ⟶ Y)`.
- Affineness of f: `[IsAffineHom f]`, Mathlib's predicate that inverse images of affine
  opens are affine. X and Y themselves need not be affine.
- E in D_QCoh(X): `(E : schemeDerivedCategory X)` and
  `(hE : schemeDerivedQCohProperty X E)`. The latter says every integer-degree
  cohomology sheaf is quasi-coherent. This is exactly the object predicate of the
  recorded full subcategory, with the underlying derived object retained for Rf_*.
- The `HasDerivedCategory.{wX}` and `HasDerivedCategory.{wY}` binders are the localization
  structures required by the recorded definitions, with separate morphism universes.
  They impose no geometric finiteness, boundedness or base-field assumption.
- E represented by a quasi-coherent sheaf in degree zero: the left existential
  `∃ F : SheafOfModules.{u} (moduleRings X.toRingedSpace), F.IsQuasicoherent ∧
  Nonempty (E ≅ (DerivedCategory.singleFunctor ... 0).obj F)`.
- Rf_*E represented by a quasi-coherent sheaf in degree zero: the right existential
  with G over Y and `(schemeDerivedDirectImage f).obj E`. Mathlib's `singleFunctor`
  sends a module to the single cochain complex in the displayed integer degree.
- “If and only if”: `↔` between these two existentials, the first conjunct.
- “In that case the degree-zero sheaf is f_*E”: the second conjunct quantifies over
  each quasi-coherent F representing E, and gives
  `Nonempty ((schemeHigherDirectImage f 0).obj E ≅
  (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj F)`.
  Thus H^0(Rf_*E) is f_*F. The node's f_*E denotes ordinary direct image of the
  degree-zero representing sheaf, as its proof explicitly says; it is not ordinary
  direct image applied to a bare derived-category object. The conditional binders
  introduce the representing module and its isomorphism, not extra global hypotheses.
  Any degree-zero representing sheaf on Y is isomorphic to this H^0, so this renders
  the whole identification clause.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  Scheme is a locally ringed space locally isomorphic to Spec, and Hom is a morphism
  of underlying locally ringed spaces. Imported through both module imports.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, and its full-subcategory interpretation
  `schemeDerivedQCohCategory`. Imported through SchemeDerivedDirectImage.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`,
  `schemeHigherDirectImage`. Their full definitions and docstrings were read.
  The former is the ringed-space K-injective derived module pushforward;
  the latter is its composition with `DerivedCategory.homologyFunctor`.
- Its shared dependency `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `AlgebraicGeometry.RingedSpace.moduleDirectImage` is ordinary module pushforward
  along inverse images of opens, with the scalar action from the structure-sheaf map.
  This keeps the ordinary and derived pushforward on the same carrier/category instance.
- Mathlib's `DerivedCategory.singleFunctor`, `DerivedCategory.homologyFunctor`, and
  `AlgebraicGeometry.IsAffineHom` were also inspected in their defining source files.

Source check: local `literature/stacks-project/perfect.tex` is absent on this machine.
Read the official Stacks pages instead:
[0AVW](https://stacks.math.columbia.edu/tag/0AVW),
[08I8](https://stacks.math.columbia.edu/tag/08I8), and
[01XC](https://stacks.math.columbia.edu/tag/01XC).
The proof of 0AVW identifies H^i(Rf_*E) with f_*H^i(E); 08I8 supplies conservativity,
and 01XC supplies positive-degree vanishing for affine pushforward of quasi-coherent
modules. These support the node without extra Noetherian or boundedness assumptions.
The theorem docstring contains all three proof steps and their node citations.

Edge cases checked before writing:

- Identity morphism: the equivalence reduces to degree-zero representation of E on
  both sides, and the final clause is the ordinary identity-pushforward identification.
- Zero E: the zero quasi-coherent module represents it; both degree-zero sheaves are zero.
- Empty X (also empty Y when a morphism exists): the module category on X has only the
  zero module up to isomorphism; its direct image is zero. No nonemptiness is imposed.
- Affine Spec(A) → Spec(B): pushforward is restriction of scalars on quasi-coherent
  modules. It is exact and detects zero modules, so reflects concentration; this does
  not require A to be finite, flat, or nonzero.
- Unbounded E: all cohomology degrees in `schemeDerivedQCohProperty` are integers;
  there is no boundedness binder. Negative degrees and positive degrees are both covered
  by the single-degree representation, without a change to D-plus.
- No characteristic restriction, qcqs assumption on the whole schemes, or finite-type
  hypothesis is introduced. Universes u, wX, wY are explicitly declared, and all
  variables are explicitly bound. No file-local notation or instance is introduced.

Searches for an existing statement:

- `msearch.py ... leanfinder "affine scheme morphism derived pushforward reflects
  complexes represented by quasi coherent sheaves in degree zero"`: eight results,
  all ordinary pushforward/adjunction/sheaf pushforward declarations, no concentration theorem.
- `msearch.py ... loogle "DerivedCategory.singleFunctor, IsAffineHom"`: no results;
  service reported unknown identifier IsAffineHom. Located the actual declaration by rg.
- `msearch.py ... leansearch "affine derived pushforward concentrated degree zero quasi
  coherent"`: unavailable, Internal Server Error. No mathematical verdict drawn from it.
- `msearch.py ... grep "affine.*derived|derived.*affine|pushforward.*exact"
  AlgebraicGeometry`: two hits in Mathlib Modules/Sheaf.lean about pushforward
  congruence/adjunction, no theorem matching this node.
- `rg -n 'lem-sc-affine-derived-concentration|affine.*derived|derived.*affine'`
  over source WeilConjectures and project lean/Sheaf: related material and docstring
  citations only, no declaration of this equivalence with the identification clause.
- `rg -n 'affine.*degree|degree.*affine|concentrat'` over the AlgebraicGeometry
  trees: unrelated concentration, perfect-complex, and curve/cohomological-dimension results.
- `grep -rn 'lem-sc-affine-derived-concentration'` over source WeilConjectures:
  no matches.
- `rg -n 'affine_derived_concentration'` over Mathlib, WeilConjectures, project
  lean/Sheaf, and dag/lean_names_upstream.json: no collision.

Validation: `scompile.py G1 lem-sc-affine-derived-concentration` on the delivered
module returned exit code 0 (3.8 s), with no errors or warnings. Only the theorem
proof is postponed. No statement dispute or correction was necessary.

Dry-run resolution: the server sandbox lacked the compiled object for the recorded dependency module `SchemeDerivedDirectImage`. The dependency source and node were included unchanged in this packet so `scompile.py` could compile both modules together; the item theorem uses the same recorded declarations. Because the combined check shares universe declarations, the item module uses explicitly renamed universes `uA`, `wXA`, and `wYA` (with no semantic change). `deliver2.py G1 lem-sc-affine-derived-concentration --no-push` now prints `OK (dry run)`: compilation and preflight pass; only the required second-reading section remains for the delivering worker.


## Second reading by G1

I read the item node, its complete theorem signature and proof docstring, all three
statement-dependency nodes and their defining declarations. I also read the copied
SchemeDerivedDirectImage module against def-pc-derived-direct-image and read its shared
RingedSpaceDerivedDirectImage dependency, including the ordinary module pushforward.

Source reading: the repository has no literature/stacks-project directory. I downloaded
upstream Stacks perfect.tex and coherent.tex into this item's scratchpad, then read
perfect.tex conventions (lines 27-74), the complete affine-morphisms section
(lines 628-780), and coherent.tex lemma-relative-affine-vanishing (lines 180-200).
I also checked the official tag pages 0AVW, 08I8 and 01XC. The section assumes arbitrary
schemes and an affine morphism, with no Noetherian, qcqs, finite-type, flatness,
nonemptiness, characteristic or boundedness assumption. The conventions view a module
as its single complex in degree zero. The cohomology identity in the proof of 0AVW,
and the conservativity in 08I8, give exactly the node's concentration assertion.

Item-by-item statement list and verdicts:

1. Objects X and Y are arbitrary schemes; f is a morphism X to Y. Rendered by
   `{X Y : Scheme.{uA}}` and `(f : X ⟶ Y)`. PASS. Read Mathlib Scheme and Scheme.Hom:
   locally affine locally ringed spaces and morphisms of underlying locally ringed spaces.
2. Hypothesis f is affine. Rendered by `[IsAffineHom f]`. PASS. Read the class in
   Mathlib Morphisms/Affine: every affine open in Y has affine inverse image in X.
   Neither scheme is required to be globally affine.
3. Object E lies in D_QCoh(X). Rendered by `(E : schemeDerivedCategory X)` and
   `(hE : schemeDerivedQCohProperty X E)`. PASS. Read DerivedCategory.lean:
   D(O_X) uses the shared SheafOfModules category; the property quantifies over every
   integer n and asserts that H^n(E) is quasi-coherent. This is exactly the objects
   of the recorded full subcategory, not D(QCoh(X)) or a bounded subcategory.
4. Structures needed to construct these derived categories. The two
   `HasDerivedCategory.{wXA/wYA}` binders are the recorded localization structures
   for the shared module categories. PASS. The separate morphism universes are
   explicit, and the geometric universe uA is arbitrary. There is no independent
   small test-object universe making a hypothesis vacuous, or added geometric premise.
5. Left conclusion: E is represented by a quasi-coherent sheaf in degree zero.
   Rendered by `∃ F : SheafOfModules.{uA} (moduleRings X.toRingedSpace),
   F.IsQuasicoherent ∧ Nonempty (E ≅ (DerivedCategory.singleFunctor ... 0).obj F)`.
   PASS. Read Mathlib singleFunctor (Basic.lean) and IsQuasicoherent
   (ModuleCat/Sheaf/Quasicoherent.lean); no finite presentation is required.
6. Right conclusion: Rf_*E is represented by a quasi-coherent sheaf in degree zero.
   Rendered by the corresponding existential G over Y and the displayed isomorphism
   from `(schemeDerivedDirectImage f).obj E` to `singleFunctor ... 0` applied to G.
   PASS. The scheme-derived-direct-image abbreviation uses the recorded unbounded
   ringed-space derived direct image of `f.toLRSHom.toShHom`, not an underived map.
7. Equivalence of those conclusions. Rendered by the `↔` in the first conjunct.
   PASS. Both existentials are under the same arbitrary E and hE; no representing
   sheaf is presumed as an extra global hypothesis.
8. Conditional identification of the degree-zero sheaf with f_*E. Rendered by the
   second conjunct, `∀ F`, conditional on F being quasi-coherent and representing E,
   with `Nonempty ((schemeHigherDirectImage f 0).obj E ≅
   (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj F)`.
   PASS. schemeHigherDirectImage is Rf_* followed by the integer-degree homology
   functor, so this says H^0(Rf_*E) is f_*F for every representing F. Every G in
   conclusion 6 is isomorphic to H^0(Rf_*E), by Mathlib's
   singleFunctorCompHomologyFunctorIso, whose signature I read. This is precisely
   the node's identification, interpreting f_*E as pushforward of its degree-zero
   representing sheaf, as the node's proof explicitly does.

Edge cases: PASS. Zero E is represented by the zero quasi-coherent sheaf, and its
pushforward is zero. Empty X can map to nonempty Y; the worker report's parenthetical
suggesting Y must also be empty is incorrect, but the Lean imposes no such restriction.
If Y is empty, a morphism to it forces X empty; both module categories have only zero
objects up to isomorphism. No nonempty index or point is assumed. Degree zero is the
integer zero in singleFunctor and schemeHigherDirectImage; negative and positive
cohomology are both covered, even for unbounded E. There is no characteristic premise.
For Spec(A) to Spec(B), ordinary pushforward is restriction of scalars, which is exact
and detects zero modules for arbitrary commutative rings, including the zero ring.
The common scheme universe is the category convention of all recorded dependencies;
arbitrary larger objects are covered by choosing uA larger. Every variable/universe
is explicitly bound; no file-local notation, local instance, let or show occurs.

Independent searches (in addition to the first worker's recorded searches):

- LeanFinder: "direct image under affine morphisms detects cohomology concentrated
  in a single degree". Eight hits, about affine transition limits and the ordinary
  IsAffineHom predicate, not this theorem.
- Loogle: "DerivedCategory.singleFunctor". Twelve hits, including the singleFunctor
  and its homology comparison, whose definitions/signatures I inspected; no affine
  derived concentration theorem.
- LeanSearch: "An affine scheme morphism reflects vanishing of nonzero cohomology
  degrees under derived direct image". Service unavailable (Internal Server Error);
  no mathematical conclusion drawn from the unavailable search.
- msearch grep: "affine.*concentr|concentr.*affine|derived.*pushforward" in
  AlgebraicGeometry. No hits.
- Direct rg with "concentrat", "t.exact", "reflects.*[Ii]so", "affine_derived"
  across Mathlib and source AlgebraicGeometry and project lean/Sheaf/AlgebraicGeometry;
  also "affine.*derived|derived.*affine|concentrat" across source/project
  CategoryTheory. Related conservativity, generic concentration and ordinary
  affine pushforward results only. AffineDerivedPushforwardConservative is about
  morphisms being isomorphisms and does not state this object's concentration and
  degree-zero identification clauses. No existing exact declaration found.

Repairs and dependency review: no mathematical mismatch in the theorem or its node.
The copied SchemeDerivedDirectImage module is byte-for-byte the landed shared module;
its definitions genuinely render the dependency node, but its record was already
usable. An absent compiled artifact is not an unusable definition and does not justify
re-delivering that module (H4/H13). The current server now compiles the item alone
against this shared import, so I removed the redundant dependency module and node copy
from the delivery. No new nodes or dependency modules remain. The worker report's
historical dry-run explanation is superseded by this check. The theorem is unchanged,
and its node lean.statement remains verbatim its file signature. Its only proof is
`sorry`, with all three node proof steps and their dependencies in the docstring;
there are no new definitions, hollow definitions or proved statements.

Validation: scompile.py G1 lem-sc-affine-derived-concentration on the item module alone
returned exit code 0, compiled in 4.0 seconds, no errors or warnings. The final dry run
and delivery below validate the resulting single-module packet again.
