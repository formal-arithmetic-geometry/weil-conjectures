## Worker report

The module Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian states
AlgebraicGeometry.isAffine_of_isFinite_surjective_of_isLocallyNoetherian with a sorry proof.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Clause matching:
- The schemes and morphism f:Y → X are `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
- Hypothesis (1), f finite, is `[IsFinite f]`.
- Hypothesis (2), surjectivity on underlying points, is `[Surjective f]`.
- Hypothesis (3), Y affine, is `[IsAffine Y]`.
- Hypothesis (4), X locally Noetherian and quasi-compact, is
  `[IsLocallyNoetherian X] [CompactSpace X]`. CompactSpace means the whole
  topological space is quasi-compact, without a Hausdorff assumption. Mathlib's
  IsNoetherian is exactly the combination of these two classes (Noetherian.lean:280).
- The conclusion, X affine, is `IsAffine X`.

Dependency declarations read and used:
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and
  AlgebraicGeometry.Scheme.Hom; Mathlib.AlgebraicGeometry.AffineScheme,
  AlgebraicGeometry.IsAffine. The affine class expresses that X → Spec Γ(X) is
  an isomorphism, equivalent to being isomorphic to an affine spectrum.
- def-weil-finite-integral-morphism: Mathlib.AlgebraicGeometry.Morphisms.Finite,
  AlgebraicGeometry.IsFinite; its full class requires an affine morphism and finite
  section-ring maps on all affine target opens. The integral clause is not used.
- def-weil-surjective-morphism: Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap,
  AlgebraicGeometry.Surjective, whose field is Function.Surjective f.
- pqf-def-locnoeth: Mathlib.AlgebraicGeometry.Noetherian,
  AlgebraicGeometry.IsLocallyNoetherian, using its recorded module and declaration.
- def-weil-pbc-scheme-conventions is a convention-only record with no declaration;
  scheme quasi-compactness is rendered by Mathlib's CompactSpace, rather than the
  vacuous hypothesis QuasiCompact (𝟙 X).

Edge cases: empty schemes are allowed, including the affine empty scheme Spec(0).
If Y is empty, surjectivity forces X empty. No Nonempty, reducedness, integrality,
separatedness, characteristic, or field hypothesis is added. Nilpotents and
reducible schemes are allowed. The explicit universe u is arbitrary, and all
variables are bound; there is no quantified test-object universe restriction.

Source check: the local literature/stacks-project/coherent.tex is absent on this
machine. Opened https://stacks.math.columbia.edu/tag/01YQ and read its statement
and proof. Its four hypotheses and conclusion agree exactly with the DAG node.
The declaration docstring carries all eight proof steps and their dependency ids,
including the zero case of devissage and the quasi-separatedness needed by Serre.

Searches (msearch.py E1 lem-weil-pbc-finite-surjective-affine-target-noetherian):
- leansearch: "A Noetherian scheme with a finite surjective morphism from an
  affine scheme is affine". Service unavailable: Internal Server Error.
- leanfinder: "A Noetherian scheme receiving a finite surjective morphism from
  an affine scheme is affine". Eight hits: local Noetherianity of finite-type
  sources, finite-morphism criteria, affine-source consequences with affine target,
  and Noetherian affine-cover criteria. None states the node.
- loogle: "AlgebraicGeometry.IsAffine, AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.Surjective". Zero hits.
- grep of Mathlib AlgebraicGeometry: "isAffine_of|IsAffine.of_|class
  IsNoetherian|class IsLocallyNoetherian". Twenty-five hits, including the exact
  Noetherian classes and unrelated affineness criteria; no finite-surjective
  Noetherian-target theorem.
- rg of WeilConjectures and lean/Sheaf: "finite.*surjective.*affine|
  affine.*surjective|isAffine_of.*finite|01YQ". The project has
  AlgebraicGeometry.isAffine_of_isFinite_surjective in
  Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget, which drops the
  Noetherian hypothesis and therefore has a different, stronger statement.
  Other hits concern relative affine lines, ring-surjective closed immersions,
  and covers. No declaration states precisely this node.
- rg of the item id in WeilConjectures: no hits.
- rg of the proposed declaration name in Mathlib, WeilConjectures and lean/Sheaf:
  no hits.

Validation: compiled the module on the server with scompile.py; the delivery dry
run is recorded by the tool output. No mathematical dispute or node fault found.

## Second reading by E1

I independently opened the delivered node and Lean module, all five statement
 dependency nodes, and the Mathlib declarations below. The source checkout has
no local Stacks directory, so I read the upstream coherent.tex directly at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
lines 3468–3476 (section context) and 3556–3617 (the lemma and proof), and
https://stacks.math.columbia.edu/tag/01YQ. The section imposes no standing
base-field, separation, or other hypothesis. No statement correction is needed.

Object/hypothesis/conclusion checklist, in the node's order:
- Objects X and Y: `{X Y : Scheme.{u}}`. Verdict: exact. Mathlib Scheme.lean:42
  defines locally ringed spaces locally isomorphic to spectra; Hom at line 74
  is a morphism of locally ringed spaces, matching def-pc-scheme.
- Morphism f:Y → X: `(f : Y ⟶ X)`. Verdict: exact direction and quantification.
- (1) f finite: `[IsFinite f]`. Verdict: exact. Finite.lean:39 extends
  IsAffineHom and requires `(f.app U).hom.Finite` on every affine target open,
  precisely def-weil-finite-integral-morphism's finite clause. Integral is not
  a separate assumption.
- (2) f surjective on points: `[Surjective f]`. Verdict: exact.
  UnderlyingMap.lean:59 has `surj : Function.Surjective f`, using the underlying
  point-map coercion, exactly def-weil-surjective-morphism.
- (3) Y affine: `[IsAffine Y]`. Verdict: exact. AffineScheme.lean:59 requires
  the canonical map to Spec Γ(Y) to be an isomorphism. Scheme.isoSpec:72,
  isAffine_Spec:119, and IsAffine.of_isIso:122 identify this with being
  isomorphic to a spectrum, the affine clause of def-pc-scheme.
- (4a) X locally Noetherian: `[IsLocallyNoetherian X]`. Verdict: exact.
  Noetherian.lean:57 is the affine-open section-ring criterion. The recorded
  pqf-def-locnoeth equivalence is independently checked at lines 101 and 131:
  an affine Noetherian cover is equivalent to this criterion, without a finite
  cover hypothesis.
- (4b) X quasi-compact: `[CompactSpace X]`. Verdict: exact scheme-level
  quasi-compactness. Topology/Defs/Filter.lean:283 has compactness of univ and
  explicitly does not assume separation. Noetherian.lean:280 defines
  IsNoetherian by exactly IsLocallyNoetherian and CompactSpace. The convention
  node defines no new predicate; no duplicate or vacuous identity-morphism
  hypothesis is introduced.
- Conclusion X affine: `: IsAffine X`. Verdict: exact, with the same affine
  notion as for Y. All hypotheses precede this single conclusion.

Edge cases: both schemes may be empty, and Spec of the zero ring is admitted;
if Y is empty, surjectivity forces X empty. Nonreduced and reducible schemes
are included. There is no field, characteristic, integrality, Nonempty,
separatedness, index-set, or numerical hypothesis. The theorem has no index
or n to exclude an empty family or n = 0. Universe u is declared and arbitrary;
the common Scheme universe is the category's standard universe, so any pair
of schemes fits after choosing a common universe. There is no test-object
quantification in a smaller universe and no unbound variable.

Independent searches, with wording different from the first reader:
- msearch leanfinder: "Chevalley affineness theorem: a finite epimorphism from
  an affine scheme onto a Noetherian scheme implies its target is affine".
  Eight hits: isFinite_iff, IsFinite.toIsAffineHom, finite affine-local
  property, LocallyOfFiniteType.isLocallyNoetherian, locallyOfFiniteType_iff,
  IsFinite.iff_isProper_and_isAffineHom, finite_app,
  noetherianSpace_of_isAffine. None is this implication.
- msearch loogle: "AlgebraicGeometry.IsNoetherian, AlgebraicGeometry.IsAffine".
  Only isNoetherian_iff_of_finite_affine_openCover; not the node's statement.
- msearch leansearch: "Affineness descends along a finite surjective morphism
  onto a Noetherian scheme". Service unavailable (Internal Server Error),
  recorded as unavailable, without claiming a negative search result.
- Independent rg over Mathlib AlgebraicGeometry, source WeilConjectures,
  and repository lean/Sheaf used "chevalley|affine.*image|affine.*surject|
  surject.*affine|01YQ" and the exact declaration name; also searched
  dag/lean_names_upstream.json for the theorem name and source label.
  Hits concern flat descent, constructibility, affine covers and unrelated
  affine schemes. I opened Sheaf/AlgebraicGeometry/FiniteSurjectiveAffineTarget.lean
  at its declaration: isAffine_of_isFinite_surjective has no Noetherian
  hypothesis and is the stronger general theorem, not an exact existing
  statement of this node. No exact duplicate was found.

H5–H9: the module introduces no definitions, hollow data, auxiliary theorems,
new nodes, or dependency modules. The only theorem proof is `by sorry`.
Its declaration and module docstrings identify 01YQ and the blueprint id;
I matched all eight documented proof steps to the node: finiteness/local
Noetherianity; zero and extension stability; summand retraction; generic
support and coherent pushforward; coherent ideal product and stalk;
projection formula and affine cohomology vanishing; devissage; Serre's
criterion with quasi-separatedness. All imports serve predicates in the
signature; namespace, file topic, and line lengths follow the conventions.
The node's lean.statement is verbatim the signature before `:=`.

Mismatches and changes: none in the mathematical statement, dependencies,
source attribution, proof docstring, or Lean code. Only this independent
second-reading section was added; the Worker report is retained.

Validation: scompile.py compiled the delivered module on the server in 1.7 s,
exit code 0, with no errors or warnings. The delivery dry run is checked before
pushing by deliver2.py.

## Review by R-fsa1141 (FIX)

Hypothesis (4), "X is Noetherian, i.e. locally Noetherian and quasi-compact", is
now `[IsNoetherian X]` (Mathlib class extending IsLocallyNoetherian and
CompactSpace), per STATE NOETHERIAN SCHEME (11:39 UTC: new statements use
`[IsNoetherian X]`; the two-class form is kept only in landed modules). The
declaration is renamed `isAffine_of_isFinite_surjective_of_isNoetherian`; the
docstring's first sentence says Noetherian. Hypotheses (1)-(3) and the conclusion
(`IsFinite`, `Surjective`, `IsAffine Y`, `IsAffine X`) were already exact; no
hollow clause, universe single and arbitrary, statement true (Stacks 01YQ; the
landed general `isAffine_of_isFinite_surjective` is the stronger 01ZT form).
Compiled clean under L; `#check` confirms `AlgebraicGeometry.IsNoetherian`.
