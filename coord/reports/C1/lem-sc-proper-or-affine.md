## Worker report

The module `Sheaf.AlgebraicGeometry.IsProperOrIsAffine` states
`AlgebraicGeometry.IsConnectedCurve.isProper_or_isAffine`, with `sorry` as its only proof.
No definitions, dependency modules, or new nodes are needed. The item's node changes only
in `lean`.

Hypothesis and clause correspondence:

- A field k: `{k : Type u} [Field k]`, using `Field` from
  `Mathlib.Algebra.Field.Defs` (the mathlib_match of def-weil-field).
- The curve notion of def-sc-curves requires algebraic closure: `[IsAlgClosed k]`.
  This is already stipulated by that definition and explicitly acknowledged by the node's
  first proof step; it is not an additional restriction on that notion.
- A scheme C over k: `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`.
- A separated finite-type curve: `[IsConnectedCurve f]` extends `IsCurve f`, whose
  fields are `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, and
  `topologicalKrullDim C ≤ 1`.
- A connected curve in exactly the dependency's sense: the same class has
  `connectedSpace : ConnectedSpace C` (including nonemptiness) and
  `krullDim_eq_one : topologicalKrullDim C = 1`.
- Smooth over k: `[Smooth f]`.
- Proper over k: the left disjunct `IsProper f`.
- Affine over k, meaning an affine scheme as def-sc-curves specifies: the right
  disjunct `IsAffine C`. Since the base is Spec k this is also affineness over k.
- Either conclusion: `IsProper f ∨ IsAffine C`, an inclusive disjunction.

Dependency declarations used: `WeilConjectures.AlgebraicGeometry.Curve` supplies
`AlgebraicGeometry.IsCurve` (recorded for def-sc-curves) and its existing specialization
`AlgebraicGeometry.IsConnectedCurve`. I read both full signatures and docstrings. The
specialization exactly supplies connectedness, nonemptiness, and dimension one; no
replacement of the recorded dependency is necessary. `Field` is the recorded Mathlib leaf.
Other standard predicates are `IsAlgClosed` from
`Mathlib.FieldTheory.IsAlgClosed.Basic`, `AlgebraicGeometry.Smooth` from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, and `AlgebraicGeometry.IsAffine` from
`Mathlib.AlgebraicGeometry.AffineScheme` (available through the used imports).

Edge cases checked before writing: the empty scheme and Spec k are curves in the broad
IsCurve sense but are not connected curves in def-sc-curves, since dimension must equal
one. Disconnected curves are likewise excluded by the given hypothesis. No characteristic
restriction is imposed. Proper projective curves and affine curves give the respective
branches. The empty/nonempty compactification boundary is precisely the case split in the
node proof, reproduced in the declaration docstring. There is no assumption of a rational
point, projectivity, or geometric connectedness beyond the stated curve conditions.
The universe `u` is explicitly bound and arbitrary, matching the existing scheme library.
No auto-implicit variables occur.

Source check: the local literature directory does not contain varieties.tex on this
machine. I opened https://stacks.math.columbia.edu/tag/0A28 (Stacks Lemma 33.43.11),
which states affineness for separated finite-type schemes of dimension at most one with
no proper dimension-one irreducible component. Its application to a smooth connected
curve agrees with the node. No statement fault or dispute was found.

Searches for an existing statement:

- msearch.py LeanFinder: "A smooth separated connected curve over an algebraically closed
  field is proper or affine". Eight hits concerned proper morphisms, affine space, and
  affineness; none stated this dichotomy.
- msearch.py Loogle: "AlgebraicGeometry.IsCurve, AlgebraicGeometry.IsProper,
  AlgebraicGeometry.IsAffine". Zero hits; IsCurve is not in the service's index.
- msearch.py LeanSearch: "A smooth separated connected curve over a field is proper or
  affine". Service unavailable (Internal Server Error); no verdict is inferred.
- msearch.py grep in Mathlib AlgebraicGeometry:
  `proper_or_affine|isProper_or_isAffine|IsProper.*∨.*IsAffine|IsAffine.*∨.*IsProper`.
  Zero hits.
- Local rg of that same disjunction/name pattern in Mathlib, WeilConjectures, and
  lean/Sheaf: zero hits. Broader curve searches located the existing curve classes in
  WeilConjectures/AlgebraicGeometry/Curve.lean, which are reused.
- Local rg for `proper_or_affine|isProper_or_isAffine|lem-sc-proper-or-affine` in
  dag/lean_names_upstream.json, WeilConjectures, and lean/Sheaf: zero hits.

Validation: server single-file compilation and deliver2.py --no-push are run before
handoff; the dry run's result is the acceptance gate. The independent second reading
is intentionally left to the second worker.

## Second reading by C1

I independently opened the repository node, the sandbox node and Lean module, both
statement-dependency nodes, and the full declarations of `IsCurve` and `IsConnectedCurve`
in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/AlgebraicGeometry/Curve.lean`.
There is no statement correction, new definition node, or dependency module in this delivery.
The existing dependency is usable: `IsConnectedCurve` extends the recorded `IsCurve`, rather
than replacing its meaning with an unrelated curve notion.

Object, hypothesis, and conclusion checklist (H3):

- Ground field `k`: `{k : Type u} [Field k]`. I read `Field` in
  `Mathlib.Algebra.Field.Defs`: it extends `CommRing` and `DivisionRing`, including
  nontriviality and inverses of nonzero elements. Verdict: exact def-weil-field.
- Algebraic closure, implicit in the cited curve definition: `[IsAlgClosed k]`.
  The text of def-sc-curves begins with an algebraically closed field and explicitly
  reiterates this requirement. I read `IsAlgClosed`, which requires every polynomial
  to split. Verdict: required inherited hypothesis, not an added restriction.
- Scheme `C` over this field: `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`.
  Verdict: exactly a scheme with its specified structure morphism; the explicit
  morphism form is necessary for the recorded `IsConnectedCurve f` API and is permitted
  by the scheme-over-field convention in coord/STATE.md.
- Curve, separated and finite type: `[IsConnectedCurve f]` extends `IsCurve f`, which
  extends `IsSeparated f`, `LocallyOfFiniteType f`, and `QuasiCompact f`, with
  `krullDim_le_one : topologicalKrullDim C ≤ 1`. Verdict: separated finite type
  dimension-at-most-one scheme, exactly the dependency's broad curve notion.
- Connected curve: the same class adds `connectedSpace : ConnectedSpace C` and
  `krullDim_eq_one : topologicalKrullDim C = 1`. ConnectedSpace includes nonemptiness.
  Verdict: precisely the nonempty, connected, dimension-one specialization explicitly
  required by def-sc-curves and the item; a merely connected zero-dimensional scheme
  would be the wrong object.
- Smooth over `k`: `[Smooth f]`. I read the Mathlib class: smoothness is checked on
  the induced ring maps for affine opens. Verdict: the structure morphism is smooth,
  without any added properness, rational-point, or relative-dimension assumption.
- Proper over `k`: the left disjunct `IsProper f`. I read Mathlib's class, separated,
  universally closed and locally of finite type. Verdict: exact properness conclusion.
- Affine over `k`: the right disjunct `IsAffine C`. I read Mathlib's class, saying
  that `C.toSpecΓ` is an isomorphism. Verdict: exact affineness as specified in
  def-sc-curves (an affine scheme); the base is affine as well.
- Either conclusion, for every such field, scheme and structure map:
  `IsProper f ∨ IsAffine C`. Verdict: inclusive disjunction with the same quantified
  objects and no extra hypotheses or clauses.

Source reading: local literature has no varieties.tex. I fetched and read the Stacks
varieties.tex source in the sandbox scratchpad, chapter Notation, section Curves,
and `lemma-dim-1-nonproper-affine`, and checked its tag page
[Stacks 0A28](https://stacks.math.columbia.edu/tag/0A28).
The chapter takes `k` to be a ground field; the lemma assumes separated finite type,
dimension at most one, and absence of a proper dimension-one irreducible component,
and concludes affine. No characteristic or algebraic-closure assumption is hidden in
that source. For the item's smooth connected curve, regularity and connectedness give
irreducibility, so the nonproper case has no proper component. The algebraic-closure
restriction comes from the item's expressly cited blueprint curve definition; the Lean
states that item, not the more general Stacks lemma. No node fault was found.

Edge cases: the empty scheme has dimension bottom and fails IsConnectedCurve;
Spec k has dimension zero and also fails it. Both are excluded by the node's
connected-curve definition, not by an accidental extra Lean hypothesis. Disconnected
curves are excluded exactly as requested. All characteristics are admitted. There is
no integer parameter, index family or sheaf/module zero object in this statement.
Both empty and nonempty compactification boundaries occur and give the two branches.
The explicitly bound arbitrary universe `u` matches the existing Scheme and curve API;
no unbound variable or universe occurs. No Noetherian, projective, rational-point,
or geometric-connectedness instance is demanded in the signature.

Independent H4 searches, with different wording from the worker:

- msearch.py LeanFinder: `Every noncomplete nonsingular algebraic curve is affine`:
  eight unrelated elliptic-curve point/nonsingularity hits; no dichotomy statement.
- msearch.py Loogle: `AlgebraicGeometry.IsProper, Or`: zero hits.
- msearch.py grep: `IsConnectedCurve|dim.*nonproper|nonproper.*affine`: zero hits
  in its Mathlib search. This does not claim the source lacks IsConnectedCurve.
- Direct rg over Mathlib, WeilConjectures and repository lean/Sheaf for
  `IsProper.*∨|∨.*IsAffine|proper_or|affine_or`: no relevant dichotomy;
  unrelated proper-action/ideal hits only. Broader `complete.*curve`,
  `curve.*complete`, and proper/affine searches found Curve/Compactification.lean.
  I opened its compactification and `IsConnectedCurve.isAffine_of_ne_top`
  statements: neither is the item's dichotomy (the latter assumes a proper ambient
  curve and a strict open). Their existence supports reuse in the eventual proof,
  not dropping this module as an existing statement.
- Direct rg of `IsProperOrIsAffine|isProper_or_isAffine|lem-sc-proper-or-affine`
  in dag/lean_names_upstream.json, WeilConjectures and repository lean/Sheaf:
  no match. The worker's recorded LeanSearch service failure remains an unavailable
  search, not evidence of absence.

H5–H9: no definitions are introduced and the sole theorem has exactly `sorry` as
its proof. The module/declaration docstrings carry source and blueprint id. The
statement docstring reproduces both proof steps: compactification with finite boundary,
then empty boundary gives an isomorphism and properness; nonempty boundary invokes
lem-sc-affine-open-proper. Imports provide precisely the predicates/classes used,
namespace and file placement follow the example, and all Lean lines are at most
100 characters. The sandbox node's lean.statement is verbatim the signature in the
file through the conclusion, omitting the proof delimiter as required.

Mismatches and changes: none. I preserved the statement, module, node record and
Worker report. This second reading adds only this independent review report.
Validation: scompile.py compiled the candidate on the server in 1.8 seconds with
exit code zero and no warnings. The delivery dry run and push follow this review.
