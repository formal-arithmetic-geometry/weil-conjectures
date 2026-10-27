## Worker report

Item: lem-sfb-scheme-unramified-etale-locality. The module
`Sheaf.AlgebraicGeometry.SchemeUnramifiedEtaleLocality` states
`AlgebraicGeometry.scheme_unramified_etale_locality`, with its whole proof `sorry`.
There are no new definitions or helper theorems. The accepted stage-1 split, statement,
statement dependencies, and proof are preserved; only the item's `lean` record is added.

The inherited BLOCKED ending concerns reopening the reviewed stage-1 split. The stage
handoff in coord/brief-stage2.md §0 explicitly permits stating that split at stage 2.
The current node is split, has no Lean record, and is in the stage-2 queue. There is no
repair note for this item. This delivery proceeds through deliver2.py.

Clause-by-clause rendering:

- All schemes and morphisms use `Scheme.{u}` and `⟶`, for the explicitly declared,
  arbitrary universe `u`. The property P is exactly the dependency's `IsUnramified`,
  not formal unramifiedness alone. The theorem universally quantifies the schemes
  and maps separately in each clause, so no object is fixed or excluded.
- Clause (i) is the first conjunct: for `e : U ⟶ X` and `f : X ⟶ Y`,
  `Etale e → IsUnramified f → IsUnramified (e ≫ f)`.
  Lean's composition `e ≫ f` is the node's f composed with e.
- Clause (ii) is the second conjunct: for `f : X ⟶ Y` and `b : V ⟶ Y`,
  `IsUnramified f → Etale b → IsUnramified (pullback.snd f b)`.
  This is the projection `X ×_Y V → V`, not the projection to X. No cartesian
  square is assumed as extra data: it is the chosen scheme fibre product.
- Clause (iii) is the final conjunct, universally quantified over `X`, `Y`, and `f`.
  `IsUnramified f ↔ ∀ x : X, ...` gives both directions with exactly the node's scope.
  The existential binders introduce schemes `U V`, maps `a : U ⟶ X`, `b : V ⟶ Y`,
  the point `u : U`, and `h : U ⟶ V`. Their conjunction says exactly `Etale a`,
  `Etale b`, `a.base u = x`, `a ≫ f = h ≫ b`, and `IsUnramified h`.
  Neither chart map is required to be surjective, and the square is not assumed cartesian.
- No quasi-compactness, separation, or Noetherian assumption is present anywhere.
  There is no Nonempty hypothesis or implicit unbound variable. `autoImplicit` is false.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`. The full structures and their docstrings identify
  locally ringed spaces with local affine charts, and morphisms of locally ringed spaces.
- def-weil-unramified-morphism: `AlgebraicGeometry.IsUnramified` in
  `Sheaf.AlgebraicGeometry.UnramifiedMorphism`. Its full body is
  `LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`, exactly the node's notion.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. Its affine-local ring-map definition and
  `Etale.iff_flat_and_formallyUnramified` express the recorded étale notion.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `pullback.fst`, and
  `pullback.snd` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  The signatures and docstrings give the chosen universal fibre product and projections;
  scheme pullbacks are available through the geometric imports.

The statement dependencies are public imports. Proof-only imports include the recorded
`scheme_etale_source_target_properties`, `unramified_baseChange_restrict_open` (the upstream
WeilConjectures module), `smooth_and_fibre_dimension_zero_of_etale`, and the Mathlib modules
carrying the formal-unramified stalk, differential, flat-local, tensor, and smooth-stalk
leaves. The composition-cancellation node has no Lean module yet, so no such import is
invented. The module docstring reproduces all six accepted proof steps and their inputs.

Sources opened: Stacks descent.tex, `definition-local-source-target` (04QZ),
`lemma-unramified-etale-local-source` (03YV), and `remark-list-local-source-target` (04R3),
including item (9). Definition 04QZ has exactly the three conjuncts written here.

Edge cases checked before writing:

- If X is empty, the pointwise condition in (iii) is vacuous. The node's local finite
  type and all-stalk criteria also include empty sources, so this is intended.
- For identity charts, U = X, V = Y, a and b identities, h = f, u = x satisfy the
  forward implication, without any nonemptiness or global cover condition.
- Empty U is permitted in (i); empty V is permitted in (ii), giving an empty pullback.
- A nonreduced source such as Spec(k[ε]/ε²) over Spec(k) is not incorrectly declared
  unramified: the pointwise condition still requires an unramified h in actual étale
  charts. Inseparable field extensions likewise are not excluded or made unramified.
- Arbitrarily large schemes are covered by the arbitrary universe `u`. All chart
  schemes are in the same scheme category as X and Y, as in the source convention.

Searches made with msearch.py for this group/item, and direct source searches:

- LeanFinder: "Unramified morphisms of schemes are etale local on source and target in
  compatible pointwise etale charts". Eight hits: étale implies formal unramifiedness,
  `IsEtale`, the postcomposition instance, `FormallyUnramified`, `IsEtale.of_comp`,
  `Scheme.Etale`, `formallyUnramified_iff`, and étale implies smooth. None states the
  three-clause source-and-target theorem. Search-service historical names were checked
  against the current source, where the class is `Etale`.
- Loogle: "AlgebraicGeometry.IsUnramified, AlgebraicGeometry.Etale". Zero hits,
  unknown identifier `AlgebraicGeometry.IsUnramified` in the search index; the notion
  is supplied by the project's recorded definition, read directly above.
- Mathlib grep: `unramified.*(etale|local)|etale.*unramified` in
  AlgebraicGeometry/Morphisms. Ten hits in FormallyUnramified.lean and Etale.lean:
  local ring-map properties, open diagonal, étale implies formally unramified, and
  cancellation/flatness criteria. None is this statement.
- LeanSearch: "Unramified morphisms of schemes are etale local on source and target".
  Eight hits: `Scheme.Etale`, `IsEtale`, `RingHom.FormallyUnramified.propertyIsLocal`,
  `FormallyUnramified.recOn`, `FormallyUnramified`, `IsLocalAtTarget`, `affineLocally`,
  and `IsLocalAtSource`. None is the required theorem.
- rg of lean/WeilConjectures and lean/Sheaf for
  `unramified.*[Ee]tale|[Ee]tale.*[Uu]nramified|unramified_etale|etaleLocalSourceTarget|etale_local_source_target`,
  followed by focused `IsUnramified|scheme_unramified_etale_locality|unramified.*local`
  searches in their AlgebraicGeometry trees and dag/lean_names_upstream.json.
  Existing results concern étale local decomposition, finite unramified maps,
  fibre/neighbourhood criteria, or the five other scheme properties. No exact match.
- grep -rn for the item id in lean/WeilConjectures: no match.

No statement correction, missing notion, dependency repair, or STATEMENT-DISPUTED flag
is needed. The only node delta is the Lean record, with its signature copied verbatim.

Validation: scompile.py compiled the sandbox and library forms separately on the live
server, in 5.9 s and 2.4 s, with no errors or non-sorry warnings. Delivery preflight and
its per-file compile are run through deliver2.py before pushing.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
