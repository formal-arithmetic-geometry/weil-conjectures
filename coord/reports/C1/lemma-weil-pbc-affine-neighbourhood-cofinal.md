## Worker report

The module lean/Sheaf/AlgebraicGeometry/AffinePointedNeighbourhoodCofinal.lean states
AlgebraicGeometry.Scheme.affinePointedNeighbourhoods_initial_and_final_op with a sorry proof.
No definitions or additional nodes are needed, and the node's statement is unchanged.

Hypothesis and clause matching:
- The scheme S is `{S : Scheme.{u}}`, with no finiteness, separatedness, or affine hypothesis.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `(s : Spec (.of Ω) ⟶ S)`. Algebraic closedness is precisely that specified by the
  pointed-neighbourhood dependency, and supplies Mathlib's IsSepClosed instance.
- The ambient pointed étale neighbourhood category is `(pointSmallEtale s).fiber.Elements`.
  Its objects are étale schemes over S with a lift of s, and its arrows are S-morphisms
  carrying the chosen lift to the other lift.
- The affine full subcategory is the Mathlib ObjectProperty full subcategory for
  `fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left`.
  The `.left` is the underlying scheme V, not the base scheme S or the morphism V → S.
  `ObjectProperty.ι` is exactly its full-subcategory inclusion.
- “Is initial” is the first conjunct `Functor.Initial (ObjectProperty.ι ...)`.
  Mathlib defines this by connectedness of each CostructuredArrow category; IsConnected
  includes nonemptiness, so both parts of the node's comma criterion are present.
- “Hence cofinal for the opposite-indexed stalk colimit” is the second conjunct
  `Functor.Final (ObjectProperty.ι ...).op`. Finality is the standard cofinality condition
  for colimits. It uses exactly the opposite of the same inclusion, so applies to the
  stalk diagram over the opposite neighbourhood category, without adding a separate
  stalk object, coefficient category, or existence hypothesis for colimits.

Dependencies read and used:
- def-weil-pbc-scheme-conventions has a convention-only lean record (module and
  declaration null); it defines no additional notion. Its affine-scheme clause is
  Mathlib.AlgebraicGeometry.AffineScheme, AlgebraicGeometry.IsAffine, whose full class
  signature and Scheme.isoSpec were read: affine means the canonical map to Spec Γ is
  an isomorphism, equivalently isomorphic to a spectrum as required by the node.
- def-weil-pbc-pointed-etale-neighbourhoods is a Mathlib leaf with no lean record.
  Its recorded match is CategoryTheory.Functor.Elements, with categoryOfElements,
  applied to AlgebraicGeometry.Scheme.pointSmallEtale s's fiber. Read full definitions
  and docstrings in Mathlib.CategoryTheory.Elements and
  Mathlib.AlgebraicGeometry.Sites.EtalePoint; use this exact specialization inline.
  Read Scheme.Etale and Etale.forget in Mathlib.AlgebraicGeometry.Morphisms.Etale.
- Mathlib.CategoryTheory.ObjectProperty.FullSubcategory supplies ObjectProperty.ι;
  Mathlib.CategoryTheory.Limits.Final supplies Functor.Initial and Functor.Final.
  These imports are transitively/directly available from the two imports of the module.

Proof docstring records all three node steps: affine shrink gives comma nonemptiness;
cofiltered refinement, equalization, and affine shrink give a connecting zigzag;
opposites give finality and the colimit comparison. It names the original proof nodes.

Edge cases checked mathematically: no geometric point exists on an empty base scheme,
so no extra nonempty assumption is needed. An empty étale scheme cannot carry the
chosen Spec Ω lift. Nonaffine bases and non-quasi-compact neighbourhoods are allowed,
because only an affine open around the lift is needed. For S = Spec Ω with Ω
algebraically closed, the identity is itself an affine pointed neighbourhood. No
characteristic restriction is imposed. Both S and Ω use the same arbitrary universe u,
as in Mathlib's pointSmallEtale, and the full category includes all neighbourhoods
in that universe, not a bounded-size selection.

Searches (2026-10-11):
- msearch.py leanfinder, “The inclusion of affine pointed etale neighborhoods of a
  geometric point is initial”: eight hits (Scheme.Etale, its category and forgetful
  functor, stalk/étale definitions); none state this theorem.
- msearch.py loogle, “CategoryTheory.Functor.Initial, CategoryTheory.FullSubcategory”:
  zero hits, unknown identifier CategoryTheory.FullSubcategory. Source inspection
  located the actual ObjectProperty.FullSubcategory API.
- msearch.py grep, “affine.*[Nn]eigh|[Nn]eigh.*affine|pointSmallEtale|fullSubcategoryInclusion”
  in AlgebraicGeometry: twelve hits, chiefly pointSmallEtale and ordinary affine
  neighbourhood statements; no affine pointed-neighbourhood initiality theorem.
- msearch.py leansearch, “affine pointed etale neighbourhood inclusion initial functor”:
  unavailable, Internal Server Error; no verdict assigned to this unavailable search.
- rg over WeilConjectures and lean/Sheaf for affine/neighbourhood/initial combinations:
  affine-chart and shrinking results, no exact declaration. rg for the item's exact
  blueprint id in WeilConjectures returned no hit. rg for the proposed theorem name
  in dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf returned no hit.

The local literature paths in the source record are absent on this machine. Read the
source proof at https://stacks.math.columbia.edu/tag/04HX (affine neighbourhoods form
 a cofinal system), and https://stacks.math.columbia.edu/tag/0BUC (the full-subcategory
cofinality criterion, used dually). The blueprint text and proof are also preserved
in full in the node. No statement fault or dispute found.

Validation: scompile.py C1 lemma-weil-pbc-affine-neighbourhood-cofinal compiled the
53-line module on the server in 1.7 seconds with exit code 0 and no warnings.

## Second reading by C1

I opened the node and the complete Lean declaration independently.  The node's
objects and clauses match as follows:

- The base scheme is the implicit `{S : Scheme.{u}}`; the geometric point is the
  explicit `s : Spec (.of Ω) ⟶ S`, with `{Ω : Type u}`, `[Field Ω]`, and
  `[IsAlgClosed Ω]`.  These are exactly the point data supplied by the recorded
  pointed-neighbourhood convention; no Noetherian, separated, finite type,
  characteristic, or affine hypothesis is added.
- The ambient category `𝓝_s` is rendered by
  `(pointSmallEtale s).fiber.Elements`.  Its objects are the fibre elements
  (pointed étale neighbourhoods), with the Mathlib category-of-elements
  morphisms.  The affine predicate is exactly
  `fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left`, where
  `n.1.left` is the underlying neighbourhood scheme.
- The full affine subcategory is rendered by
  `ObjectProperty.ι (...)`; it is genuinely full by Mathlib's
  `ObjectProperty.FullSubcategory` construction.  The first conclusion clause
  is exactly `Functor.Initial` of this inclusion.
- The second clause is exactly
  `Functor.Final (ObjectProperty.ι (...)).op`, the opposite inclusion's
  finality and hence the cofinality needed for an opposite-indexed stalk
  colimit.  No colimit object, coefficient category, or extra existence
  hypothesis is silently introduced.

The quantifier order and universes are unchanged: `S` and `Ω` share `u`, and
the theorem covers arbitrary `u`, including the empty scheme (which simply has
no such `s`), the zero/empty neighbourhood cases (none can contain the chosen
geometric point), `n = 0` (there is no numerical parameter), and every
characteristic.  For `S = Spec Ω` with Ω algebraically closed, the identity
neighbourhood is included and affine, as expected.  The source places were
checked against Stacks Tags 04HX (affine étale neighbourhoods cofinal in the
stalk description) and 0BUC (the full filtered-subcategory cofinality
criterion); the Lean statement expresses their initial/opposite-final form.

I searched Mathlib and `WeilConjectures/` with `rg` for the theorem name and
for combinations of `pointSmallEtale`, affine neighbourhood, and initial/final,
and reran the available `msearch.py` LeanFinder/Loogle/grep queries.  Only the
underlying point, étale, elements, and ObjectProperty APIs were found; no
existing theorem states this result.  The unavailable LeanSearch endpoint was
recorded in the worker report.  The dependency declarations and their source
signatures were opened; no dependency module is unusable and no second
definition is present.

No mismatch was found, so no Lean or node statement change was required.  The
module was recompiled with `scompile.py` and passed with only the permitted
`sorry` proof warning (in fact no warning was emitted).
