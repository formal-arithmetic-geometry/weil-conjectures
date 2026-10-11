## Worker report

The module `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily` states
`AlgebraicGeometry.Etale.isIso_iff_of_jointlySurjective_etale_family`, with proof `sorry`.
It introduces no definition and changes only the item's `lean` record.

Hypothesis and clause matching:

- The scheme T is `{T : Scheme.{u}}`.
- The arbitrary index set is `{I : Type w}`, with its universe independent of u.
- The schemes T_i and morphisms t_i are `{U : I → Scheme.{u}}` and
  `(t : ∀ i : I, U i ⟶ T)`.
- Each morphism is étale: `[∀ i : I, Etale (t i)]`.
- Joint surjectivity on underlying points is exactly
  `(ht : ∀ x : T, ∃ (i : I) (y : U i), (t i).base y = x)`.
- G and H are abelian sheaves on the small étale site:
  `{G H : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}`.
- Their morphism is `(φ : G ⟶ H)`.
- The global isomorphism condition is `IsIso φ`.
- “If and only if” is `↔`; “for every i” is `∀ i : I`.
- The actual inverse-image morphism is `(upperStar AddCommGrpCat.{u + 1} (t i)).map φ`,
  with `IsIso` taken in the sheaf category on `(U i).smallEtaleTopology`.
- The empty-family parenthetical is included by the unrestricted I binder: when I is
  empty, ht implies that T has no points, the right side is true vacuously, and the
  equivalence asserts every φ is invertible. It needs no separate hypothesis or theorem.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, including their signatures and docstrings.
- `def-weil-etale-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  `AlgebraicGeometry.Etale` (affine-local étale condition).
- `def-weil-pbc-abelian-etale-sheaves`: Mathlib.CategoryTheory.Sites.Sheaf,
  `CategoryTheory.Sheaf`; Mathlib.AlgebraicGeometry.Sites.Etale,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`. This is precisely the specialization
  indicated by the dependency's recorded `lean.note`.
- `def-weil-pbc-inverse-image`:
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs,
  `AlgebraicGeometry.Etale.upperStar`. Read its complete signature, section variables,
  definition and docstring: left Kan extension followed by sheafification, left adjoint
  to `Etale.lowerStar`. The coefficient category is AddCommGrpCat.{u + 1}, as in landed
  citers and upstream's Grothendieck abelian convention. All dependency modules are
  transitively imported through the one direct import.

Edge cases checked before writing: empty I (forces empty T); empty T with any I
(all schemes mapping to it must be empty); individual empty U_i; infinite families;
repeated members; zero sheaves; arbitrary characteristic; schemes with no Noetherian,
separatedness, finiteness or base-field assumption. No case needs an extra hypothesis.
All universes and variables are bound explicitly.

Searches for an existing statement (logged by msearch.py in searches.jsonl):

- LeanFinder: “A morphism of abelian sheaves on the small etale site is an isomorphism if
  and only if its inverse image under every map in a jointly surjective etale family is
  an isomorphism”. Eight hits; the closest are general-site local bijectivity and
  cover-dense restriction results, none states this inverse-image criterion.
- Loogle: `CategoryTheory.Sheaf.isIso_iff_of_coversTop`. One hit, read in full in
  Mathlib.CategoryTheory.Sites.LocalProperties. It uses `K.overPullback` on localized
  sites and `K.CoversTop`, so does not directly state this node with `Etale.upperStar`
  and joint surjectivity of scheme morphisms. A site-comparison theorem is required.
- LeanSearch: “isomorphism of etale sheaves detected by pullback along a jointly
  surjective etale covering”. Service unavailable (Internal Server Error), recorded.
- Mathlib grep: `isIso_iff_of_coversTop|isIso.*upperStar|upperStar.*isIso`.
  Only two LocalProperties hits, for the preceding general-site lemma.
- Source repository and lean/Sheaf rg:
  `isIso.*upperStar|upperStar.*isIso|etale-cover-detects-iso|isIso_iff_of_coversTop`.
  Found `Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective` in
  WeilConjectures.SixFunctors.OpenClosed.Conservative. Read its signature and docstring.
  It is only the converse implication, for a general coefficient category and arbitrary
  scheme morphisms, and has `{ι : Type u}`. It does not state this node's full equivalence,
  étale hypothesis, or independent index universe. It is a useful proof tool, not an
  identical statement to record as existing.
- Exact item-id search in WeilConjectures finds no declaration for the node.
- Name collision search for `isIso_iff_of_jointlySurjective_etale_family` in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found none.

Source verification: the local Stacks checkout is absent on this machine, so opened
https://stacks.math.columbia.edu/tag/0EZR (proof of (1)),
https://stacks.math.columbia.edu/tag/03PU and
https://stacks.math.columbia.edu/tag/03Q1 (3) directly. These give covering detection,
geometric-stalk conservativity and the natural stalk identification, respectively.
The docstring carries all four proof steps and their DAG dependencies for stage 3.
No statement correction, missing notion, unusable dependency or disputed statement was found.

Validation: added the used import `Mathlib.Algebra.Category.Grp.AB` supplying the Abelian
and IsGrothendieckAbelian instances required by `upperStar` for AddCommGrpCat. Server
single-file compile passed cleanly (1.7 s). The only proof is the named theorem's `sorry`.

## Second reading by C1

The node introduces the following data and clauses, matched against the Lean signature:

- A scheme $T$ is `{T : Scheme.{u}}`.
- An arbitrary index type $I$ is `{I : Type w}`; its universe is independent of that of
  $T$.
- Schemes $T_i$ and maps $t_i:T_i\to T$ are `{U : I → Scheme.{u}}` and
  `(t : ∀ i : I, U i ⟶ T)`.
- Étaleness is the instance binder `[∀ i : I, Etale (t i)]`.
- Joint surjectivity is exactly `ht : ∀ x : T, ∃ (i : I) (y : U i),
  (t i).base y = x`.
- Abelian sheaves $G,H$ on the small étale site are
  `{G H : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}`, and their morphism is
  `(φ : G ⟶ H)`.
- The conclusion is the ordered equivalence `IsIso φ ↔ ∀ i : I, IsIso
  ((upperStar AddCommGrpCat.{u + 1} (t i)).map φ)`, rendering exactly the isomorphism
  criterion for every inverse image in the node.

Each introduced object, hypothesis, and conclusion clause agrees with the node and its
dependency declarations. No extra finiteness, separation, Noetherian, characteristic,
or field assumptions occur. The empty family is admitted; `ht` then forces $T$ to have
no points and the universal right side is vacuous. Empty schemes and members, repeated
members, infinite families, zero sheaves, $n=0$ (not present), and arbitrary
characteristic are all covered by the unrestricted binders. Universes are explicit and
no variable is left implicit by the module options.

I rechecked the Mathlib and project searches recorded above, including the general
`CategoryTheory.Sheaf.isIso_iff_of_coversTop` result and the existing converse lemma.
Neither states this étale-family equivalence with `upperStar`; the recorded declaration
is therefore new. The dependency declarations are the exact notions used by the node;
no missing or unusable dependency and no statement correction was found. The only repair
from the worker delivery was procedural: this independent reading and its report section
were added. The module compiles cleanly with only the intentional theorem `sorry`.
