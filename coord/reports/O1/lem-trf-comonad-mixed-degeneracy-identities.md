## Worker report

The module `Sheaf.CategoryTheory.ComonadMixedDegeneracyIdentities` states
`CategoryTheory.NaturalTransport.comonad_mixed_degeneracy_identities` with a single
`sorry` proof. Its two helper definitions, `comonadFace` and `comonadDegeneracy`,
construct exactly the displayed transformations by recursive whiskering. They
introduce no independent mathematical notion, no arbitrary transformations and no
simplicial object. Both helpers are listed in `lean.declarations` and have source
and blueprint docstrings. All definition data are explicit and contain no sorry.

Read the item's complete statement, its six proof steps, its statement dependency
and the latter's recorded declaration and docstring. Checked the source at Stacks
`simplicial.tex`, Example 0G5M and Lemma 0G5N, specifically the verification of
(1)(b)--(e), against the statement and all four conclusion families.
The node is unchanged except for its new `lean` record. No correction, disputed
statement, new node or dependency module is needed.

Hypotheses and objects:

- Ordinary category: `{C : Type u} [Category.{v} C]`, with independent explicitly
  declared object and morphism universes. There are no size restrictions.
- Endofunctor: `(T : C ⥤ C)`.
- Powers: the recorded `NaturalTransport.power T`, whose definition is zero equal
  to `𝟭 C` and successor `power T n ⋙ T`, exactly `T ∘ T^n` in mathematical order.
  Thus `B_n` is `power T (n + 1)`; no second definition of powers is introduced.
- Counit and comultiplication: `(e : T ⟶ 𝟭 C)` and `(c : T ⟶ T ⋙ T)`. The latter
  is the same second power, definitionally; no comonad or simplicial structure
  is assumed in place of these raw data.
- `(1_1 ⋆ e) ∘ c = 1_1`: `h₁`, using `Functor.whiskerRight e T`, whose component
  is `T.map (e.app x)`.
- `(e ⋆ 1_1) ∘ c = 1_1`: `h₂`, using `Functor.whiskerLeft T e`, whose component
  is `e.app (T.obj x)`. These are the node's two counit equalities in reverse
  listing order. The unitors have identity components and only identify the
  identity-functor composites with `T`.
- Coassociativity: `h₃`. Its left component is `c_x ≫ T(c_x)` and its right
  component is `c_x ≫ c_(T x)`. It is the node's equality in the symmetric
  orientation; the associator has identity components and only records
  parenthesization.

Prescribed maps and naturality:

- `comonadFace T e n i : power T (n + 1) ⟶ power T n` is the node's `d_i^n`.
  At index zero the definition is `whiskerLeft (power T n) e`, applying `e` to
  the outermost factor. At a successor index it is the preceding face
  whiskered on the outside by `T`. Consequently its components are exactly
  `T^i(e_(T^(n-i) x))`. Its degree-zero extension is `e`; the theorem uses
  faces only in the positive degrees specified in the node.
- `comonadDegeneracy T c n i` has source `power T (n + 1)` and target
  `power T (n + 2)` and is the node's `s_i^n`. The same recursion gives
  components `T^i(c_(T^(n-i) x))`, including the degree-zero map `c`.
- The maps are constructed as natural transformations, using Mathlib whiskering.
  Thus their asserted naturality is part of the definitions' types, and requires
  no extra assumed equations or postponed naturality proof.

Every conclusion and its full index range (write `N` for the node's degree):

- First conjunct: `N = n + 2`, node indices `i_old = i.val` and
  `j_old = j.val + 1`. `i : Fin (n + 2)`, `j : Fin (n + 1)` and
  `i ≤ j.castSucc` are exactly `0 ≤ i_old < j_old ≤ N-1`.
  `comonadDegeneracy ... (n+1) j.succ ≫ comonadFace ... (n+2) i.castSucc`
  is `d_i^N ∘ s_j^(N-1)`; the right side is
  `s_(j-1)^(N-2) ∘ d_i^(N-1)`. Conversely, the node inequality gives
  `j_old ≥ 1`, so every allowed pair occurs in this reindexing.
- Second conjunct: `N = n + 2`, `i_old = i.val + 1`, `j_old = j.val`.
  The same Fin types and `j.castSucc < i` are exactly
  `0 ≤ j_old < i_old-1 ≤ N-1`. The left side uses the degree `n+1`
  degeneracy at `j.castSucc` and the degree `n+2` face at `i.succ`;
  the right side uses the degree `n+1` face at `i` and degree `n`
  degeneracy at `j`. This is precisely the node's second mixed equation.
  Every original allowed pair has `j_old ≤ N-2`, hence fits these Fin types.
- Third conjunct: `N = n + 1`, `j : Fin (n + 1)`, exactly `0 ≤ j ≤ N-1`.
  The two equalities are `s_j^(N-1) ≫ d_j^N = 𝟙 (power T N)` and
  `s_j^(N-1) ≫ d_(j+1)^N = 𝟙 (power T N)`. This is the node's equality
  chain, with its identity on `B_(N-1)` and both equalities retained.
- Fourth conjunct: `N = n + 1`, `i j : Fin (n + 1)` and `i ≤ j`,
  exactly `0 ≤ i ≤ j ≤ N-1`. Its left side is `s_j^(N-1) ≫ s_i^N`;
  the right side is `s_i^(N-1) ≫ s_(j+1)^N`.
- All quantifiers have explicit binders. Natural-number offsets cover every
  original positive degree or degree at least two, without truncated subtraction.
  Composition `≫` means first-then, so the displayed orders translate exactly
  to the node's mathematical right-to-left composition.

Dependencies used:

- Statement dependency `def-trf-endofunctor-powers`:
  `Sheaf.CategoryTheory.NaturalTransportInduction`, declaration
  `CategoryTheory.NaturalTransport.power`. Read its full recursive definition
  and source docstring. Imported publicly and reused directly throughout.
- Proof dependency `lem-amb-natural-transformation-whisker-exchange`: the node's
  Mathlib match is `CategoryTheory.Functor.whiskerLeft_comp_whiskerRight`,
  `Mathlib.CategoryTheory.Whiskering`, lines 203--207. Read its full signature
  and the surrounding whiskering definitions. This module is already a public
  import of `NaturalTransportInduction`, so no redundant direct import is added.
- Mathlib `Functor.whiskerLeft`, `Functor.whiskerRight`, `Functor.leftUnitor`,
  `Functor.rightUnitor`, and `Functor.associator` define the actual transformations
  and harmless parenthesization identifications. Read their component formulas.

Edge cases checked before writing and again against the final file:

- Original `N = 1`: there are both counit cancellations at `j = 0` and the
  degeneracy equation at `i = j = 0`. These unfold to the two counit hypotheses
  and coassociativity. None is lost by the shifted degrees.
- Original `N = 2`: the first mixed pair `(i,j)=(0,1)` is Lean `n=0,i=0,j=0`;
  the second mixed pair `(i,j)=(2,0)` is Lean `n=0,i=1,j=0`.
- Outermost and innermost positions, adjacent positions and zero intervening
  powers are handled by `Fin.cases`, including `power T 0 = 𝟭 C`.
- Equal degeneracy indices are included by `≤`, not just strict inequality.
- The identity endofunctor is allowed. The empty category is allowed. No
  nonemptiness, limits, additive structure or simplicial data is imposed.

Searches (2026-10-24):

- `msearch.py leanfinder`, query "Whiskered counit and comultiplication on powers
  of an endofunctor satisfy the mixed face degeneracy and double degeneracy
  identities": eight hits, consisting of `Comonad.right_counit` and
  cosimplicial relations. None states these identities for the raw transformations.
- `msearch.py loogle`, query
  `CategoryTheory.Comonad, CategoryTheory.SimplicialObject.σ_comp_σ`:
  zero hits.
- `msearch.py grep`, query `comonad|Comonad|degeneracy` in
  `CategoryTheory/Monad`: 25 hits on adjunctions, Kleisli categories and
  comonadicity. Read `Mathlib.CategoryTheory.Monad.Basic`'s full comonad
  signature: it supplies the degree-one axioms, not these indexed identities.
- `msearch.py leansearch`, query "The raw whiskered counit and comultiplication
  of a comonad satisfy the mixed and double degeneracy identities on powers of
  the endofunctor": eight hits on comonad data, bicategorical counit or
  coassociativity axioms, and comonoid axioms; none states the item.
- `rg` in Mathlib category theory and simplicial-object sources, in
  `lean/WeilConjectures`, in `lean/Sheaf`, and in `dag/lean_names_upstream.json`
  for `comonad`, `Comonad`, the three proposed declaration names, and mixed
  degeneracy phrases: no existing raw operator definitions or exact theorem.
  Also searched the item id in `lean/WeilConjectures`: no hit.
  Read `Sheaf.CategoryTheory.ComonadSimplicialObject` and
  `Sheaf.CategoryTheory.ComonadStandardResolution`: these characterize a whole
  simplicial object, rather than define standalone raw face/degeneracy maps or
  prove their equations. Read Mathlib's simplicial operators and relations:
  these require an already given simplicial object and cannot substitute here.
- Searched the trace-formula DAG for mixed/degeneracy identities: the
  simplicial-object identities node assumes an existing simplicial object;
  the comonad face-identities sibling is complementary and currently has no
  standalone recorded map declaration. No duplicated node is added.

Validation: compiled the module through the prescribed `scompile.py` on the
server against the live library. Both sandbox and library-module checks passed
without errors or non-sorry warnings (0.7 s and 0.8 s respectively). The only
postponed proof is the named theorem above, whose docstring contains all six
natural-language proof steps from the node. Definitions have no postponed data.

## Second reading by O1

Independent second reading by the maintainer review service (cc reviewer, 2026-10-24),
replacing the earlier author self-check section. Read against the node, Stacks
`simplicial.tex` Example 0G5M and Lemma 0G5N (proof of (1)(b)--(e)), and the recorded
`def-trf-endofunctor-powers` declaration `NaturalTransport.power`
(`| 0 => 𝟭 C | n + 1 => power T n ⋙ T`, so `(power T (n+1)).obj x = T (T^n x)`).

Objects:
- C, T: `{C : Type u} [Category.{v} C] (T : C ⥤ C)`, no extra instances. OK.
- e, c: `(e : T ⟶ 𝟭 C) (c : T ⟶ T ⋙ T)`, raw data, no comonad structure. OK.
- `d_i^n = 1_i ⋆ e ⋆ 1_{n-i}` (component `T^i(e_{T^{n-i}x})`): `comonadFace T e n i`.
  Index 0 at degree n+1 is `whiskerLeft (power T (n+1)) e` (component `e_{T^{n+1}x}`),
  successor index is `whiskerRight (face n j) T` (component `T(face_x)`). By induction the
  component is `T^i(e_{T^{n-i}x})`. Matches the node and the convention of the sibling
  `lem-trf-comonad-simplicial-object` (`whiskerLeft (power (n+1-i)) (whiskerRight e (power i))`).
  The degree-0 value `e` is only a recursion base; the theorem uses faces in degree ≥ 1. OK.
- `s_i^n = 1_i ⋆ c ⋆ 1_{n-i}`: `comonadDegeneracy T c n i`, same recursion, real data. OK.
- Naturality: by construction (whiskering of natural transformations). OK.

Hypotheses (Stacks: `1_Y = (d⋆1_Y)∘s = (1_Y⋆d)∘s`, `(s⋆1)∘s = (1⋆s)∘s`):
- `(1_1⋆e)∘c = 1_1` (component `T(e_x)∘c_x`): `h₁` with `whiskerRight e T`. OK.
- `(e⋆1_1)∘c = 1_1` (component `e_{Tx}∘c_x`): `h₂` with `whiskerLeft T e`. OK.
- coassociativity: `h₃`, `T(c_x)∘c_x = c_{Tx}∘c_x`; unitors/associator have identity
  components. OK, not stronger.

Conclusions (node degree N):
- (b) N ≥ 2, 0 ≤ i < j ≤ N-1: Lean N = n+2, j_old = j+1, `i ≤ j.castSucc` ⟺ i < j_old,
  `i : Fin (n+2)` ⟺ i ≤ N-1; `s_{j+1}^{N-1} ≫ d_i^N = d_i^{N-1} ≫ s_j^{N-2}`. Bijective
  reindexing, all pairs covered. OK.
- (second mixed) N ≥ 2, 0 ≤ j < i-1 ≤ N-1: i_old = i+1, `j.castSucc < i`,
  `s_j^{N-1} ≫ d_{i+1}^N = d_i^{N-1} ≫ s_j^{N-2}`; j ≤ N-2 forced, so `Fin (n+1)` loses nothing. OK.
- (c)/(d) N ≥ 1, 0 ≤ j ≤ N-1: `s_j ≫ d_j = 𝟙 (power T N) = s_j ≫ d_{j+1}`, both kept. OK.
- (e) N ≥ 1, 0 ≤ i ≤ j ≤ N-1: `s_j^{N-1} ≫ s_i^N = s_i^{N-1} ≫ s_{j+1}^N`. OK.
- `≫` order = node's right-to-left composition, checked on every clause.

Edge cases: N = 1 (both cancellations, i = j = 0 degeneracy), N = 2 for the mixed
identities, the outermost/innermost positions, `power T 0 = 𝟭 C`, empty category,
T = 𝟭: all covered; no truncated subtraction.

One definition per notion: the face/degeneracy maps are not defined elsewhere in the
live tree (grep `comonadFace|comonadDegeneracy` in lean/Sheaf and dag/nodes: none);
`lem-trf-comonad-simplicial-object` asserts an existential simplicial object, sibling
`lem-trf-comonad-face-identities` has no lean record yet. Mathlib `Comonad` gives only
the degree-one axioms. Powers reuse `NaturalTransport.power`. OK.

Records: `lean.statement` equals the file signature up to whitespace; `declarations`
lists both helpers and the theorem; helpers have source and blueprint docstrings; the
theorem docstring carries the six proof steps; only `sorry` is the theorem proof.

Finding: the previous "Second reading" section was a self-check by the author (H11);
replaced by this reading. No Lean or record change.
