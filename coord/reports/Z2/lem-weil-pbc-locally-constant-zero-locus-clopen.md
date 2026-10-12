## Worker report

Item `lem-weil-pbc-locally-constant-zero-locus-clopen`, module
`Sheaf.Topology.LocallyConstantZeroLocusClopen`, theorem
`TopCat.Sheaf.isClopen_setOf_germ_eq_zero_of_locallyConstant` (proof `sorry`).

Why the node had no declaration: it left the queue on 2026-10-10 as unreachable from the target
(lead note of that day), so stage 2 never listed it; it is reached again and was newly open.

Rendering, clause by clause:

- `T` a topological space, sheaves on the site of its opens: `T : TopCat.{u}`,
  `F : TopCat.Sheaf AddCommGrpCat.{u} T` (a sheaf for `Opens.grothendieckTopology T`,
  def-weil-pbc-sites-and-cohomology).
- `F` locally constant: `hF : ∀ x, ∃ U : Opens T, x ∈ U ∧ ∃ A : AddCommGrpCat.{u},
  Nonempty (abelianOpenRestriction U F ≅ (constantSheaf (Opens.grothendieckTopology
  ((Opens.toTopCat T).obj U)) AddCommGrpCat.{u}).obj A)`. `F|_U` is the landed
  `TopCat.Sheaf.abelianOpenRestriction` (`W ↦ F(W)` on the opens of `U`, module
  `Sheaf.Topology.AbelianOpenExtensionByZero`); the constant sheaf is Mathlib's
  `CategoryTheory.constantSheaf` (def-weil-pbc-constant-sheaf). `A` depends on the point.
- `s ∈ Γ(T, F)`: `s : F.obj.obj (op ⊤)`.
- `Z(s) = {x | s_x = 0}`: `{x : T | F.presheaf.germ ⊤ x (Set.mem_univ x) s = 0}`, the germ in
  Mathlib's stalk `TopCat.Presheaf.stalk` (the `mathlib_match` of def-weil-pbc-module-stalk for a
  sheaf of abelian groups).
- Open and closed: `IsClopen`.

Edge cases: empty `T` (both hypothesis and conclusion trivial); `F = 0`; `A` in the universe of
`F` is no restriction, since on a neighbourhood of `x` the group `A` is isomorphic to the stalk
`F_x`. The docstring carries the four proof steps of the node.

Searches for an existing statement: grep of `lean/WeilConjectures` and `lean/Sheaf` for
`IsClopen`, `locally constant`, `germ.*= 0` (upstream
`WeilConjectures/Topology/Sheaves/SpectralRestriction.lean`, the module of the citer
lemma-weil-pbc-spectral-restriction, has no such statement); the node's own recorded searches
(LeanSearch, Loogle, LeanFinder, grep of Mathlib: `IsLocallyConstant.isClopen_fiber` is the
statement for functions only). No existing declaration.

Compile time on the server (with `.olean` output): see the landing; 1.3 s locally.

## Second reading by Z2

Independent reader Z2-zlc (a fresh `codex exec` session that did not write the module):

VERDICT: PASS

1. Objects match: `T : TopCat.{u}` is the space, `F` is an abelian sheaf on its open-cover site, and `s : F.obj.obj (op ⊤)` is a global section.
2. `hF` states exactly local constancy: each point has an open neighbourhood and an isomorphism to a constant sheaf; `A` may vary with the neighbourhood. No hypothesis is added, dropped, or hollow.
3. `abelianOpenRestriction U F` evaluates on the image of each open of `U`, with F’s restriction maps, so it is the node’s `F|_U`. Mathlib’s `constantSheaf … .obj A` is precisely sheafification of the constant presheaf.
4. `F.presheaf.germ ⊤ x _ s` is the colimit germ in `F_x`, matching the dependency’s stalk construction. `IsClopen` asserts exactly openness and closedness of its zero locus.
5. Universes cause no substantive restriction: on a neighbourhood containing `x`, any constant coefficient group is isomorphic to the `u`-small stalk `F_x`. Arbitrary space/value sizes can be accommodated in a common larger universe. Empty `T` and the zero sheaf are included.
6. The docstring supplies the source, blueprint identifier, and all four node proof steps. The only postponed proof is the named theorem’s stage-2 `sorry`. Single-file compilation passed.
7. Searches found no duplicate in Mathlib or `lean/Sheaf`/`WeilConjectures`. `IsLocallyConstant.isClopen_fiber` concerns functions; `Etale.isClopen_stalkZeroLocus` concerns vanishing entire stalks of an étale sheaf, not germs of a section.
