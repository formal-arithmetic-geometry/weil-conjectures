## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric` states
`AlgebraicGeometry.constant_subsheaf_generic`, with only `sorry` as proof. No new
notion, dependency module, statement correction, or disputed statement is needed.

Hypothesis and clause correspondence:
- Nonempty irreducible scheme W: `(W : Scheme.{u}) [Nonempty W] [IrreducibleSpace W]`.
- Its generic point η: `(η : W) (_hη : IsGenericPoint η Set.univ)`.
- Finite commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Finite Λ-module M: `(M : ModuleCat.{u + 1} Λ) [Finite M]`; finite here means a
  finite underlying set, as required by the node's finite-intersection proof.
- Constant sheaf on the small etale site: `(constantSheaf W.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)).obj M`.
- Subsheaf H of Λ-modules: H is a `Sheaf` with values in `ModuleCat Λ`, with
  inclusion `hH` into that constant sheaf and `[Mono hH]`. A sheaf together with
  a monomorphism is a representative of a subsheaf; no splitting is assumed.
- Nonempty open W°: `∃ (U : W.Opens) (_hU : (U : Set W).Nonempty)`.
- Submodule M': `∃ (M' : Submodule Λ M)`.
- Restriction: `(Etale.upperStar (ModuleCat Λ) U.ι).obj H` is inverse image along
  the open inclusion, the restriction to the small etale site of U.
- Equality with constant M' AS SUBSHEAVES: an isomorphism `e` from the restriction
  of H to constant M', satisfying the equation `e.hom ≫ constantSheaf.map
  (ModuleCat.ofHom (Submodule.subtype M')) = upperStar.map hH ≫
  upperStarConstantSheafIso.hom.app M`. Thus this is equality of subobjects of
  the ambient constant M sheaf, rather than an arbitrary abstract isomorphism.

Dependency declarations read and used: `AlgebraicGeometry.Scheme.Etale` and
`AlgebraicGeometry.Scheme.smallEtaleTopology` in
`Mathlib.AlgebraicGeometry.Sites.Etale` (the recorded module for
`def-weil-pbc-etale-site`), imported transitively through
`WeilConjectures.ConstructibleSheaf.Defs`. The source definitions include the
jointly-surjective covering characterization and finite limits. Also used:
`CategoryTheory.constantSheaf` in `Mathlib.CategoryTheory.Sites.ConstantSheaf`;
`AlgebraicGeometry.Etale.upperStar` in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso` in
`WeilConjectures.ConstructibleSheaf.Defs`; `ModuleCat`, `Submodule`, `Mono`,
and the open subscheme `U.toScheme` with inclusion `U.ι`, all existing notions.
No dependency's record is unusable.

Edge cases checked before writing: the zero module, zero subsheaf, whole subsheaf,
and zero ring are allowed; a one-point irreducible scheme is allowed; the empty
scheme is excluded precisely by the stated nonemptiness hypothesis; no reduced,
normal, separated, Noetherian, characteristic, or quasi-compact hypothesis is
added. Arbitrary scheme universes u are allowed; coefficients in u+1 follow the
source's sheafification convention, with finite rings/modules from lower
universes available by lifting. The conclusion retains the inclusions, including
for nontrivial automorphisms of the abstract module sheaf.

Searches (all service queries run through msearch.py and recorded in searches.jsonl):
- LeanSearch: "subsheaf of a constant finite module sheaf on an irreducible scheme
  is constant on a nonempty open": service unavailable (Internal Server Error).
- LeanFinder: the same query: eight hits, including `ModuleCat.Tilde.exists_const`
  and `AlgebraicGeometry.StructureSheaf.exists_const`; these describe sections
  of Zariski structure/module sheaves, not this etale subsheaf statement.
- Loogle: `CategoryTheory.constantSheaf, CategoryTheory.Mono`: no matching theorem.
- Mathlib grep: `subsheaf.*constant|constant.*subsheaf|constant.*generic`: no hits.
- Source/project rg: `constant.*[Ss]ubsheaf|subsheaf.*constant|constant.*generic|generic.*constant`
  found normal-generic pushforward results and the simple-sheaf definition, none
  stating this theorem. The item's blueprint id has no source declaration.
- Name search `constant_subsheaf_generic` in upstream names, source, and project:
  no existing declaration.

Source checked: https://stacks.math.columbia.edu/tag/03RY, proof of Proposition
59.74.1(3), and https://stacks.math.columbia.edu/tag/03RZ. The local literature
checkout is absent on this machine, so the primary Stacks pages were opened.
The finite-ring finite-underlying-module statement is the node's specialization
of the source's generic-constancy argument. The docstring carries both DAG proof
steps and identifies the openness and geometric-stalk-conservativity inputs.

Server compile: scompile.py returned exit code 0, with no errors or warnings.

## Second reading by C1

I reread the source statement (Stacks Tag 03RY, Proposition 59.74.1(3),
with Tag 03RZ, Lemma 59.71.6) and matched each item to the Lean signature.

- The nonempty irreducible scheme with generic point is rendered by
  `(W : Scheme.{u}) [Nonempty W] [IrreducibleSpace W]`, `(η : W)`, and
  `_hη : IsGenericPoint η Set.univ`.  This permits arbitrary scheme universes
  and excludes the empty scheme exactly as the source does.
- The finite commutative coefficient ring is
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`; the finite module is
  `(M : ModuleCat (u + 1) Λ) [Finite M]`.  The universe lift is the sheaf
  convention and adds no algebraic hypothesis.
- The ambient constant sheaf is
  `constantSheaf W.smallEtaleTopology (ModuleCat (u + 1) Λ)).obj M`.
- A subsheaf is represented by a sheaf `H` and a monomorphism
  `hH : H ⟶ constantSheaf ... .obj M`, with `[Mono hH]`; no splitting or
  extra finiteness condition is assumed.
- The conclusion introduces a nonempty open `U : W.Opens` with
  `_hU : (U : Set W).Nonempty` and a submodule `M' : Submodule Λ M`.
- It supplies an isomorphism `e` from the upper-star restriction of `H` to
  the constant sheaf on `U.toScheme` with coefficient `M'`.
- The final composition equation identifies this isomorphism as an equality
  of subsheaves inside the restricted constant `M`-sheaf: the left side is
  `e.hom` followed by the map induced by `Submodule.subtype M'`, while the
  right side is the restricted inclusion `hH` followed by
  `Scheme.upperStarConstantSheafIso`.  Thus the statement is stronger than an
  abstract isomorphism and matches the source's “as subsheaves” clause.

No mismatch was found, and no statement correction or dependency module was
needed.  I checked the zero ring, zero and whole submodules, zero module,
one-point irreducible schemes, `n = 0` vacuity (there is no numerical `n`),
and arbitrary coefficient and scheme universes.  The generic-point and
nonempty-open hypotheses correctly rule out the empty-scheme edge case.

Searches were repeated with LeanFinder/Loogle and `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf` for constant-subsheaf and generic-constancy
variants; only unrelated `ModuleCat.Tilde.exists_const` and structure-sheaf
results were found.  The exact declaration name `constant_subsheaf_generic`
was absent.  The module compiles cleanly with `scompile.py`; its only proof
placeholder is the permitted `sorry` for this statement node.
