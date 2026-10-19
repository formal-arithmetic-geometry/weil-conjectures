## Worker report

The module `Sheaf/DeligneLaumon/BertiniSections.lean` states
`AlgebraicGeometry.exists_eventual_immersion_vanishingSections` for Stacks Tag 0FD5.
It binds a field `k`, a `k`-scheme `Y` with proper structure morphism, an invertible
module `L` with `IsAmple`, and a closed immersion `i : Z ⟶ Y`. It supplies an open `U`
whose points are exactly the complement of the image of `i`, then an eventual bound `n₀`.
For every `n ≥ n₀`, it supplies the kernel submodule `V` of the restriction map on global
sections, a finite index type `I`, a linearly independent spanning family `s` (the basis
coordinates of `V`), and restricted sections `t`. The restricted family is epi on the
module over `U`, and the morphism
`ProjectiveSpace.homOfGeneratingSections` into `ℙ(I; Spec k)` is an immersion.
The scalar action on global sections is the explicit restriction of scalars along the
structure map `k → Γ(Y, ⊤)`, introduced with the `letI` binder required by the existing
section-module API.

The hypotheses and clauses render as follows.

* `k` is `(k : Type u) [Field k]`.
* “`Y` is a `k`-scheme” is `[Y.Over (Spec (.of k))]`.
* Properness is `[IsProper (Y ↘ Spec (.of k))]`.
* `L` is `(L : Y.Modules) [L.IsInvertible]` and ampleness is
  `(hL : IsAmple (Y ↘ Spec (.of k)) L)`.
* The closed subscheme is `{Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]`.
* The complement is `(∀ y : Y, y ∈ U ↔ y ∉ Set.range i.base)`.
* Eventuality is `∀ (n : ℕ), n₀ ≤ n →`.
* The kernel clause is
  `∀ v, v ∈ V ↔ (AlgebraicGeometry.pullbackΓ i (L.tensorPow n)) v = 0`.
* Basis coordinates are the conjunction
  `Submodule.span k (Set.range (fun j ↦ (s j).val (Opposite.op ⊤))) = V` and
  `LinearIndependent (M := Γ(L.tensorPow n, ⊤)) k ...`, with finite `I`.
* Restriction is the equality
  `(t j).val (Opposite.op ⊤) = pullbackΓ U.ι ... ((s j).val (Opposite.op ⊤))`.
* Generation is the explicit existential `∃ ht : Epi (...)`; the associated morphism
  is `ProjectiveSpace.homOfGeneratingSections ... t ht`, and the conclusion is
  `IsImmersion` of that morphism.

Dependency declarations used:

* `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`, from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
* `def-sc-ample`: `AlgebraicGeometry.IsAmple`, from
  `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`.
* `def-weil-pbc-generating-sections`: Mathlib's `SheafOfModules.GeneratingSections` /
  `SheafOfModules.freeHomEquiv` interface, used by the epi clause.
* `def-weil-pbc-morphism-to-projective-space-by-sections`:
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`, from
  `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`.
* `def-weil-pbc-scheme-conventions` and `def-weil-scheme-morphism-properties` are
  convention nodes with no standalone declaration; their meanings are rendered directly
  by `Scheme`, `Scheme.Over`, `IsProper`, `IsClosedImmersion`, `IsImmersion`, and the
  structure morphism used above.
* `AlgebraicGeometry.pullbackΓ` is imported from
  `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit` for the canonical restriction
  map on global sections.

Edge cases checked: `Z = Y` (the complement can be empty and `I` can be empty), `Z` empty,
`Y` empty, nonreduced closed subschemes, zero tensor powers (`n = 0` is allowed whenever
above the eventual bound), and arbitrary or imperfect fields. No characteristic or
nonemptiness hypothesis was added.

Searches for an existing declaration: `msearch.py ... leanfinder "sections vanishing on a
closed subscheme ample invertible sheaf complement immersion"` returned only generic
vanishing/basic-open results and no theorem. `msearch.py ... loogle "AlgebraicGeometry.IsAmple,
ProjectiveSpace.homOfGeneratingSections, IsImmersion"` returned zero hits (the parser did
not recognize the source namespace). `msearch.py ... grep "ample.*sections|vanishing.*closed|
homOfGeneratingSections" Mathlib/AlgebraicGeometry` returned no matching theorem. `rg` over
`WeilConjectures/` and the project `lean/Sheaf` found no declaration of this eventual
closed-subscheme complement statement. The recorded declarations were opened and checked
for their full signatures and docstrings.

No `STATEMENT-DISPUTED` flag or node correction is needed.

## Second reading by NA

I reread the copied node and the module independently. The field, properness, invertibility,
and ampleness hypotheses are all present. The complement is stated pointwise as the complement
of the closed immersion image. The eventual quantifier includes every `n ≥ n₀`; its kernel is
exactly the vanishing restriction kernel. The finite family has both span-equals-kernel and
linear independence, so it represents a basis, and the restricted family is tied to the same
sections through `pullbackΓ`. The epi clause gives generation on the complement, and the final
clause applies the recorded projective-space construction to those restricted sections and
asserts immersion. Empty complements and empty coordinate types remain expressible. I found
no mismatch with the node statement.
