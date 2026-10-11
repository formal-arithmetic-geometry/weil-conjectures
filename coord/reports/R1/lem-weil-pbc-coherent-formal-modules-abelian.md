## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian` states
`AlgebraicGeometry.coherentFormalModule_abelian`, with its proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- The Noetherian scheme is `(X : Scheme.{u}) [IsNoetherian X]`.
- The quasi-coherent ideal sheaf is `(I : X.IdealSheafData)`. This is the existing
  bundled quasi-coherent ideal-sheaf data, used by the dependency definition itself.
- The category Coh(X,I) is exactly `CoherentFormalModule X I`, the dependency's
  full subcategory of inverse systems satisfying coherence, annihilation and quotient
  compatibility. Its index `op n` represents the source's positive level n+1.
- Abelianness is `Nonempty (Abelian (CoherentFormalModule X I))`. Abelian is a
  structure, not a proposition, so Nonempty states its existence without adding a
  structure as a hypothesis. The category and its termwise zero maps already exist.
- Every morphism is quantified by
  `∀ (F G : CoherentFormalModule X I) (α : F ⟶ G)`.
- Its cokernel is specified by `∃ c : CokernelCofork α, Nonempty (IsColimit c)`.
  The point of c is itself a coherent formal system, and its projection is a
  compatible family of maps killing α, with the cokernel universal property.
- The termwise description is the remaining `∀ n : ℕ, Nonempty (IsColimit ...)`:
  map that same cofork under `(IsCoherentFormalModule I).ι` and evaluation at `op n`.
  Its evaluated diagram is the parallel pair (α_n,0), so the point at each level
  and its projection are a cokernel of α_n in X.Modules. Thus it specifies the
  entire inverse system, not merely isolated object isomorphisms. Naturality of the
  projection forces the transition maps to be the induced cokernel transitions;
  each cokernel projection is epi. Conversely the termwise cokernel system of the
  node gives precisely this cofork and these universal properties. This is the
  usual unique-up-to-isomorphism reading of categorical cokernels, with no extra
  conclusion or hypothesis.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.CoherentFormalModule`, declarations
  `AlgebraicGeometry.CoherentFormalModule` and `AlgebraicGeometry.IsCoherentFormalModule`.
  Read the complete module, including the docstrings and the defining object conditions.
- `def-sp-abelian` is a Mathlib leaf: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`. Read its full structure signature and
  docstring: preadditive, finite products, kernels, cokernels, normal monos and epis.
- Mathlib supplies `ObjectProperty.ι`, `evaluation`, `CokernelCofork`, `IsColimit`,
  and `Functor.mapCocone`. Preadditive.FunctorCategory supplies the termwise
  preadditive structure on inverse systems; full subcategories inherit it.

Source: opened https://stacks.math.columbia.edu/tag/087X, since the recorded
`literature/stacks-project/coherent.tex` is not present on this machine. Its part (1)
and the first paragraph of its proof state the node's two clauses. The theorem
 docstring gives all ten proof steps from the node, including the Artin-Rees
kernel construction, uniqueness, affine restriction, and the coimage-image criterion.

Edge cases checked mathematically before writing:

- The empty Noetherian scheme is allowed; its module and formal-system categories
  are zero categories, satisfying both clauses. No nonemptiness of X is assumed.
- For I=0, quotient compatibility makes transitions isomorphisms, and the assertion
  reduces to coherent modules on a Noetherian scheme with compatible isomorphisms.
- For I=O_X, all levels are zero, again giving a zero category.
- Zero maps have target systems as their termwise cokernels; identity maps have
  zero systems. The cofork universal-property formulation covers both.
- `n=0` means source level 1, not an unintended level 0. The unbounded positive
  system and all schemes of universe u are retained. There is no characteristic,
  properness, completeness, finite-type, or base-ring restriction.
- Kernels are intentionally not claimed to be termwise kernels: the Artin-Rees
  construction is necessary, as indicated by the source and the node.

Searches for an existing statement (no exact declaration found):

- msearch LeanFinder: "category of coherent formal modules on a Noetherian scheme
  is abelian cokernels computed termwise". Eight hits concerned condensed modules,
  all scheme modules, general sheaves of modules, and finitely generated modules;
  none concern the category of coherent adic systems.
- msearch Loogle: "CategoryTheory.Abelian, CategoryTheory.Limits.IsColimit".
  Twelve general abelian-category cofork and short-complex results; no match.
- msearch grep: "CoherentFormal|coherent formal|formal.*abelian" in
  AlgebraicGeometry. Zero hits.
- msearch LeanSearch: "coherent formal modules abelian category termwise cokernels".
  Service unavailable (Internal Server Error); no verdict inferred from that failure.
- rg in project lean/Sheaf and upstream WeilConjectures:
  "CoherentFormal|formal.*[Cc]okernel|coherent.*[Aa]belian". Only the dependency
  category and unrelated quasi-coherent cokernel/image declarations were found.
- grep for the exact blueprint id in upstream WeilConjectures: no hits.
- tools/lean_names_upstream.py show and rg of dag/lean_names_upstream.json,
  Mathlib, upstream WeilConjectures and project lean/Sheaf for
  "coherentFormalModule_abelian|CoherentFormalModulesAbelian": no name collision.

Server validation: scompile.py compiled the 78-line module cleanly in 2.5 seconds,
exit code 0, with no errors or warnings. Every variable and universe is explicit.
## Second reading by R1

I independently opened the node, dependency declaration, Lean module, and Stacks Lemma 087X (tag 087X, Lemma 30.23.2, part (1)). The node introduces a Noetherian scheme `X`, a quasi-coherent ideal sheaf `I`, the category `Coh(X,I)`, and each morphism `α`. Lean renders these as `(X : Scheme.{u}) [IsNoetherian X]`, `(I : X.IdealSheafData)`, `CoherentFormalModule X I`, and `∀ (F G : CoherentFormalModule X I) (α : F ⟶ G)`. The bundled ideal sheaf and full subcategory are exactly the dependency declarations, with no extra hypotheses.

The abelian conclusion is `Nonempty (Abelian (CoherentFormalModule X I))`, correctly expressing existence of Mathlib's Abelian structure. The cokernel clause is `∃ c : CokernelCofork α, Nonempty (IsColimit c)` and, for every `n : ℕ`, `Nonempty (IsColimit (((IsCoherentFormalModule I).ι ⋙ (evaluation ℕᵒᵖ X.Modules).obj (op n)).mapCocone c))`. Thus one compatible cofork is a cokernel and its evaluation at every positive level is the component cokernel, which is the categorical meaning of the node's inverse system `(Coker α_n)_n`; `op n` is level `n+1`, so all source levels `n≥1` are covered. No conclusion is weakened or strengthened beyond this canonical universal-property formulation.

I checked the dependency module and Mathlib's `CategoryTheory.Abelian` declaration. The docstrings give the Stacks source, blueprint id, and all ten proof steps, and the proof is only `sorry`. Searches (LeanFinder, Loogle, grep, and LeanSearch) found no exact existing declaration; LeanSearch was unavailable. Edge cases checked: empty scheme, zero category, `I=0`, `I=O_X`, zero and identity maps, `n=0`, arbitrary allowed universe, and no characteristic/properness assumptions. Kernels remain intentionally non-termwise as in the Artin--Rees source proof. No mismatch was found and no file change was needed. The module compiles cleanly with `scompile.py`.
