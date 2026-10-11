## Worker report

The module `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` states the entire node as one theorem, `AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine`, with a single `sorry` proof. It defines no new notion. The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- The scheme is `(X : Scheme.{u})`; no Noetherian, compact, or separation hypothesis is imposed.
- Every O_X-module of finite presentation in (0) is `∀ G : X.Modules, G.IsFinitePresentation → G.IsQuasicoherent`. This clause is outside the later quasi-coherence assumption, so it does not assume its conclusion.
- The subsequent quasi-coherent module is `∀ F : X.Modules, F.IsQuasicoherent → ...`. This assumption applies to (a), (b), and both consequences in (c).
- The in-statement definition of finite presentation is Mathlib's `SheafOfModules.IsFinitePresentation`: a local presentation with finite generators and finite relations. Its `QuasicoherentData.IsFinitePresentation` requires each presentation on a covering object to be finite. This is exactly the local finite-free right-exact sequence in Stacks 01BN, including zero ranks.
- An affine open is `U : X.Opens` with `IsAffineOpen U`. The coefficient ring R is `Γ(X, U)`, and the module of sections is `Γ(F, U)` with its existing sectionwise action.
- Restriction F|_U is `F.over U`, a sheaf of modules on the over site of U, as in the dependency's Coherent module; the over site of opens of X over U is equivalent to the opens of U. This avoids another restriction definition.
- Clause (a) is `(F.over U).IsFiniteType ↔ Module.Finite Γ(X, U) Γ(F, U)`.
- Clause (b) is `(F.over U).IsFinitePresentation ↔ Module.FinitePresentation Γ(X, U) Γ(F, U)`. The ring-module predicate means a finite generating set with finitely generated kernel of its free presentation; `Module.FinitePresentation.exists_fin` and `exists_fin'` give precisely the quotient and right-exact-sequence descriptions in the node.
- The affine open covering in (c) is `∀ (I : Type v) (U : I → X.Opens), (⨆ i, U i) = ⊤ → (∀ i, IsAffineOpen (U i)) → ...`. All index types are permitted, and this imposes neither finiteness nor nonemptiness.
- Finite generation on each member is `∀ i, Module.Finite Γ(X, U i) Γ(F, U i)`.
- The two conclusions from the cover are `F.IsFiniteType ∧ ∀ V : X.Opens, IsAffineOpen V → Module.Finite Γ(X, V) Γ(F, V)`.
- The last consequence is a separate conjunct, independent of the covering assumption: `F.IsFinitePresentation → ∀ U : X.Opens, IsAffineOpen U → Module.FinitePresentation Γ(X, U) Γ(F, U)`.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declaration `AlgebraicGeometry.Scheme`; `X.Opens` and `IsAffineOpen` are the standard scheme notions.
- `pqf-def-coherent`: imported its recorded module `Sheaf.AlgebraicGeometry.Coherent`. That module explicitly directs quasi-coherence and finite type to `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType` (Mathlib's Quasicoherent and Generators modules). Its own `RingedSpace.IsCoherent` is not needed in this theorem. Its explanatory docstring identifies Mathlib's local-presentation quasi-coherence with the affine-local tilde characterization on schemes, so the existing dependency is usable; no duplicate definition is introduced.
- `def-weil-sheaf-of-modules-category`: the mathlib_match is `SheafOfModules` in `Mathlib.Algebra.Category.ModuleCat.Sheaf`. `Scheme.Modules` is exactly `SheafOfModules.{u} X.ringCatSheaf`, not another sheaf category.
- `def-weil-finitely-generated-module`: `Module.Finite`, `Mathlib.RingTheory.Finiteness.Defs`, meaning finitely generated top submodule.
- Finite presentation of ring modules: `Module.FinitePresentation`, `Mathlib.Algebra.Module.FinitePresentation`; read its full definition and the quotient/exact-sequence signatures. Finite presentation of sheaves: `SheafOfModules.IsFinitePresentation`, `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. These are existing notions, so no new definition node is required.

Edge cases checked before writing: the zero sheaf and zero ranks are allowed by the finite generating/presentation definitions. The empty affine open has zero ring and zero sections, hence both finiteness conditions. The empty scheme admits the empty cover and all local conditions are vacuous, consistently with the conclusion. For a nonempty scheme an empty family cannot satisfy the covering equation. Arbitrarily infinite affine covers are allowed, and the index universe v is independent because no categorical limit or colimit over I is being asserted. There is no assumption that X itself is affine. Finite type is not confused with finite presentation, including over non-Noetherian rings. No statement dispute or correction was needed.

Searches performed (2026-10-11):

- msearch leanfinder, query `quasi-coherent sheaf finite type finite presentation iff sections on affine open finitely generated finitely presented`: eight hits, all definitions and local finite-presentation implications in `SheafOfModules`; no full affine criterion.
- msearch loogle, query `SheafOfModules.IsFiniteType, Module.Finite`: zero hits.
- msearch leansearch, query `quasi coherent module affine sections finite presentation equivalence`: service unavailable (Internal Server Error); no verdict assigned to this unavailable search. Other search kinds and direct source inspection completed the search.
- msearch grep, query `finiteType.*iff|finitePresentation.*iff|finite_sections|IsFinitePresentation`, subdirectory `AlgebraicGeometry/Modules`: zero hits in Mathlib.
- Direct rg in Mathlib, source `WeilConjectures`, and project `lean/Sheaf` for `finiteType.*iff|finitePresentation.*iff|isFiniteType.*iff|isFinitePresentation.*iff|finite_sections|lem-weil-pbc-quasi-coherent-finite-type-affine`: upstream has `finite_sections_top_of_isIso_fromTildeΓ` and `finite_sections_of_isFinitePresentation` in QuasicoherentKernel, whose full signatures and docstrings were read; they prove only parts, not the iff statements or the full conjunction. Project files cite this node in proof docstrings but do not already state it. Mathlib has finite-presentation predicates and the implication to quasi-coherence, not all clauses of this node.
- Full chosen declaration name searched in Mathlib, WeilConjectures, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

The local literature TeX files were absent. Read the source directly at https://stacks.math.columbia.edu/tag/01BO, https://stacks.math.columbia.edu/tag/01PB, and https://stacks.math.columbia.edu/tag/01PC; their statements agree with (0) and the affine criteria. The module docstring includes all nine proof steps with their dependency node names.

Validation: server single-file compile via scompile.py succeeded in 4.3 seconds, exit code 0, with no errors or warnings. Delivery dry run is the final check; the independent second reading is left to the second reader.

## Second reading by E1

I read the node statement and the source places (Stacks Modules 01BN/01BO and
Properties 01PB/01PC) against the Lean declaration item by item. The introduced
objects and their rendering are: `X : Scheme.{u}`; the universal clause
`∀ G : X.Modules, G.IsFinitePresentation → G.IsQuasicoherent`; the quasi-coherent
`F : X.Modules`; affine `U : X.Opens` with `IsAffineOpen U`; the section modules
`Γ(X, U)` and `Γ(F, U)`; restriction `(F.over U)`; the two equivalences between
sheaf finite type/presentation and `Module.Finite`/`Module.FinitePresentation`;
an arbitrary index type `I : Type v` and affine cover `U : I → X.Opens` with
`(⨆ i, U i) = ⊤`; its pointwise finite-section hypothesis; the conclusions
`F.IsFiniteType` and finite sections on every affine open; and the final global
finite-presentation-to-finite-sections implication. Each appears in the Lean
signature with the same quantifier order and hypotheses. The parenthetical
description of finite presentation in the node is represented by Mathlib's
`Module.FinitePresentation`, exactly the cited notion.

Edge cases were checked: arbitrary (including empty) cover index types, zero
modules and zero ranks, empty schemes and empty affine opens, `n = 0`, and no
characteristic, Noetherian, separation, or universe restriction beyond the
scheme universe and the independent cover index universe. No categorical limit
or colimit is quantified over the cover index, so `Type v` is appropriate.

I repeated the existing-definition searches with msearch (LeanFinder, Loogle,
and LeanSearch), `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`, including
the exact declaration name. They found only component predicates and partial
upstream lemmas, not this theorem; the declaration is therefore new and does
not collide with an existing name. The dependency declarations recorded by the
worker are the matching scheme, module-category, quasi-coherence, and module
finiteness notions; no dependency module or new definition node is required.

No mismatch was found, so no source, node statement, hypotheses, quantifiers,
or Lean code was changed. The module's docstring gives all nine proof steps and
the required source and blueprint tag, and its only proof is the permitted
`sorry`. The module was independently compiled successfully with `scompile.py`.
